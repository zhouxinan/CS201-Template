#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/IRBuilder.h"
#include <string>
#include <fstream>
#include <unordered_map>
#include <set>
#include <queue>
#include <stdlib.h>

using namespace llvm;
using namespace std;

namespace {
    struct ReachingDefinition : public FunctionPass {
        static char ID;
        ReachingDefinition() : FunctionPass(ID) {}

        struct Definition {
            Instruction *instruction; // The instruction that calculates that definition.
            Value *variableDefined;
            Value *variableValue;
        };

        bool isTwoDenseSetOfDefinitionsEqual(DenseSet<Definition *> *setA, DenseSet<Definition *> *setB) {
            if (setA->size() != setB->size()) {
                return false;
            }
            for (auto v = setA->begin(); v != setA->end(); v++) {
                Definition *v1 = &(*(*v));
                if (findDefinitionInDenseSetOfDefinitions(setA, v1) == setA->end()) {
                    return false;
                }
            }
            return true;
        }

        void computeDefinitionDenseSetAminusDenseSetB(DenseSet<Definition *> *setA, DenseSet<Definition *> *setB, DenseSet<Definition *> *result) {
            for (auto v = setA->begin(); v != setA->end(); v++) {
                Definition *v1 = &(*(*v));
                if (findDefinitionInDenseSetOfDefinitions(setB, v1) == setB->end()) {
                    result->insert(v1);
                }
            }
        }

        void computeDenseSetAUnionDenseSetB(DenseSet<Definition *> *setA, DenseSet<Definition *> *setB, DenseSet<Definition *> *result) {
            for (auto v = setA->begin(); v != setA->end(); v++) {
                Definition *v1 = &(*(*v));
                result->insert(v1);
            }
            for (auto v = setB->begin(); v != setB->end(); v++) {
                Definition *v1 = &(*(*v));
                if (findDefinitionInDenseSetOfDefinitions(result, v1) == result->end()) {
                    result->insert(v1);
                }
            }
        }

        DenseSet<Definition *>::iterator findDefinitionInDenseSetOfDefinitions(DenseSet<Definition *> *denseSet, Definition *definition) {
            for (auto it = denseSet->begin(); it != denseSet->end(); it++) {
                Definition *def = &(*(*it));
                if (def->instruction == definition->instruction) {
                    return it;
                }
            }
            return denseSet->end();
        }

        void addDefinitionToKillB(DenseSet<Definition *> *kill_b, DenseSet<Definition *> *allDefinitions, Definition *definition) {
            for (auto v = allDefinitions->begin(); v != allDefinitions->end(); v++) {
                Definition *def = &(*(*v));
                if (def->variableDefined == definition->variableDefined) {
                    if (findDefinitionInDenseSetOfDefinitions(kill_b, def) == kill_b->end()) {
                        // errs() << "^^^^^^^^add def to KILL[B]: ";
                        // printDefinition(def);
                        // errs() << "\n";
                        kill_b->insert(def);
                    }
                }
            }
        }

        void printDefinition(Definition *definition) {
            errs() << "(";
            if (!dyn_cast<ConstantInt>(definition->variableDefined)) {
                errs() << definition->variableDefined->getName();
            } else {
                errs() << dyn_cast<ConstantInt>(definition->variableDefined)->getSExtValue();
            }
            errs() << "=";
            if (definition->variableValue == NULL) {
                errs() << "0";
            } else {
                if (!dyn_cast<ConstantInt>(definition->variableValue)) {
                    errs() << definition->variableValue->getName();
                } else {
                    errs() << dyn_cast<ConstantInt>(definition->variableValue)->getSExtValue();
                }
            }
            errs() << ")";
        }

        void removeDefinitionFromGenB(DenseSet<Definition *> *gen_b, Definition *definition) {
            for (auto it = gen_b->begin(); it != gen_b->end(); it++) {
                Definition *def = &(*(*it));
                if (def->variableDefined == definition->variableDefined) {
                    // errs() << "********erase definition from GEN[B]: ";
                    // printDefinition(def);
                    // errs() << "\n";
                    gen_b->erase(def);
                }
            }
            return;
        }

        bool reaching_definition_data_flow_analysis(Function &F, map<BasicBlock*, DenseSet<Definition *>> &bb_to_reaching_definition_gen_b,
            map<BasicBlock*, DenseSet<Definition *>> &bb_to_reaching_definition_kill_b,
            map<BasicBlock*, DenseSet<Definition *>> &bb_to_reaching_definition_in_b,
            map<BasicBlock*, DenseSet<Definition *>> &bb_to_reaching_definition_out_b, DenseSet<Definition *> &allDefinitions) {
            auto basicBlockList = &(F.getBasicBlockList());
            // Calculate GEN[B]
            // errs() << "=================reaching_definition_data_flow_analysis=================\n";
            for (auto it = basicBlockList->begin(); it != basicBlockList->end(); it++) {
                BasicBlock *bb = &(*it);
                DenseSet<Definition *> reaching_definition_gen_b;
                // errs() << "=================Basic Block Name: " + bb->getName() + "=================\n";
                for (auto it = bb->begin(), e = bb->end(); it != e; ++it) {
                    Instruction *instruction = &(*it);
                    if (instruction->getOpcode() == Instruction::Store) {
                        // errs() << "This is a Store!\n";
                        // be careful of the operand order.
                        Value *lhsVariable = instruction->getOperand(1);
                        Value *rhsVariable = instruction->getOperand(0);
                        Definition *newDefinition = (Definition *)malloc(sizeof(Definition));
                        newDefinition->variableDefined = lhsVariable;
                        newDefinition->variableValue = rhsVariable;
                        newDefinition->instruction = instruction;
                        removeDefinitionFromGenB(&reaching_definition_gen_b, newDefinition);
                        // errs() << "reaching_definition_gen_b.insert(";
                        if (!dyn_cast<ConstantInt>(newDefinition->variableDefined)) {
                            // errs() << newDefinition->variableDefined->getName();
                        } else {
                            // errs() << dyn_cast<ConstantInt>(newDefinition->variableDefined)->getSExtValue();
                        }
                        // errs() << "=";
                        if (!dyn_cast<ConstantInt>(newDefinition->variableValue)) {
                            // errs() << newDefinition->variableValue->getName();
                        } else {
                            // errs() << dyn_cast<ConstantInt>(newDefinition->variableValue)->getSExtValue();
                        }
                        // errs() << ")\n";
                        reaching_definition_gen_b.insert(newDefinition);
                        allDefinitions.insert(newDefinition);
                    } else if (instruction->getOpcode() == Instruction::Alloca) {
                        // errs() << "This is a Alloca!\n";
                        // instruction->dump();
                        Definition *newDefinition = (Definition *)malloc(sizeof(Definition));
                        newDefinition->variableDefined = instruction;
                        newDefinition->variableValue = NULL;
                        newDefinition->instruction = instruction;
                        // errs() << "reaching_definition_gen_b.insert(";
                        // errs() << instruction->getName() << "=0)\n";
                        reaching_definition_gen_b.insert(newDefinition);
                        allDefinitions.insert(newDefinition);
                    }
                }
                bb_to_reaching_definition_gen_b.insert(std::make_pair(bb, reaching_definition_gen_b));
                // Initialization
                bb_to_reaching_definition_out_b.insert(std::make_pair(bb, reaching_definition_gen_b));
                bb_to_reaching_definition_in_b.insert(std::make_pair(bb, NULL));
            }

            // Calculate KILL[B]
            // errs() << "Calculate KILL[B]!\n";
            for (auto it = basicBlockList->begin(); it != basicBlockList->end(); it++) {
                BasicBlock *bb = &(*it);
                DenseSet<Definition *> kill_b;
                // errs() << "=================Basic Block Name: " + bb->getName() + "=================\n";
                for (auto it = bb->begin(), e = bb->end(); it != e; ++it) {
                    Instruction *instruction = &(*it);
                    if (instruction->getOpcode() == Instruction::Store) {
                        // be careful of the operand order.
                        Value *lhsVariable = instruction->getOperand(1);
                        Value *rhsVariable = instruction->getOperand(0);
                        Definition *newDefinition = (Definition *)malloc(sizeof(Definition));
                        newDefinition->variableDefined = lhsVariable;
                        newDefinition->variableValue = rhsVariable;
                        newDefinition->instruction = instruction;
                        addDefinitionToKillB(&kill_b, &allDefinitions, newDefinition);
                    }
                }
                bb_to_reaching_definition_kill_b.insert(std::make_pair(bb, kill_b));
            }

            // Reaching Definition Iterative algorithm
            basicBlockList = &(F.getBasicBlockList());
            bool change = true;
            while (change) {
                change = false;
                for (auto it = basicBlockList->begin(); it != basicBlockList->end(); it++) {
                    if (it != basicBlockList->begin()) {
                        BasicBlock *bb = &(*it);
                        DenseSet<Definition *> genb_of_this_bb = bb_to_reaching_definition_gen_b.at(bb);
                        DenseSet<Definition *> killb_of_this_bb = bb_to_reaching_definition_kill_b.at(bb);
                        DenseSet<Definition *> oldout = bb_to_reaching_definition_out_b.at(bb);
                        DenseSet<Definition *> in_of_this_bb;
                        DenseSet<Definition *> union_of_out_of_preds;
                        for (auto it2 = pred_begin(bb), end = pred_end(bb); it2 != end; ++it2) {
                            BasicBlock *pred = *it2;
                            DenseSet<Definition *> outb_of_this_pred = bb_to_reaching_definition_out_b.at(pred);
                            if (it2 == pred_begin(bb)) {
                                in_of_this_bb = outb_of_this_pred;
                            } else {
                                union_of_out_of_preds.clear();
                                computeDenseSetAUnionDenseSetB(&in_of_this_bb, &outb_of_this_pred, &union_of_out_of_preds);
                                in_of_this_bb = union_of_out_of_preds;
                            }
                        }
                        bb_to_reaching_definition_in_b.erase(bb);
                        bb_to_reaching_definition_in_b.insert(std::make_pair(bb, in_of_this_bb));

                        DenseSet<Definition *> in_minus_kill;
                        computeDefinitionDenseSetAminusDenseSetB(&in_of_this_bb, &killb_of_this_bb, &in_minus_kill);
                        
                        DenseSet<Definition *> new_out_b;
                        computeDenseSetAUnionDenseSetB(&in_minus_kill, &genb_of_this_bb, &new_out_b);
                        
                        bb_to_reaching_definition_out_b.erase(bb);
                        bb_to_reaching_definition_out_b.insert(std::make_pair(bb, new_out_b));

                        if (!isTwoDenseSetOfDefinitionsEqual(&new_out_b, &oldout)) {
                            change = true;
                        }
                    }
                }
            }
            return true;
        }

        bool runOnFunction(Function &F) override {
            map<BasicBlock*, DenseSet<Definition *>> bb_to_reaching_definition_gen_b;
            map<BasicBlock*, DenseSet<Definition *>> bb_to_reaching_definition_kill_b;
            map<BasicBlock*, DenseSet<Definition *>> bb_to_reaching_definition_in_b;
            map<BasicBlock*, DenseSet<Definition *>> bb_to_reaching_definition_out_b;
            DenseSet<Definition *> allDefinitions;
            bb_to_reaching_definition_gen_b.clear();
            bb_to_reaching_definition_kill_b.clear();
            bb_to_reaching_definition_in_b.clear();
            bb_to_reaching_definition_out_b.clear();
            allDefinitions.clear();
            reaching_definition_data_flow_analysis(F, bb_to_reaching_definition_gen_b, bb_to_reaching_definition_kill_b, bb_to_reaching_definition_in_b, bb_to_reaching_definition_out_b, allDefinitions);

            // Print OUT[B] for all basic blocks.
            for (map<BasicBlock*, DenseSet<Definition *>>::iterator it = bb_to_reaching_definition_out_b.begin(); it != bb_to_reaching_definition_out_b.end(); it++) {
                BasicBlock* basicBlock = it->first;
                DenseSet<Definition *> outSet = it->second;
                errs() << basicBlock->getName() << ": ";
                set<std::string> setOfReachingDefinitionNames;
                for (DenseSet<Definition *>::iterator it_2 = outSet.begin(); it_2 != outSet.end(); it_2++) {
                    Definition *definition = &(*(*it_2));
                    std::string definitionString = "(";
                    if (!dyn_cast<ConstantInt>(definition->variableDefined)) {
                        definitionString += definition->variableDefined->getName();
                    } else {
                        definitionString += to_string(dyn_cast<ConstantInt>(definition->variableDefined)->getSExtValue());
                    }
                    definitionString += "=";
                    if (definition->variableValue == NULL) {
                        definitionString += "0";
                    } else {
                        if (!dyn_cast<ConstantInt>(definition->variableValue)) {
                            definitionString += definition->variableValue->getName();
                        } else {
                            definitionString += to_string(dyn_cast<ConstantInt>(definition->variableValue)->getSExtValue());
                        }
                    }
                    definitionString += ")";
                    setOfReachingDefinitionNames.insert(definitionString);
                }
                for (auto it_3 = setOfReachingDefinitionNames.begin(); it_3 != setOfReachingDefinitionNames.end() ; ++it_3) {
                    errs() << *it_3 << " ";
                }
                errs() << "\n";
            }
            
            return false;
        }
    }; // end of struct ReachingDefinition
} // end of anonymous namespace

char ReachingDefinition::ID = 0;
static RegisterPass<ReachingDefinition> X("ReachingDefinition", "ReachingDefinition Pass",
                                      false /* Only looks at CFG */,
                                      true /* Tranform Pass */);