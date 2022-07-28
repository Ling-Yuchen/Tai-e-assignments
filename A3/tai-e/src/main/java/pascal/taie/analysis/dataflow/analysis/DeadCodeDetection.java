/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.dataflow.analysis;

import pascal.taie.analysis.MethodAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.cfg.Edge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.ArithmeticExp;
import pascal.taie.ir.exp.ArrayAccess;
import pascal.taie.ir.exp.CastExp;
import pascal.taie.ir.exp.FieldAccess;
import pascal.taie.ir.exp.NewExp;
import pascal.taie.ir.exp.RValue;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.AssignStmt;
import pascal.taie.ir.stmt.If;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.SwitchStmt;
import pascal.taie.util.collection.Pair;

import java.util.*;

public class DeadCodeDetection extends MethodAnalysis {

    public static final String ID = "deadcode";

    public DeadCodeDetection(AnalysisConfig config) {
        super(config);
    }

    @Override
    public Set<Stmt> analyze(IR ir) {
        // obtain CFG
        CFG<Stmt> cfg = ir.getResult(CFGBuilder.ID);
        // obtain result of constant propagation
        DataflowResult<Stmt, CPFact> constants =
                ir.getResult(ConstantPropagation.ID);
        // obtain result of live variable analysis
        DataflowResult<Stmt, SetFact<Var>> liveVars =
                ir.getResult(LiveVariableAnalysis.ID);
        // keep statements (dead code) sorted in the resulting set
        Set<Stmt> deadCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        // TODO - finish me
        // Your task is to recognize dead code in ir and add it to deadCode

        // detect control-flow unreachable code & unreachable branch
        detectUnreachable(deadCode, cfg, constants);
        // detect dead assignment
        detectDeadAssign(deadCode, cfg, liveVars);

        return deadCode;
    }

    private void detectUnreachable(Set<Stmt> deadCode, CFG<Stmt> cfg, DataflowResult<Stmt, CPFact> constants) {
        // I first tried to find all the unreachable statements,
        // but found it hard to know where an unreachable block ended,
        // because I can only acquire the first statement of the block.

        // However, it is much easier to find all the reachable statements
        // by continuously get the successors of the current reachable statements.
        // So, we can assume all the statements except the entry are unreachable
        // and continuously remove the reachable ones from the unreachable set.

        Set<Stmt> unreachable = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        unreachable.addAll(cfg.getNodes());
        unreachable.removeAll(List.of(cfg.getEntry(), cfg.getExit()));

        List<Stmt> reachable = new LinkedList<>();
        reachable.add(cfg.getEntry());

        while (!reachable.isEmpty()) {
            Stmt stmt = reachable.get(0);
            reachable.remove(0);

            if (stmt instanceof If ifStmt) {
                Value conditionValue = ConstantPropagation.evaluate(ifStmt.getCondition(), constants.getInFact(ifStmt));

                // dead code happens if the condition is a constant
                if (conditionValue.isConstant()) {
                    Set<Edge<Stmt>> edges = cfg.getOutEdgesOf(ifStmt);

                    assert edges.size() == 2;

                    Stmt ifTrueStmt = null;
                    Stmt ifFalseStmt = null;
                    for (Edge<Stmt> edge : edges) {
                        if (edge.getKind().equals(Edge.Kind.IF_TRUE)) {
                            ifTrueStmt = edge.getTarget();
                        } else {
                            ifFalseStmt = edge.getTarget();
                        }
                    }

                    if (conditionValue.getConstant() == 0) {
                        // in case being added into reachable list more than once
                        if (unreachable.contains(ifFalseStmt)) {
                            unreachable.remove(ifFalseStmt);
                            reachable.add(ifFalseStmt);
                        }
                    } else {
                        // in case being added into reachable list more than once
                        if (unreachable.contains(ifTrueStmt)) {
                            unreachable.remove(ifTrueStmt);
                            reachable.add(ifTrueStmt);
                        }
                    }
                    continue;
                }

            } else if (stmt instanceof SwitchStmt switchStmt) {
                Value caseValue = ConstantPropagation.evaluate(switchStmt.getVar(), constants.getInFact(switchStmt));

                // dead code happens if the condition is a constant
                if (caseValue.isConstant()) {
                    boolean useDefaultEdge = true;
                    Stmt target = switchStmt.getDefaultTarget();
                    for (Pair<Integer, Stmt> caseTarget : switchStmt.getCaseTargets()) {
                        if (caseTarget.first() == caseValue.getConstant()) {
                            useDefaultEdge = false;
                            target = caseTarget.second();
                            // in case being added into reachable list more than once
                            if (unreachable.contains(target)) {
                                unreachable.remove(target);
                                reachable.add(target);
                            }
                        }
                    }
                    if (useDefaultEdge) {
                        // in case being added into reachable list more than once
                        if (unreachable.contains(target)) {
                            unreachable.remove(target);
                            reachable.add(target);
                        }
                    }
                    continue;
                }
            }

            // the statement is neither an if-statement nor a switch-statement with constant condition
            // all the successors of it are reachable
            for (Stmt succ : cfg.getSuccsOf(stmt)) {
                if (unreachable.contains(succ)) {
                    unreachable.remove(succ);
                    reachable.add(succ);
                }
            }
        }

        deadCode.addAll(unreachable);
    }

    private void detectDeadAssign(Set<Stmt> deadCode, CFG<Stmt> cfg, DataflowResult<Stmt, SetFact<Var>> liveVars) {
        for (Stmt stmt : cfg) {
            if (!deadCode.contains(stmt) &&
                    stmt instanceof AssignStmt<?,?> assignStmt &&
                    hasNoSideEffect(assignStmt.getRValue()) &&
                    assignStmt.getLValue() instanceof Var lhs &&
                    !liveVars.getOutFact(assignStmt).contains(lhs)) {
                deadCode.add(assignStmt);
            }
        }
    }

    /**
     * @return true if given RValue has no side effect, otherwise false.
     */
    private static boolean hasNoSideEffect(RValue rvalue) {
        // new expression modifies the heap
        if (rvalue instanceof NewExp ||
                // cast may trigger ClassCastException
                rvalue instanceof CastExp ||
                // static field access may trigger class initialization
                // instance field access may trigger NPE
                rvalue instanceof FieldAccess ||
                // array access may trigger NPE
                rvalue instanceof ArrayAccess) {
            return false;
        }
        if (rvalue instanceof ArithmeticExp) {
            ArithmeticExp.Op op = ((ArithmeticExp) rvalue).getOperator();
            // may trigger DivideByZeroException
            return op != ArithmeticExp.Op.DIV && op != ArithmeticExp.Op.REM;
        }
        return true;
    }
}
