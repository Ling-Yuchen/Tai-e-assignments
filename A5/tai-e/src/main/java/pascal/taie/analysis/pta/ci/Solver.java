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

package pascal.taie.analysis.pta.ci;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.DefaultCallGraph;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.AnalysisException;
import pascal.taie.language.type.Type;
import pascal.taie.util.collection.Sets;

import java.util.List;
import java.util.Set;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final HeapModel heapModel;

    private DefaultCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private StmtProcessor stmtProcessor;

    private ClassHierarchy hierarchy;

    Solver(HeapModel heapModel) {
        this.heapModel = heapModel;
    }

    /**
     * Runs pointer analysis algorithm.
     */
    void solve() {
        initialize();
        analyze();
    }

    /**
     * Initializes pointer analysis.
     */
    private void initialize() {
        workList = new WorkList();
        pointerFlowGraph = new PointerFlowGraph();
        callGraph = new DefaultCallGraph();
        stmtProcessor = new StmtProcessor();
        hierarchy = World.get().getClassHierarchy();
        // initialize main method
        JMethod main = World.get().getMainMethod();
        callGraph.addEntryMethod(main);
        addReachable(main);
    }

    /**
     * Processes new reachable method.
     */
    private void addReachable(JMethod method) {
        // TODO - finish me
        if (callGraph.addReachableMethod(method)) {
            for (Stmt stmt : method.getIR().getStmts()) {
                // Statements below are required to deal with here:
                //      x = new T()
                //      x = y
                //      T.f = y
                //      x = T.f
                //      x = T.m(a1,...,an) / T.m(a1,...,an)
                if (stmt instanceof New ||
                        stmt instanceof Copy ||
                        stmt instanceof StoreField store && store.isStatic() ||
                        stmt instanceof LoadField load && load.isStatic() ||
                        stmt instanceof Invoke invoke && invoke.isStatic()) {
                    // use visitor pattern
                    stmt.accept(stmtProcessor);
                }
            }
        }
    }

    /**
     * Processes statements in new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {
        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me

        @Override
        public Void visit(New stmt) {
            VarPtr varPtr = pointerFlowGraph.getVarPtr(stmt.getLValue());
            PointsToSet flowedInObjs = new PointsToSet(heapModel.getObj(stmt));
            workList.addEntry(varPtr, flowedInObjs);
            return StmtVisitor.super.visit(stmt);
        }

        @Override
        public Void visit(Copy stmt) {
            VarPtr sourcePtr = pointerFlowGraph.getVarPtr(stmt.getRValue());
            VarPtr targetPtr = pointerFlowGraph.getVarPtr(stmt.getLValue());
            addPFGEdge(sourcePtr, targetPtr);
            return StmtVisitor.super.visit(stmt);
        }

        @Override
        public Void visit(LoadField stmt) {
            if (stmt.isStatic()) {
                JField staticField = stmt.getFieldRef().resolve();
                StaticField sourcePtr = pointerFlowGraph.getStaticField(staticField);
                VarPtr targetPtr = pointerFlowGraph.getVarPtr(stmt.getLValue());
                addPFGEdge(sourcePtr, targetPtr);
            }
            return StmtVisitor.super.visit(stmt);
        }

        @Override
        public Void visit(StoreField stmt) {
            if (stmt.isStatic()) {
                JField staticField = stmt.getFieldRef().resolve();
                StaticField targetPtr = pointerFlowGraph.getStaticField(staticField);
                VarPtr sourcePtr = pointerFlowGraph.getVarPtr(stmt.getRValue());
                addPFGEdge(sourcePtr, targetPtr);
            }
            return StmtVisitor.super.visit(stmt);
        }

        @Override
        public Void visit(Invoke stmt) {
            if (stmt.isStatic()) {
                JMethod staticMethod = resolveCallee(null, stmt);
                if (callGraph.addEdge(new Edge<>(CallKind.STATIC, stmt, staticMethod))) {
                    // deal with addReachable, arguments and parameters, return variables
                    handleNewReachableMethod(staticMethod, stmt);
                }
            }
            return StmtVisitor.super.visit(stmt);
        }

        public void handleNewReachableMethod(JMethod method, Invoke callSite) {
            addReachable(method);
            for (int i = 0; i < method.getParamCount(); ++i) {
                VarPtr sourcePtr = pointerFlowGraph.getVarPtr(callSite.getInvokeExp().getArg(i));
                VarPtr targetPtr = pointerFlowGraph.getVarPtr(method.getIR().getParam(i));
                addPFGEdge(sourcePtr, targetPtr);
            }
            // note there may be no result in the callSite
            Var resultVar = callSite.getResult();
            if (resultVar != null) {
                VarPtr resultVarPtr = pointerFlowGraph.getVarPtr(resultVar);
                for (Var returnVar : method.getIR().getReturnVars()) {
                    VarPtr returnVarPtr = pointerFlowGraph.getVarPtr(returnVar);
                    addPFGEdge(returnVarPtr, resultVarPtr);
                }
            }
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        // TODO - finish me
        if (pointerFlowGraph.addEdge(source, target)) {
            PointsToSet setFromSource = source.getPointsToSet();
            if (!setFromSource.isEmpty()) {
                workList.addEntry(target, setFromSource);
            }
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        // TODO - finish me
        while (!workList.isEmpty()) {
            WorkList.Entry entry = workList.pollEntry();
            Pointer pointer = entry.pointer();
            PointsToSet pts = entry.pointsToSet();
            PointsToSet delta = propagate(pointer, pts);
            if (pointer instanceof VarPtr varPtr) {
                Var var = varPtr.getVar();
                for (Obj obj : delta) {
                    for (StoreField store : var.getStoreFields()) {
                        JField instanceField = store.getFieldRef().resolve();
                        InstanceField targetPtr = pointerFlowGraph.getInstanceField(obj, instanceField);
                        VarPtr sourcePtr = pointerFlowGraph.getVarPtr(store.getRValue());
                        addPFGEdge(sourcePtr, targetPtr);
                    }
                    for (LoadField load : var.getLoadFields()) {
                        JField instanceField = load.getFieldRef().resolve();
                        InstanceField sourcePtr = pointerFlowGraph.getInstanceField(obj, instanceField);
                        VarPtr targetPtr = pointerFlowGraph.getVarPtr(load.getLValue());
                        addPFGEdge(sourcePtr, targetPtr);
                    }
                    for (StoreArray store : var.getStoreArrays()) {
                        ArrayIndex targetPtr = pointerFlowGraph.getArrayIndex(obj);
                        VarPtr sourcePtr = pointerFlowGraph.getVarPtr(store.getRValue());
                        addPFGEdge(sourcePtr, targetPtr);
                    }
                    for (LoadArray load : var.getLoadArrays()) {
                        ArrayIndex sourcePtr = pointerFlowGraph.getArrayIndex(obj);
                        VarPtr targetPtr = pointerFlowGraph.getVarPtr(load.getLValue());
                        addPFGEdge(sourcePtr, targetPtr);
                    }
                    processCall(var, obj);
                }
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        // TODO - finish me
        PointsToSet delta = new PointsToSet();
        PointsToSet currentSet = pointer.getPointsToSet();
        if (!pointsToSet.isEmpty()) {
            for (Obj obj : pointsToSet) {
                if (currentSet.addObject(obj)) {
                    delta.addObject(obj);
                }
            }
            for (Pointer succPtr : pointerFlowGraph.getSuccsOf(pointer)) {
                workList.addEntry(succPtr, delta);
            }
        }
        return delta;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param var the variable that holds receiver objects
     * @param recv a new discovered object pointed by the variable.
     */
    private void processCall(Var var, Obj recv) {
        // TODO - finish me
        for (Invoke callSite : var.getInvokes()) {
            // m = dispatch(o_i, k)
            JMethod method = resolveCallee(recv, callSite);

            // add <m_this, [o_i]> to WL
            Pointer thisPtr = pointerFlowGraph.getVarPtr(method.getIR().getThis());
            workList.addEntry(thisPtr, new PointsToSet(recv));

            // add a new edge to call graph
            CallKind callKind;
            if (callSite.isStatic()) { callKind = CallKind.STATIC; }
            else if (callSite.isSpecial()) { callKind = CallKind.SPECIAL; }
            else if (callSite.isInterface()) { callKind = CallKind.INTERFACE; }
            else if (callSite.isVirtual()) { callKind = CallKind.VIRTUAL; }
            else if (callSite.isDynamic()) { callKind = CallKind.DYNAMIC; }
            else { callKind = CallKind.OTHER; }
            assert callKind != CallKind.STATIC;
            if (callGraph.addEdge(new Edge<>(callKind, callSite, method))) {
                // deal with addReachable, arguments and parameters, return variables
                stmtProcessor.handleNewReachableMethod(method, callSite);
            }
        }
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv     the receiver object of the method call. If the callSite
     *                 is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(Obj recv, Invoke callSite) {
        Type type = recv != null ? recv.getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    CIPTAResult getResult() {
        return new CIPTAResult(pointerFlowGraph, callGraph);
    }
}
