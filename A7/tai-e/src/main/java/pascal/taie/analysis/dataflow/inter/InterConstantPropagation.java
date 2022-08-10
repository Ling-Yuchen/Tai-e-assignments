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

package pascal.taie.analysis.dataflow.inter;

import pascal.taie.World;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.icfg.*;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;

import java.util.HashSet;
import java.util.Set;

/**
 * Implementation of interprocedural constant propagation for int values.
 */
public class InterConstantPropagation extends
        AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {

    public static final String ID = "inter-constprop";

    private final ConstantPropagation cp;

    private PointerAnalysisResult pta;

    public InterConstantPropagation(AnalysisConfig config) {
        super(config);
        cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
    }

    @Override
    protected void initialize() {
        String ptaId = getOptions().getString("pta");
        pta = World.get().getResult(ptaId);
        // You can do initialization work here
    }

    @Override
    public boolean isForward() {
        return cp.isForward();
    }

    @Override
    public CPFact newBoundaryFact(Stmt boundary) {
        IR ir = icfg.getContainingMethodOf(boundary).getIR();
        return cp.newBoundaryFact(ir.getResult(CFGBuilder.ID));
    }

    @Override
    public CPFact newInitialFact() {
        return cp.newInitialFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        cp.meetInto(fact, target);
    }

    @Override
    protected boolean transferCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        assert stmt instanceof Invoke;
        return out.copyFrom(in);
    }

    @Override
    protected boolean transferNonCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        if (stmt instanceof LoadField loadField) {
            // x = T.f
            if (loadField.isStatic()) {
                FieldAccess fieldAccess = loadField.getFieldAccess();
                Value valueFromStaticField = Value.getUndef();
                for (Stmt store : this.icfg) {
                    if (store instanceof StoreField storeField &&
                            storeField.isStatic() &&
                            isAlias(fieldAccess, storeField.getFieldAccess())) {
                        CPFact fact = this.solver.getResult().getOutFact(storeField);
                        valueFromStaticField = cp.meetValue(valueFromStaticField, fact.get(storeField.getRValue()));
                    }
                }
                CPFact temp = in.copy();
                temp.update(loadField.getLValue(), valueFromStaticField);
                return out.copyFrom(temp);
            // x = y.f
            } else {
                FieldAccess fieldAccess = loadField.getFieldAccess();
                Value valueFromInstanceField = Value.getUndef();
                for (Stmt store : this.icfg) {
                    if (store instanceof StoreField storeField &&
                            !storeField.isStatic() &&
                            isAlias(fieldAccess, storeField.getFieldAccess())) {
                        CPFact fact = this.solver.getResult().getOutFact(storeField);
                        valueFromInstanceField = cp.meetValue(valueFromInstanceField, fact.get(storeField.getRValue()));
                    }
                }
                CPFact temp = in.copy();
                temp.update(loadField.getLValue(), valueFromInstanceField);
                return out.copyFrom(temp);
            }
        }
        // x = a[i]
        if (stmt instanceof LoadArray loadArray) {
            Value valueFromArray = Value.getUndef();
            for (Stmt store : this.icfg) {
                if (store instanceof StoreArray storeArray &&
                        isAlias(loadArray, storeArray)) {
                    CPFact fact = this.solver.getResult().getOutFact(storeArray);
                    valueFromArray = cp.meetValue(valueFromArray, fact.get(storeArray.getRValue()));
                }
            }
            CPFact temp = in.copy();
            temp.update(loadArray.getLValue(), valueFromArray);
            return out.copyFrom(temp);
        }

        if (stmt instanceof StoreField storeField) {
            // T.f = x
            if (storeField.isStatic()) {
                for (Stmt load : this.icfg) {
                    if (load instanceof LoadField loadField &&
                            loadField.isStatic() &&
                            isAlias(loadField.getFieldAccess(), storeField.getFieldAccess())) {
                        this.solver.addToWorkList(load);
                    }
                }
            // y.f = x
            } else {
                FieldAccess fieldAccess = storeField.getFieldAccess();
                for (Var var : pta.getVars()) {
                    for (LoadField loadField : var.getLoadFields()) {
                        if (isAlias(loadField.getFieldAccess(), fieldAccess)) {
                            this.solver.addToWorkList(loadField);
                        }
                    }
                }
            }
        }
        // a[i] = x
        if (stmt instanceof StoreArray storeArray) {
            for (Var var : pta.getVars()) {
                for (LoadArray loadArray : var.getLoadArrays()) {
                    if (isAlias(loadArray, storeArray)) {
                        this.solver.addToWorkList(loadArray);
                    }
                }
            }
        }

        return cp.transferNode(stmt, in, out);
    }

    @Override
    protected CPFact transferNormalEdge(NormalEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        return out.copy();
    }

    @Override
    protected CPFact transferCallToReturnEdge(CallToReturnEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        assert edge.getSource() instanceof Invoke;

        Invoke callSite = (Invoke) edge.getSource();
        CPFact fact = out.copy();
        Var result = callSite.getResult();
        if (result != null) {
            fact.remove(result);
        }
        return fact;
    }

    @Override
    protected CPFact transferCallEdge(CallEdge<Stmt> edge, CPFact callSiteOut) {
        // TODO - finish me
        assert edge.getSource() instanceof Invoke;

        Invoke callSite = (Invoke) edge.getSource();
        JMethod callee = edge.getCallee();
        CPFact fact = new CPFact();
        for (int i = 0; i < callSite.getInvokeExp().getArgs().size(); ++i) {
            Value argValue = callSiteOut.get(callSite.getInvokeExp().getArgs().get(i));
            fact.update(callee.getIR().getParam(i), argValue);
        }
        return fact;
    }

    @Override
    protected CPFact transferReturnEdge(ReturnEdge<Stmt> edge, CPFact returnOut) {
        // TODO - finish me
        assert edge.getCallSite() instanceof Invoke;

        Invoke callSite = (Invoke) edge.getCallSite();
        CPFact fact = new CPFact();
        Var result = callSite.getResult();
        if (result != null) {
            Value returnValue = Value.getUndef();
            for (Var returnVar : edge.getReturnVars()) {
                returnValue = cp.meetValue(returnValue, returnOut.get(returnVar));
            }
            fact.update(result, returnValue);
        }
        return fact;
    }

    private boolean isAlias(Var var1, Var var2) {
        Set<Obj> base1Pts = new HashSet<>(pta.getPointsToSet(var1));
        Set<Obj> base2Pts = new HashSet<>(pta.getPointsToSet(var2));
        base1Pts.retainAll(base2Pts);
        return !base1Pts.isEmpty();
    }

    private boolean isAlias(FieldAccess access1, FieldAccess access2) {
        JField field1 = access1.getFieldRef().resolve();
        JField field2 = access2.getFieldRef().resolve();
        if (!field1.equals(field2)) {
            return false;
        }
        if (access1 instanceof InstanceFieldAccess ifa1) {
            assert access2 instanceof InstanceFieldAccess;
            InstanceFieldAccess ifa2 = (InstanceFieldAccess) access2;
            return isAlias(ifa1.getBase(), ifa2.getBase());
        }
        assert access1.getFieldRef().isStatic();
        assert access2.getFieldRef().isStatic();
        JClass clazz1 = access1.getFieldRef().getDeclaringClass();
        JClass clazz2 = access2.getFieldRef().getDeclaringClass();
        return clazz1.equals(clazz2);
    }

    private boolean isAlias(LoadArray loadArray, StoreArray storeArray) {
        ArrayAccess loadAccess = loadArray.getArrayAccess();
        ArrayAccess storeAccess = storeArray.getArrayAccess();

        Set<Obj> base1Pts = new HashSet<>(pta.getPointsToSet(loadAccess.getBase()));
        Set<Obj> base2Pts = new HashSet<>(pta.getPointsToSet(storeAccess.getBase()));
        base1Pts.retainAll(base2Pts);
        if (base1Pts.isEmpty()) {
            return false;
        }
        CPFact fact1 = this.solver.getResult().getInFact(loadArray);
        CPFact fact2 = this.solver.getResult().getInFact(storeArray);
        Value index1 = fact1.get(loadAccess.getIndex());
        Value index2 = fact2.get(storeAccess.getIndex());
        return index1.isNAC() && !index2.isUndef() ||
                index2.isNAC() && !index1.isUndef() ||
                index1.isConstant() && index2.isConstant() && index1.getConstant() == index2.getConstant();
    }
}
