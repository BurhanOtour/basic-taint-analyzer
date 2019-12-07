package me.burhanotour.apps.sootexample.analysis;

import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import me.burhanotour.apps.sootexample.reporting.Reporter;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import soot.*;
import soot.jimple.*;
import soot.toolkits.graph.ExceptionalUnitGraph;
import soot.toolkits.scalar.ForwardFlowAnalysis;

/**
 * Class implementing dataflow analysis
 */
public class IntraproceduralAnalysis extends ForwardFlowAnalysis<Unit, Set<FlowAbstraction>> {

    private final Logger logger = LoggerFactory.getLogger(getClass());
    private static int counter = 0;
    public int flowThroughCount = 0;
    private final SootMethod method;
    private final Reporter reporter;

    public IntraproceduralAnalysis(Body b, Reporter reporter, int exerciseNumber) {
        super(new ExceptionalUnitGraph(b));
        this.method = b.getMethod();
        this.reporter = reporter;
        logger.info("Analyzing method " + b.getMethod().getSignature() + "\n" + b);
    }

    @Override
    protected void flowThrough(Set<FlowAbstraction> taintsIn, Unit d, Set<FlowAbstraction> taintsOut) {
        Stmt s = (Stmt) d;
        logger.info("Unit " + d.getClass().getName() + " " + d);
        System.out.println("Unit " + d.getClass().getName() + " " + d);

        if (s instanceof AssignStmt) {
            // Declare a tainted local attribute
            AssignStmt assignStmt = (AssignStmt) s;
            // Fetch left side of the assignment
            List<ValueBox> defBoxes = assignStmt.getDefBoxes();
            // Fetch right side of the assignment
            List<ValueBox> useBoxes = assignStmt.getUseBoxes();
            if (defBoxes.size() > 0 && useBoxes.size() > 0) {
                Value defValue = defBoxes.get(0).getValue();
                if (defValue instanceof Local || defValue instanceof SootField) {
                    for (ValueBox useBox : useBoxes) {
                        if (useBox.getValue() instanceof VirtualInvokeExpr) {
                            // If the right value of the assignment is an invocation to another method
                            VirtualInvokeExpr rValueInvocation = (VirtualInvokeExpr) useBox.getValue();
                            // according to documentation, Jimple IR enforce the 3-address form via linearization so even a single invocation expression to foo() method in represented as assignment to a stack variable ex. $v
                            // That is why I processed the secret leak situation inside of  if (s instanceof AssignStmt) block

                            List<Value> args = rValueInvocation.getArgs();
                            Iterator<Value> valueIterator = args.iterator();
                            while (valueIterator.hasNext()) {
                                Value nextArgValue = valueIterator.next();
                                Iterator<FlowAbstraction> iterator = taintsIn.iterator();
                                while (iterator.hasNext()) {
                                    FlowAbstraction currentTaintVariableUnderInspection = iterator.next();
                                    if (nextArgValue.equals(currentTaintVariableUnderInspection.getField()) || nextArgValue.equals(currentTaintVariableUnderInspection.getLocal())) {
                                        reporter.report(this.method, currentTaintVariableUnderInspection.getSource(), d);
                                    }
                                }
                            }
                        } else if (useBox.getValue() instanceof SpecialInvokeExpr) {
                            // Add a new tainted local/ field variable
                            SpecialInvokeExpr invokedMethod = (SpecialInvokeExpr) useBox.getValue();
                            if (invokedMethod.getMethod().getName().equalsIgnoreCase("getSecret")) {
                                addToTainted(d, taintsOut, defValue);
                            }
                        } else if (useBox.getValue() instanceof Constant) {
                            // Defuse a tainted local variable if it is assigned to a constant
                            Iterator<FlowAbstraction> iterator = taintsIn.iterator();
                            while (iterator.hasNext()) {
                                FlowAbstraction currentTaintVariableUnderInspection = iterator.next();
                                if ((currentTaintVariableUnderInspection.getLocal() != null && currentTaintVariableUnderInspection.getLocal().equals(defValue))
                                        || (currentTaintVariableUnderInspection.getField() != null && currentTaintVariableUnderInspection.getField().equals(defValue))) {
                                    taintsIn.remove(currentTaintVariableUnderInspection);
                                }
                            }
                        } else if (useBox.getValue() instanceof Local) {
                            Local rValueLocal = (Local) useBox.getValue();
                            Iterator<FlowAbstraction> iterator = taintsIn.iterator();
                            while (iterator.hasNext()) {
                                FlowAbstraction currentTaintVariableUnderInspection = iterator.next();
                                if (currentTaintVariableUnderInspection.getLocal().equals(rValueLocal)) {
                                    addToTainted(d, taintsOut, defValue);
                                }
                            }
                        }
                    }
                }
            }
        }

        if (s instanceof ReturnStmt) {
            ReturnStmt returnStmt = (ReturnStmt) s;
            Value returnedValue = returnStmt.getOp();
            Iterator<FlowAbstraction> iterator = taintsIn.iterator();
            while (iterator.hasNext()) {
                FlowAbstraction fa = iterator.next();
                // FlowAbstraction has either a local or a field value not equal to null
                if (returnedValue.equals(fa.getLocal()) || returnedValue.equals(fa.getField())) {
                    reporter.report(this.method, fa.getSource(), d);
                }
            }
        }
        // Pass in the taints to the next unit note processing
        taintsOut.addAll(taintsIn);
    }

    private static void addToTainted(Unit d, Set<FlowAbstraction> taintsOut, Value useValue) {
        if (useValue instanceof Local) {
            taintsOut.add(new FlowAbstraction(d, (Local) useValue));
        } else if (useValue instanceof SootField) {
            taintsOut.add(new FlowAbstraction(d, (SootField) useValue));
        }
    }

    @Override
    protected Set<FlowAbstraction> newInitialFlow() {
        return new HashSet<FlowAbstraction>();
    }

    @Override
    protected Set<FlowAbstraction> entryInitialFlow() {
        return new HashSet<FlowAbstraction>();
    }

    @Override
    protected void merge(Set<FlowAbstraction> in1, Set<FlowAbstraction> in2, Set<FlowAbstraction> out) {
        out.addAll(in1);
        out.addAll(in2);
    }

    @Override
    protected void copy(Set<FlowAbstraction> source, Set<FlowAbstraction> dest) {
        dest.clear();
        dest.addAll(source);
    }

    public void doAnalyis() {
        super.doAnalysis();
    }

}
