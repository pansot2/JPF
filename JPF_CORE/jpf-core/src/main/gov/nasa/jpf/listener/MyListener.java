/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package gov.nasa.jpf.listener;

import gov.nasa.jpf.PropertyListenerAdapter;
import gov.nasa.jpf.jvm.bytecode.MONITORENTER;
import gov.nasa.jpf.jvm.bytecode.MONITOREXIT;
import gov.nasa.jpf.jvm.bytecode.EXECUTENATIVE;
import gov.nasa.jpf.search.Search;
import gov.nasa.jpf.vm.ChoiceGenerator;
import gov.nasa.jpf.vm.ElementInfo;
import gov.nasa.jpf.vm.FieldInfo;
import gov.nasa.jpf.vm.Instruction;
import gov.nasa.jpf.vm.ThreadInfo;
import gov.nasa.jpf.vm.VM;
import gov.nasa.jpf.vm.bytecode.FieldInstruction;
import gov.nasa.jpf.vm.bytecode.InvokeInstruction;
import gov.nasa.jpf.vm.choice.ThreadChoiceFromSet;
import gov.nasa.jpf.vm.StackFrame;
import java.util.List;
import java.util.ArrayList;
import java.util.Map;
import java.util.HashMap;

public class MyListener extends PropertyListenerAdapter {

    Node root = null;
    Node current = null;
    volatile private int depth = 0;
    volatile private int id = 0;
    Map<String, FieldInfo> prevFields = null;
    Map<String, FieldInfo> lockFields = null;

    enum OpType {
        block, lock, unlock, wait, notify, notifyAll, started, terminated
    };
    ThreadOp lastOp;

    public MyListener() {
        root = new Node();
        current = new Node();
        current.parent = root;
        root.children.add(current);
        prevFields = new HashMap<>();
        lockFields = new HashMap<>();
    }

    @Override
    public void choiceGeneratorSet(VM vm, ChoiceGenerator<?> cg) {
        boolean found = current.findNode(id, depth);

        if (!found) {

            Node newN = new Node();
            newN.parent = current;
            newN.depth = depth;
            newN.id = id;

            if (cg instanceof ThreadChoiceFromSet) {
                ThreadInfo[] threads = ((ThreadChoiceFromSet) cg).getAllThreadChoices();

                for (int i = 0; i < threads.length; i++) {
                    ThreadInfo ti = threads[i];
                    Instruction insn = ti.getPC();

                    if (insn instanceof MONITORENTER) {
                        System.out.println("****** MENT : " + prevFields.get(ti.getName()));

                        MONITORENTER mentsinsn = (MONITORENTER) insn;
                        System.out.println("#####" + mentsinsn.getLastLockRef());
                    }

                    if (insn instanceof MONITOREXIT) {
                        MONITOREXIT mexinsn = (MONITOREXIT) insn;

                        if (prevFields.get(ti.getName()) != null) {
                            System.out.println("****** MEX : " + prevFields.get(ti.getName()));
                        }

                        System.out.println("#####" + mexinsn.getLastLockRef());
                    }

                    if (insn instanceof FieldInstruction) { // Ok, its a get/putfield

                        Data newD = new Data();

                        newD.fileLocation = insn.getFileLocation();
                        newD.lineNumber = insn.getLineNumber();
                        newD.methodName = insn.getMethodInfo().getName();
                        newD.isSynchronized = insn.getMethodInfo().isSynchronized();

                        FieldInstruction finsn = (FieldInstruction) insn;

                        if (finsn.isRead()) {
                            newD.readOperation = true;
                        } else {
                            newD.writeOperation = true;
                        }
                        System.out.println("++++" + finsn.isMonitorEnterPrologue() + " " + finsn.getFieldName() + " " + finsn.getSourceLine());
                        FieldInfo fi = finsn.getFieldInfo();

                        newD.threadName = ti.getName();

                        newD.instance = ti.getThreadObjectClassInfo().toString();
                        newD.className = fi.getClassInfo().getSimpleName();
                        newD.packageName = fi.getClassInfo().getPackageName();
                        newD.fieldName = fi.getName();

                        ElementInfo ei = lastOp.ei;
                        if (prevFields.get(newD.threadName) != null) {
                            System.out.println("========" + prevFields.get(newD.threadName).getFullName());
                            try {
                                newD.isLockProtected = ei.isLockProtected(prevFields.get(newD.threadName));
                            } catch (Exception e) {
                                System.out.println(e.getMessage());
                            }
                        }
                        prevFields.put(newD.threadName, fi);
                        try {
                            newD.isLocked = ei.isLocked();
                        
                            newD.lockCount = lastOp.ti.getLockCount();

                            newD.lockRef = lastOp.ti.getLockRef();
                        } catch (Exception e){
                            System.out.println(e.getMessage());
                        }
                        prevFields.put(newD.threadName, fi);
                        newN.data.add(newD);
                    }

                    if (insn instanceof InvokeInstruction) {
                        InvokeInstruction ikinsn = (InvokeInstruction) insn;

                        // ikinsn.
                    }

                }

            }

            current.children.add(newN);
        }
    }

    static class ThreadOp {

        ThreadInfo ti;
        ElementInfo ei;
        Instruction insn;

        // kind of redundant, but there might be context attributes in addition
        // to the insn itself
        OpType opType;

        // we could identify this with the insn, but only in case this is
        // a transition boundary, which is far less general than we can be
        int stateId;
        ThreadOp prevOp;

        ThreadOp(ThreadInfo ti, ElementInfo ei, OpType type, int id) {
            this.ti = ti;
            this.ei = ei;
            insn = getReportInsn(ti); // we haven't had the executeInsn notification yet
            opType = type;
            stateId = id;
            prevOp = null;
        }

        Instruction getReportInsn(ThreadInfo ti) {
            StackFrame frame = ti.getTopFrame();
            if (frame != null) {
                Instruction insn = frame.getPC();
                if (insn instanceof EXECUTENATIVE) {
                    frame = frame.getPrevious();
                    if (frame != null) {
                        insn = frame.getPC();
                    }
                }

                return insn;
            } else {
                return null;
            }
        }

        void printLocOn() {
            System.out.println(String.format("%6d", new Integer(stateId)));

            if (insn != null) {
                System.out.print(String.format(" %18.18s ", insn.getMnemonic()));
                System.out.print(insn.getFileLocation());
                String line = insn.getSourceLine();
                if (line != null) {
                    System.out.print(" : ");
                    System.out.print(line.trim());
                    //System.out.print(insn);
                }
            }
        }

        void printOn() {
            System.out.println(stateId);
            System.out.print(" : ");
            System.out.print(ti.getName());
            System.out.print(" : ");
            System.out.print(opType.name());
            System.out.print(" : ");
            System.out.println(ei);
        }

        @Override
        public String toString() {
            StringBuilder sb = new StringBuilder();
            sb.append(stateId);
            sb.append(" : ");
            sb.append(ti.getName());
            sb.append(" : ");
            sb.append(opType.name());
            sb.append(" : ");
            sb.append(ei);
            return sb.toString();
        }

    }

    void addOp(ThreadInfo ti, ElementInfo ei, OpType opType) {
        ThreadOp op = new ThreadOp(ti, ei, opType, id);
        if (lastOp == null) {
            lastOp = op;
        } else {
            assert lastOp.stateId == 0;

            op.prevOp = lastOp;
            lastOp = op;
        }
    }

    @Override
    public void objectLocked(VM vm, ThreadInfo ti, ElementInfo ei) {
        addOp(ti, ei, OpType.lock);
        lastOp.printLocOn();
        lastOp.printOn();
    }

    @Override
    public void objectUnlocked(VM vm, ThreadInfo ti, ElementInfo ei) {
        addOp(ti, ei, OpType.unlock);
        lastOp.printLocOn();
        lastOp.printOn();
    }

    @Override
    public void objectWait(VM vm, ThreadInfo ti, ElementInfo ei) {
        addOp(ti, ei, OpType.wait);
    }

    @Override
    public void objectNotify(VM vm, ThreadInfo ti, ElementInfo ei) {
        addOp(ti, ei, OpType.notify);
    }

    @Override
    public void objectNotifyAll(VM vm, ThreadInfo ti, ElementInfo ei) {
        addOp(ti, ei, OpType.notifyAll);
    }

    @Override
    public void threadBlocked(VM vm, ThreadInfo ti, ElementInfo ei) {
        addOp(ti, ei, OpType.block);
    }

    @Override
    public void threadStarted(VM vm, ThreadInfo ti) {
        addOp(ti, null, OpType.started);
    }

    @Override
    public void stateRestored(Search search) {
        id = search.getStateId();
        depth = search.getDepth();
    }

    //--- the ones we are interested in
    @Override
    public void searchStarted(Search search) {
        System.out.println("----------------------------------- search started");
    }

    @Override
    public void stateAdvanced(Search search) {
        id = search.getStateId();
        depth = search.getDepth();
    }

    @Override
    public void stateBacktracked(Search search) {
        id = search.getStateId();
        depth = search.getDepth();
    }

    @Override
    public void searchFinished(Search search) {
        System.out.println("----------------------------------- search finished");

            printTree(root);
    }

    public void printTree(Node myNode) {

        List<Data> ld = myNode.data;

        for (Data d : ld) {
            System.out.println();
            System.out.print("id : " + myNode.id);
            System.out.print(" depth : " + myNode.depth);
            System.out.print(" fieldName : " + d.fieldName);
            System.out.print(" lineNumber : " + d.lineNumber);
            System.out.print(" methodName : " + d.methodName);
            System.out.print(" className : " + d.className);
            System.out.print(" instance : " + d.instance);
            System.out.print(" isLocked : " + d.isLocked);
            System.out.print(" fieldLock : " + d.fieldLock);
            System.out.print(" writeOperation : " + d.writeOperation);
            System.out.print(" readOperation : " + d.readOperation);
            System.out.print(" threadName : " + d.threadName);
            System.out.print(" isSynchronized : " + d.isSynchronized);
            System.out.print(" packageName : " + d.packageName);
            System.out.print(" fileLocation : " + d.fileLocation);
            System.out.print(" lockCount : " + d.lockCount);
            System.out.print(" isLockProtected : " + d.isLockProtected);
            System.out.print(" lockRef : " + d.lockRef);
        }

        for (Node nd : myNode.children) {
            printTree(nd);
        }
    }

    class Node {

        protected List<Data> data = new ArrayList<Data>();
        protected Node parent = null;
        protected List<Node> children = new ArrayList<Node>();
        protected int id = 0;
        protected int depth = 0;

        public boolean findNode(int id, int depth) {
            boolean found = false;

            while (current.id > id && current.id != 0) {
                current = current.parent;
            }

            if (current.id != id) {
                for (Node nd : current.children) {
                    if (nd.id == id) {
                        current = nd;
                        found = true;
                        break;
                    }
                }
            } else {
                found = true;
            }

            return found;
        }
    }

    class Data {

        String fieldName = null;
        String className = null;
        String instance = null;
        boolean isLocked = false;
        String fieldLock = null;
        boolean writeOperation = false;
        boolean readOperation = false;
        String threadName = null;
        String methodName = null;
        boolean isSynchronized = false;
        String fileLocation = null;
        int lineNumber = -1;
        String packageName = null;
        int lockCount = -1;
        boolean isLockProtected = false;
        int lockRef = -1;
    }

}
