/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package gov.nasa.jpf.listener;

import gov.nasa.jpf.PropertyListenerAdapter;
import gov.nasa.jpf.search.Search;
import gov.nasa.jpf.vm.ChoiceGenerator;
import gov.nasa.jpf.vm.ElementInfo;
import gov.nasa.jpf.vm.FieldInfo;
import gov.nasa.jpf.vm.Instruction;
import gov.nasa.jpf.vm.ThreadInfo;
import gov.nasa.jpf.vm.VM;
import gov.nasa.jpf.vm.bytecode.FieldInstruction;
import gov.nasa.jpf.vm.choice.ThreadChoiceFromSet;
import java.util.List;
import java.util.ArrayList;
import java.util.Map;
import java.util.HashMap;

public class MyListener extends PropertyListenerAdapter {

    Node root = null;
    Node current = null;
    volatile private int depth = 0;
    volatile private int id = 0;
    Map<String,FieldInfo> prevFields = null;

    public MyListener() {
        root = new Node();
        current = new Node();
        current.parent = root;
        root.children.add(current);
        prevFields = new HashMap<>();
    }

    @Override
    public void choiceGeneratorSet(VM vm, ChoiceGenerator<?> cg) {
        boolean found = current.findNode(id,depth);
        
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

                    if (insn instanceof FieldInstruction) { // Ok, its a get/putfield
                        
                        Data newD = new Data();
                        
                        newD.fileLocation = insn.getFileLocation();
                        newD.lineNumber = insn.getLineNumber();
                        newD.methodName = insn.getMethodInfo().getName();
                        newD.isSynchronized = insn.getMethodInfo().isSynchronized();
                    
                        FieldInstruction finsn = (FieldInstruction) insn;
                        
                        if (finsn.isRead())
                            newD.readOperation = true;
                        else
                            newD.writeOperation = true;
                        
                        FieldInfo fi = finsn.getFieldInfo();
      
                        newD.threadName = ti.getName();
                        newD.instance = ti.getThreadObjectClassInfo().toString();
                        newD.className = fi.getClassInfo().getSimpleName();
                        newD.packageName = fi.getClassInfo().getPackageName();
                        newD.fieldName = fi.getName();

                        ElementInfo ei = finsn.peekElementInfo(ti);
                        if (prevFields.get(newD.threadName)!=null) {
                            ei.isLockProtected(prevFields.get(newD.threadName));
                        }
                        prevFields.put(newD.threadName,fi);
                        newD.isLocked = ei.isLocked();
                        newD.lockCount = ti.getLockCount();
                        if (ti.getLockObject()!= null)
                            newD.isLockProtected = ti.getLockObject().getFieldLockInfo(fi).isProtected();
                        newD.lockRef = ti.getLockRef();

                        newN.data.add(newD);
                    }
                            
                }
                
            }
            
            current.children.add(newN);
        }
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
                    if(nd.id == id) {
                        current = nd;
                        found = true;
                        break;
                    }
                }
            } else 
                found = true;
            
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
