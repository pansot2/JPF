/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package gov.nasa.jpf.listener;
import com.mongodb.BasicDBObject;
import com.mongodb.DB;
import com.mongodb.DBCollection;
import com.mongodb.DBObject;
import com.mongodb.MongoClient;
import com.mongodb.MongoClientURI;
import gov.nasa.jpf.PropertyListenerAdapter;
import gov.nasa.jpf.jvm.bytecode.MONITORENTER;
import gov.nasa.jpf.jvm.bytecode.MONITOREXIT;
import gov.nasa.jpf.search.Search;
import gov.nasa.jpf.util.DeepClone;
import gov.nasa.jpf.vm.ChoiceGenerator;
import gov.nasa.jpf.vm.FieldInfo;
import gov.nasa.jpf.vm.Instruction;
import gov.nasa.jpf.vm.LocalVarInfo;
import gov.nasa.jpf.vm.MethodInfo;
import gov.nasa.jpf.vm.ThreadInfo;
import gov.nasa.jpf.vm.VM;
import gov.nasa.jpf.vm.bytecode.FieldInstruction;
import gov.nasa.jpf.vm.bytecode.InvokeInstruction;
import gov.nasa.jpf.vm.bytecode.LocalVariableInstruction;
import gov.nasa.jpf.vm.choice.ThreadChoiceFromSet;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.util.List;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import java.util.logging.Level;
import java.util.logging.Logger;

public class MyListener extends PropertyListenerAdapter {

    Node root = null;
    Node current = null;
    volatile private int depth = 0;
    volatile private int id = 0;
    HashMap<Long, Integer> parentLockRemovals = null;
    Set<String> allowDepth = null;
    Set<String> allowChild = null;
    Set<String> allowThreads = null;
    HashMap<String, ArrayList<String>> threadsDepMap = null;
    HashMap<Integer, ArrayList<Integer>> allowedPaths = null;
    int previousId = -1;
//    ArrayList<Integer> statesHistory = new ArrayList<Integer>();
//    ArrayList<String> statesAction = new ArrayList<String>();
    StateNode rootNode = new StateNode();
    HashMap<Integer, StateNode> stateMap = new HashMap<>();
//    ArrayList<Integer> statesExcluded = new ArrayList<Integer>();
//    ArrayList<Integer> statesIncluded = new ArrayList<Integer>();
    HashMap<Integer, Node> nodesIncluded = new HashMap<>();
    HashMap<Integer, Boolean> isEndState = new HashMap<>();
    HashMap<Integer, Integer> stateGroups = new HashMap<>();
    HashMap<String, Integer> stateGroupMap = new HashMap<>();
    HashMap<Integer, String> stateGroupMap2 = new HashMap<>();
    HashSet<Integer> firstElements = new HashSet<>();
    HashSet<String> finalSequences = new HashSet<>();
    HashSet<String> errors = new HashSet<>();
    HashMap<String, HashSet<String>> threadNames = new HashMap<>();
    int endNodes = 0;
    HashSet<String> fieldNames = new HashSet<>();
    HashMap<String, ArrayList<String>> functions = new HashMap<>();
    HashMap<String, ArrayList<String>> functionsMapping = new HashMap<>();
    Set<String> functionNames = new HashSet<>();
    BufferedWriter bw;
    DBCollection collection;

    public MyListener() {
        root = new Node();
        current = new Node();
        current.parent = root;
        root.children.add(current);
        allowedPaths = new HashMap<>();

        if (VM.getVM().getConfig().get("fieldNames") != null) {
            String[] fields = VM.getVM().getConfig().get("fieldNames").toString().split(",");
            if (fields != null) {
                fieldNames = new HashSet<String>(Arrays.asList(fields));
            }
        }
        if (VM.getVM().getConfig().get("vm.functions") != null) {
            String[] functions = VM.getVM().getConfig().get("vm.functions").toString().split(";");
            if (functions != null) {
                for(String f:functions) {
                    String fname = f.substring(0, f.indexOf("("));
                    String fparams =f.substring(f.indexOf("(")+1, f.indexOf(")"));
                    ArrayList<String> pa = new ArrayList<>();
                    if(fparams!=null) {
                        String[] params = fparams.split(",");
                        for(String s:params) {
                            pa.add(s);
                        }
                    }
                    this.functions.put(fname, pa);
                }
            }
            this.functionNames = this.functions.keySet();
        }

        if (allowThreads == null && VM.getVM().getConfig().get("vm.allowed.threads") != null) {
            String[] tids = VM.getVM().getConfig().get("vm.allowed.threads").toString().split(",");
            if (tids != null) {
                allowThreads = new HashSet<String>(Arrays.asList(tids));
            }

            if (threadsDepMap == null && VM.getVM().getConfig().get("vm.allowed.threads.seqdeps") != null) {
                String[] deps = VM.getVM().getConfig().get("vm.allowed.threads.seqdeps").toString().split(";");
                if (deps != null) {
                    threadsDepMap = new HashMap<>();
                    for (String s : deps) {
                        String d = s.split(":")[0];
                        String[] depList = s.split(":")[1].split(",");
                        for (String s2 : depList) {
                            if (threadsDepMap.get(s2) == null) {
                                ArrayList<String> d2 = new ArrayList();
                                d2.add(d);
                                threadsDepMap.put(s2, d2);
                            } else {
                                threadsDepMap.get(s2).add(d);
                            }
                        }

                    }
                }
            }
        }

        if (allowedPaths.size() == 0) {
            String[] allowedDepths = null;
            String[] allowedChildren = null;
            if (allowDepth == null && VM.getVM().getConfig().get("vm.parallel.allowed.depth") != null) {
                allowedDepths = VM.getVM().getConfig().get("vm.parallel.allowed.depth").toString().split(",");
                if (allowedDepths != null) {
                    allowDepth = new HashSet<String>(Arrays.asList(allowedDepths));
                }
            }
            if (allowChild == null && VM.getVM().getConfig().get("vm.parallel.allowed.child") != null) {
                allowedChildren = VM.getVM().getConfig().get("vm.parallel.allowed.child").toString().split(",\\[");
                if (allowedChildren != null) {
                    allowChild = new HashSet<String>(Arrays.asList(allowedChildren));
                }
            }

            if (allowDepth != null && allowChild != null) {

                if (allowedDepths.length == allowedChildren.length) {
                    for (int i = 0; i < allowedDepths.length; i++) {
                        String[] depthSeq = allowedDepths[i].split("-");
                        String[] childrenSeq = allowedChildren[i].replaceAll("\\[", "").replaceAll("\\]", "").split(",");

                        ArrayList<Integer> allowedChildrenArray = new ArrayList<>();
                        for (int j = 0; j < childrenSeq.length; j++) {
                            String[] childSeqRange = childrenSeq[j].split("-");
                            for (int k = Integer.parseInt(childSeqRange[0]); k <= Integer.parseInt(childSeqRange[childSeqRange.length - 1]); k++) {
                                allowedChildrenArray.add(k);
                            }
                        }
                        for (int j = Integer.parseInt(depthSeq[0]); j <= Integer.parseInt(depthSeq[depthSeq.length - 1]); j++) {
                            allowedPaths.put(j, allowedChildrenArray);
                            //        System.out.println("j " + j);
                        }
                    }
                } else {
                    System.err.println("Parameters allowed.depth and allowed.child should have the same length.");
                }
            }
        }

    }
    
    @Override
    public void methodEntered (VM vm, ThreadInfo currentThread, MethodInfo enteredMethod) {
    //    System.out.println("MMM : " + enteredMethod.getLongName());
    //    if(enteredMethod.getArgumentLocalVars()!=null)
    //    for(LocalVarInfo lvi:enteredMethod.getArgumentLocalVars())
     //       if(lvi!=null)
     //       System.out.println("ppp : " +  lvi.getName());
    }
    
    @Override
    public void instructionExecuted(VM vm, ThreadInfo ti, Instruction nextInsn, Instruction insn) {
      //  if(executedInsn instanceof LocalVariableInstruction)
      //      System.out.println("LocalVariableInstruction " + ((LocalVariableInstruction) executedInsn).getVariableId() + " linenumber " + executedInsn.getLineNumber() + " " + executedInsn.getSourceLine() + " " + executedInsn.getSourceLocation());
        
      Search search = vm.getSearch();

        id = search.getStateId();
        depth = search.getDepth();

        boolean found = current.findNode(id, depth);

    //    if (found) {

            Node newN = current;
            
         //   for(int i=0; i<newN.data.size(); i++)
         //       printData(newN.data.get(i));

            
            
            if(insn instanceof LocalVariableInstruction) {
                LocalVariableInstruction lvinsn = (LocalVariableInstruction) insn;
                        
                    LocalVarInfo vi = lvinsn.getLocalVarInfo();
                    if(vi!=null)
               //     System.out.println("vname : " + vi.getName());
                        
                 //   if (vi!=null)
                 //   System.out.println("LocalVariableInstruction2 " + vi.getName() + " linenumber " + insn.getLineNumber() + " " + insn.getSourceLine() + " " + insn.getSourceLocation());
                    if (functionNames!=null)
                   //     System.out.println("functionNames ... " + functionNames.size());
                    for(String f : functionNames) {
                        if (lvinsn.getSourceLine()!=null && lvinsn.getSourceLine().contains(f)) {
                            String func = lvinsn.getSourceLine().substring(lvinsn.getSourceLine().indexOf(f), lvinsn.getSourceLine().indexOf(")"));
                            func = func.substring(func.indexOf("(")+1);
                            String[] pars = func.split(",");
                            ArrayList<String> params = new ArrayList<>();
                            for (String p : pars) {
                                params.add(p);               
                            }
                            if (functionsMapping!=null)
                              //  System.out.println("functionsMapping ... " + functionsMapping.size());
                            functionsMapping.put(f, params);
                            break;
                        }
                    }
                    
                 //   System.out.println("4444444" + functionsMapping.get(lvinsn.getMethodInfo().getName()) + " " + lvinsn.getMethodInfo().getName() + " " + functionsMapping.keySet());
                 //   if(vi!=null && functionsMapping.get(lvinsn.getMethodInfo().getName())!=null)
                 //       System.out.println("333333" + vi.getName() + fieldNames.toString() + " " + " " + functionsMapping.get(lvinsn.getMethodInfo().getName()).get(functions.get(lvinsn.getMethodInfo().getName()).indexOf(vi.getName())));
                    if(vi!=null && (!newN.relationOfFieldsAndVarsMap.keySet().isEmpty()  && newN.relationOfFieldsAndVarsMap.containsKey(vi.getName())) || (functionsMapping.get(lvinsn.getMethodInfo().getName())!=null  &&  newN.relationOfFieldsAndVarsMap.containsKey(functionsMapping.get(lvinsn.getMethodInfo().getName()).get(functions.get(lvinsn.getMethodInfo().getName()).indexOf(vi.getName())))) || (functionsMapping.get(lvinsn.getMethodInfo().getName())!=null  &&  fieldNames.contains(functionsMapping.get(lvinsn.getMethodInfo().getName()).get(functions.get(lvinsn.getMethodInfo().getName()).indexOf(vi.getName())))) ) {
                    
                  //      System.out.println("555555" + vi.getName());
                        VariableData newD = new VariableData();

                        if(lvinsn.getSourceLine()!=null) {
                        newD.sourceLine = lvinsn.getSourceLine();
                        newD.fileLocation = lvinsn.getFileLocation();
                        newD.lineNumber = lvinsn.getLineNumber();
                        newD.methodName = lvinsn.getMethodInfo().getName();
                        newD.isSynchronized = lvinsn.getMethodInfo().isSynchronized();
                        newD.threadName = ti.getName();
                        if (!newN.threadAccessed.contains(ti.getName())) {
                            newN.threadAccessed.add(ti.getName());
                        }
                        newD.threadId = ti.getId();
                        newD.instance = insn.getMethodInfo().getClassInfo().getUniqueId();

                        

                        newD.threadName = ti.getName();
                        newD.threadId = ti.getId();
                        newD.instance = lvinsn.getMethodInfo().getClassInfo().getUniqueId();
                        newD.className = lvinsn.getMethodInfo().getClassInfo().getSimpleName();
                        newD.packageName = lvinsn.getMethodInfo().getClassInfo().getPackageName();
                        if(vi!=null)
                        newD.variableName = vi.getName();
                   //     System.out.println(vi.getName());
                        newD.value = lvinsn.getVariableId();
                        
                        if(vi!=null)
                        newD.type = vi.getType();
                        

                        if(newD.sourceLine!=null) {
                            if(newD.sourceLine.contains("=")) {
                                String part1 = newD.sourceLine.split("=")[0].trim();
                             //   System.out.println("p1 " + part1);
                                if(newD.sourceLine.split("=").length>=2) {
                                    String part2 = newD.sourceLine.split("=")[1].trim();
                                //    System.out.println("p2 " + part2);
                                    if (part2.contains(newD.variableName)) {
                                        newD.readOperation = true;
                                    }
                                    if(part1.contains(newD.variableName) && (part1.lastIndexOf(newD.variableName)+newD.variableName.length()==part1.length())) {
                                        newD.writeOperation = true;
                                        
                                        boolean fieldrel = false;
                                        for(String fld:newN.fieldVarGroups.keySet()) {
                                        //    System.out.println("fld " + fld.substring(fld.lastIndexOf(".")+1));
                                            if(part2.contains(fld.substring(fld.lastIndexOf(".")+1))) {
                                            //    System.out.println("par " + newD.sourceLine);
                                                fieldrel=true;
                                                break;
                                            }
                                        }
                                        if(!fieldrel && !newD.readOperation) {
                                            RelationOfFieldsAndVars rfvrem = null;
                                            boolean loop = true;
                                            
                                            if (newN.relationOfFieldsAndVarsMap!=null)
                           //     System.out.println("relationOfFieldsAndVarsMap ... " + newN.relationOfFieldsAndVarsMap.size());
                                            
                                            while(loop) {
                                                loop = false;
                                                for(RelationOfFieldsAndVars rfv:newN.relationOfFieldsAndVarsMap.get(vi.getName())) {
                                                    if(rfv.variableName.compareTo(vi.getName())==0 && rfv.threadName.compareTo(newD.threadName)==0) {
                                                        newN.fieldVarGroups.get(rfv.fieldName).remove(newD.threadName+"#"+newD.className+"."+newD.methodName+"."+vi.getName());
                                                        rfvrem = rfv;
                                                        loop = true;
                                                        break;
                                                    }
                                                }
                                                newN.relationOfFieldsAndVarsMap.get(vi.getName()).remove(rfvrem);
                                                rfvrem=null;
                                            }
                                            
                                        }
                                    }
                                    
                                    
                                    if(newD.readOperation && !newD.writeOperation) {
                                        if (part1.split(" ").length >= 2) {
                                            String fn = null;
                                            String var = part1.split(" ")[1].trim();
                                       //     System.out.println("var " + var);
                                            ArrayList<RelationOfFieldsAndVars> fvs = newN.relationOfFieldsAndVarsMap.get(vi.getName());
                                            for(RelationOfFieldsAndVars rfv:fvs) {
                                                if(rfv.threadName.compareTo(newD.threadName)==0) {
                                                    fn = rfv.fieldName;
                                               //     System.out.println("fn " + fn + " " + rfv.variableName + " " + rfv.sourceLine);
                                                    RelationOfFieldsAndVars nrfv = rfv.copy();
                                                    nrfv.variableName=var;
                                                    if(newN.relationOfFieldsAndVarsMap.get(var)!=null) {
                                                        newN.relationOfFieldsAndVarsMap.get(var).add(nrfv);
                                                    }else{
                                                        ArrayList<RelationOfFieldsAndVars> relArr = new ArrayList<>();
                                                        relArr.add(nrfv);
                                                //        System.out.println("nrfv.variableName " + nrfv.variableName + " " + newD.lineNumber + " " + newN.id + " " + newN.depth);
                                                        newN.relationOfFieldsAndVarsMap.put(var, relArr);
                                                    }
                                                    
                                                }
                                            }
                                            
                                            if (newN.fieldVarGroups!=null)
                        //        System.out.println("relationOfFieldsAndVarsMap ... " + newN.fieldVarGroups.size());
                                            
                                            if(newN.fieldVarGroups.get(fn)==null) {
                                                HashSet hs = new HashSet();
                                                hs.add(newD.threadName+"#"+newD.className+"."+newD.methodName+"."+var);
                                        //        System.out.println("fieldVarGroups " + fn);
                                                newN.fieldVarGroups.put(var, hs);
                                            }else {
                                       //         System.out.println("fieldVarGroups2 " + fn);
                                                newN.fieldVarGroups.get(fn).add(newD.threadName+"#"+newD.className+"."+newD.methodName+"."+var);
                                            }
                                        }
                                        
                                    }
                                }
                            }else if(newD.sourceLine.contains("++") || newD.sourceLine.contains("--")) {
                                newD.writeOperation = true;
                            }else
                                newD.readOperation = true;
                        }

                        if (newD.variableName != null) {
                            if (newN.varData.get(newD.threadName)==null) {
                                newN.varData.put(newD.threadName, new HashMap<>());
                                newN.varData.get(newD.threadName).put(newD.variableName, new ArrayList<>());
                            }else if (newN.varData.get(newD.threadName).get(newD.variableName)==null) {
                                newN.varData.get(newD.threadName).put(newD.variableName, new ArrayList<>()); 
                            }
                            newN.varData.get(newD.threadName).get(newD.variableName).add(newD);
                        //    if (newN.varData.get(newD.threadName).get(newD.variableName)!=null)
                            //    System.out.println("newN.varData.get(newD.threadName).get(newD.variableName) ... " + newN.varData.get(newD.threadName).get(newD.variableName).size());
                        }
                     //   if(vi!=null)
                     //       System.out.println("----" +  vi.getName());
                   //     printVarData(newD);
                        }
                    }else {
                        if (lvinsn.getSourceLine()!=null && lvinsn.getSourceLine().contains("lock()")) {
                            newN.threadLocks.get(ti.getName()).add(vi.getName());
                        } else if (lvinsn.getSourceLine()!=null && lvinsn.getSourceLine().contains("unlock()")) {
                            newN.threadLocks.get(ti.getName()).remove(vi.getName());
                        }
                    }
                }
        
       /* }else {
            search = vm.getSearch();

            Node newN = current;
            
         //   for(int i=0; i<newN.data.size(); i++)
         //       printData(newN.data.get(i));

            
            
            if(insn instanceof LocalVariableInstruction) {
                LocalVariableInstruction lvinsn = (LocalVariableInstruction) insn;
                        
                    LocalVarInfo vi = lvinsn.getLocalVarInfo();
                    
                    if (vi!=null)
                    System.out.println("LocalVariableInstruction2 " + vi.getName() + " linenumber " + insn.getLineNumber() + " " + insn.getSourceLine() + " " + insn.getSourceLocation());

                    if(!newN.relationOfFieldsAndVarsMap.keySet().isEmpty()  && vi!=null && newN.relationOfFieldsAndVarsMap.containsKey(vi.getName())) {
                    
                        VariableData newD = new VariableData();

                        newD.fileLocation = lvinsn.getFileLocation();
                        newD.lineNumber = lvinsn.getLineNumber();
                        newD.methodName = lvinsn.getMethodInfo().getName();
                        newD.isSynchronized = lvinsn.getMethodInfo().isSynchronized();
                        newD.threadName = ti.getName();
                        if (!newN.threadAccessed.contains(ti.getName())) {
                            newN.threadAccessed.add(ti.getName());
                        }
                        newD.threadId = ti.getId();
                        newD.instance = insn.getMethodInfo().getClassInfo().getUniqueId();

                        

                        newD.threadName = ti.getName();
                        newD.threadId = ti.getId();
                        newD.instance = lvinsn.getMethodInfo().getClassInfo().getUniqueId();
                        newD.className = lvinsn.getMethodInfo().getClassInfo().getSimpleName();
                        newD.packageName = lvinsn.getMethodInfo().getClassInfo().getPackageName();
                        if(vi!=null)
                        newD.variableName = vi.getName();
                        newD.value = lvinsn.getVariableId();
                        
                        if(vi!=null)
                        newD.type = vi.getType();
                        newD.sourceLine = lvinsn.getSourceLine();

                        if(newD.sourceLine!=null) {
                            if(newD.sourceLine.contains("=")) {
                                String part1 = newD.sourceLine.split("=")[0].trim();
                             //   System.out.println("p1 " + part1);
                                if(newD.sourceLine.split("=").length>=2) {
                                    String part2 = newD.sourceLine.split("=")[1].trim();
                                //    System.out.println("p2 " + part2);
                                    if (part2.contains(newD.variableName)) {
                                        newD.readOperation = true;
                                    }
                                    if(part1.contains(newD.variableName) && (part1.lastIndexOf(newD.variableName)+newD.variableName.length()==part1.length())) {
                                        newD.writeOperation = true;
                                        
                                        boolean fieldrel = false;
                                        for(String fld:newN.fieldVarGroups.keySet()) {
                                        //    System.out.println("fld " + fld.substring(fld.lastIndexOf(".")+1));
                                            if(part2.contains(fld.substring(fld.lastIndexOf(".")+1))) {
                                            //    System.out.println("par " + newD.sourceLine);
                                                fieldrel=true;
                                                break;
                                            }
                                        }
                                        if(!fieldrel && !newD.readOperation) {
                                            RelationOfFieldsAndVars rfvrem = null;
                                            boolean loop = true;
                                            
                                            while(loop) {
                                                loop = false;
                                                for(RelationOfFieldsAndVars rfv:newN.relationOfFieldsAndVarsMap.get(vi.getName())) {
                                                    if(rfv.variableName.compareTo(vi.getName())==0 && rfv.threadName.compareTo(newD.threadName)==0) {
                                                        newN.fieldVarGroups.get(rfv.fieldName).remove(newD.threadName+"#"+vi.getName());
                                                        rfvrem = rfv;
                                                        loop = true;
                                                        break;
                                                    }
                                                }
                                                newN.relationOfFieldsAndVarsMap.get(vi.getName()).remove(rfvrem);
                                                rfvrem=null;
                                            }
                                            
                                        }
                                    }
                                    
                                    if(newD.readOperation && !newD.writeOperation) {
                                        if (part1.split(" ").length >= 2) {
                                            String fn = null;
                                            String var = part1.split(" ")[1].trim();
                                            System.out.println("var " + var);
                                            ArrayList<RelationOfFieldsAndVars> fvs = newN.relationOfFieldsAndVarsMap.get(vi.getName());
                                            for(RelationOfFieldsAndVars rfv:fvs) {
                                                if(rfv.threadName.compareTo(newD.threadName)==0) {
                                                    fn = rfv.fieldName;
                                                    System.out.println("fn " + fn + " " + rfv.variableName + " " + rfv.sourceLine);
                                                    RelationOfFieldsAndVars nrfv = rfv.copy();
                                                    nrfv.variableName=var;
                                                    if(newN.relationOfFieldsAndVarsMap.get(var)!=null) {
                                                        newN.relationOfFieldsAndVarsMap.get(var).add(nrfv);
                                                    }else{
                                                        ArrayList<RelationOfFieldsAndVars> relArr = new ArrayList<>();
                                                        relArr.add(nrfv);
                                                        System.out.println("nrfv.variableName " + nrfv.variableName + " " + newD.lineNumber + " " + newN.id + " " + newN.depth);
                                                        newN.relationOfFieldsAndVarsMap.put(var, relArr);
                                                    }
                                                    
                                                }
                                            }
                                            
                                            if(newN.fieldVarGroups.get(fn)==null) {
                                                HashSet hs = new HashSet();
                                                hs.add(newD.threadName+"#"+var);
                                                System.out.println("fieldVarGroups " + fn);
                                                newN.fieldVarGroups.put(var, hs);
                                            }else {
                                                System.out.println("fieldVarGroups2 " + fn);
                                                newN.fieldVarGroups.get(fn).add(newD.threadName+"#"+var);
                                            }
                                        }
                                        
                                    }
                                }
                            }else if(newD.sourceLine.contains("++") || newD.sourceLine.contains("--")) {
                                newD.writeOperation = true;
                            }else
                                newD.readOperation = true;
                        }

                        if (newD.variableName != null) {
                            if (newN.varData.get(newD.threadName)==null) {
                                newN.varData.put(newD.threadName, new HashMap<>());
                                newN.varData.get(newD.threadName).put(newD.variableName, new ArrayList<>());
                            }else if (newN.varData.get(newD.threadName).get(newD.variableName)==null) {
                                newN.varData.get(newD.threadName).put(newD.variableName, new ArrayList<>()); 
                            }
                            newN.varData.get(newD.threadName).get(newD.variableName).add(newD);
                        }
                    }else {
                        if (lvinsn.getSourceLine()!=null && lvinsn.getSourceLine().contains("lock()")) {
                            newN.threadLocks.get(ti.getName()).add(vi.getName());
                        } else if (lvinsn.getSourceLine()!=null && lvinsn.getSourceLine().contains("unlock()")) {
                            newN.threadLocks.get(ti.getName()).remove(vi.getName());
                        }
                    }
                }
        
        }*/
        
    //    if(insn instanceof Method) {
    //        
    //    }
    }

    @Override
    public synchronized void choiceGeneratorSet(VM vm, ChoiceGenerator<?> cg) {
        Search search = vm.getSearch();

        id = search.getStateId();
        depth = search.getDepth();

        boolean found = current.findNode(id, depth);

        if (!found) {

            Node newN = new Node();
            newN.parent = current;

            newN.depth = depth;
            newN.id = id;
            newN.threadAccessed = (ArrayList<String>) current.threadAccessed.clone();
            newN.getParentThreadLocks();
            newN.getFieldVarGroups();
            newN.getRelationOfFieldsAndVarsMap();

            if(current!=null) {
                newN.objectCount = current.objectCount; 
                newN.objectPerThreadCount = DeepClone.deepClone(current.objectPerThreadCount);
            }
        
            if (cg instanceof ThreadChoiceFromSet) {

                ThreadInfo[] threads = ((ThreadChoiceFromSet) cg).getAllThreadChoices();
                for (int i = 0; i < threads.length; i++) {
                    ThreadInfo ti = threads[i];
                    if (!ti.hasChanged() && (threadsDepMap == null || threadsDepMap.get(search.getVM().getCurrentThread().getName()) == null)) {
                        continue;
                    }
                    if (allowThreads != null && !allowThreads.contains(ti.getName()) && (threadsDepMap == null || threadsDepMap.get(search.getVM().getCurrentThread().getName()) == null)) {
                        continue;
                    }

                    if (allowDepth != null && allowChild != null && allowedPaths.size() != 0) {
                        if (allowedPaths.containsKey(depth)) {
                            //       System.out.println("allowDepth " + allowedPaths.containsKey(depth) + " " + depth + " " + current.children.size() + " " + allowedPaths.get(depth).contains(current.children.size()) + " " + id + " " + ti.getName());
                            if (!allowedPaths.get(depth).contains(current.children.size())) {
                                ti.breakTransition(true);

                                continue;
                            }

                        }
                    }

                    Instruction insn = ti.getPC();
                    
                    if(!newN.threadLocks.containsKey(ti.getName())) {
                        newN.threadLocks.put(ti.getName(), new HashSet<>());
                    }

               /*     if (insn instanceof MONITORENTER) {
                        Data newD = new Data();
                        newD.locks = newN.getParentLockInfo(ti.getName(), current);
                        newD.lockRemovals = parentLockRemovals;
                        System.out.println("====MONITORENTER " + insn.getLineNumber() + " " + insn.getMethodInfo().getClassName());
                        newD.fileLocation = insn.getFileLocation();
                        newD.lineNumber = insn.getLineNumber();
                        newD.methodName = insn.getMethodInfo().getName();
                        newD.className = insn.getMethodInfo().getClassName();
                        newD.packageName = insn.getMethodInfo().getClassInfo().getPackageName();
                        newD.isSynchronized = insn.getMethodInfo().isSynchronized();
                        newD.threadName = ti.getName();
                        if (!newN.threadAccessed.contains(ti.getName())) {
                            newN.threadAccessed.add(ti.getName());
                        }
                        newD.threadId = ti.getId();
                        newD.instance = insn.getMethodInfo().getClassInfo().getUniqueId();

                        MONITORENTER mentsinsn = (MONITORENTER) insn;
                        newD.isMonitorEnter = true;
                        newD.lockRef = mentsinsn.getLastLockRef();
                        newD.sourceLine = mentsinsn.getSourceLine();

                        newN.addThreadLock(newD, newD.threadName, newD.lockRef);
                        if (fieldNames != null) {
                            newN.data.add(newD);
                        }
                    }

                    if (insn instanceof MONITOREXIT) {
                        Data newD = new Data();
                        newD.locks = newN.getParentLockInfo(ti.getName(), current);
                        newD.lockRemovals = parentLockRemovals;

                        newD.fileLocation = insn.getFileLocation();
                        newD.lineNumber = insn.getLineNumber();
                        newD.methodName = insn.getMethodInfo().getName();
                        newD.className = insn.getMethodInfo().getClassName();
                        newD.packageName = insn.getMethodInfo().getClassInfo().getPackageName();
                        newD.isSynchronized = insn.getMethodInfo().isSynchronized();
                        newD.threadName = ti.getName();
                        if (!newN.threadAccessed.contains(ti.getName())) {
                            newN.threadAccessed.add(ti.getName());
                        }
                        newD.threadId = ti.getId();
                        newD.instance = insn.getMethodInfo().getClassInfo().getUniqueId();

                        MONITOREXIT mexinsn = (MONITOREXIT) insn;
                        newD.isMonitorExit = true;
                        newD.lockRef = mexinsn.getLastLockRef();
                        newD.sourceLine = mexinsn.getSourceLine();

                        newN.removeThreadLock(newD, newD.threadName, newD.lockRef);
                        if (fieldNames != null) {
                            newN.data.add(newD);
                        }
                    }
*/
                 //   if (insn instanceof InvokeInstruction) {
                //        System.out.println("!!!!!!!!!!! InvokeInstruction : " + ((InvokeInstruction) insn).getInvokedMethodName());
                //    }
                    //    if (insn instanceof ReadOrWriteInstruction) {
                    //     System.out.println("ReadOrWriteInstruction " + id);
                    //     }
                if (insn instanceof FieldInstruction) { // Ok, its a get/putfield
                    FieldInstruction finsn = (FieldInstruction) insn;
                       
               //     if(finsn.getSourceLine()!=null) {
                        Data newD = new Data();
                 //       newD.locks = newN.getParentLockInfo(ti.getName(), current);
                 //       newD.lockRemovals = parentLockRemovals;

                        newD.fileLocation = insn.getFileLocation();
                        newD.lineNumber = insn.getLineNumber();
                        newD.methodName = insn.getMethodInfo().getName();
                        newD.isSynchronized = insn.getMethodInfo().isSynchronized();
                        newD.threadName = ti.getName();
                    //    if (!newN.threadAccessed.contains(ti.getName())) {
                    //        newN.threadAccessed.add(ti.getName());
                     //   }
                        newD.threadId = ti.getId();
                        newD.instance = insn.getMethodInfo().getClassInfo().getUniqueId();
                
                        if(current!=null) {
                            newN.objectCount = current.objectCount + 1; 
                        }
                        if(newN.objectPerThreadCount.get(newD.threadName)==null){
                            newN.objectPerThreadCount.put(newD.threadName, 1);
                        }else {
                            newN.objectPerThreadCount.put(newD.threadName, newN.objectPerThreadCount.get(newD.threadName)+1);
                        }
                        
                        

                        if (finsn.isRead()) {
                            newD.readOperation = true;
                        } else {
                            newD.writeOperation = true;
                        }
                        FieldInfo fi = finsn.getFieldInfo();

                        newD.fieldName = fi.getFullName();
                        System.out.println("===="+fi.getFullName());
                        newD.threadName = ti.getName();
                        newD.threadId = ti.getId();
                        newD.instance = insn.getMethodInfo().getClassInfo().getUniqueId();
                        newD.className = fi.getClassInfo().getSimpleName();
                        newD.packageName = fi.getClassInfo().getPackageName();
                        if (fieldNames != null) {
                            String name = fi.getFullName();
                            if (name.contains(".")) {
                                name = name.substring(name.lastIndexOf(".") + 1);
                            }
                            
                            fieldNames.add(name);
                        //    System.out.println("wwwwww" + fieldNames.toString());
                            if (fieldNames.contains(name)) {
                                newD.fieldName = fi.getFullName();
                            } else {
                                newD.fieldName = null;
                            }
                        } else {
                            newD.fieldName = fi.getFullName();
                        }
                        newD.value = String.valueOf(finsn.getLastValue());
                        newD.type = finsn.getFieldInfo().getType();
                        newD.sourceLine = finsn.getSourceLine();
                        
                        if(newD.readOperation) {
                         //   System.out.println("readOperation2 : " + newD.readOperation);
                            if(newD.sourceLine!=null) {
                            //    System.out.println("newD.sourceLine : " + newD.sourceLine);
                                String part1 = newD.sourceLine.split("=")[0].trim();
                                if (newD.sourceLine.split("=").length >= 2) {
                                    String var = null;
                                    RelationOfFieldsAndVars rel = new RelationOfFieldsAndVars();
                                    if (part1.split(" ").length >= 2) {
                                        var = part1.split(" ")[1].trim();
                                        rel.variableName=var;
                                        rel.type=part1.split(" ")[0].trim();
                                     //   System.out.println("var2 : " + var);
                                    } else {
                                        var = part1.trim();
                                        rel.variableName=var;
                                    //    System.out.println("var2 : " + var);
                                    }
                                    rel.fieldName=newD.fieldName;
                                    rel.className=newD.className;
                                    rel.methodName=newD.methodName;
                                    rel.packageName=newD.packageName;
                                    rel.threadName=newD.threadName;
                                    rel.sourceLine=newD.sourceLine;
                                    rel.lineNumber=newD.lineNumber;
                                                         //   System.out.println("LocalVariableInstruction3 " + ((LocalVariableInstruction) insn).getVariableId() + " linenumber " + insn.getLineNumber() + " " + insn.getSourceLine() + " " + insn.getSourceLocation());

                                    if(newN.relationOfFieldsAndVarsMap.get(var)==null) {
                                    //    System.out.println("var3 : " + var);
                                        ArrayList<RelationOfFieldsAndVars> relArr = new ArrayList<>();
                                        relArr.add(rel);
                                        newN.relationOfFieldsAndVarsMap.put(var, relArr);
                                    } else {
                                    //    System.out.println("var3 : " + var);
                                        newN.relationOfFieldsAndVarsMap.get(var).add(rel);
                                    }
                                    
                                    if(newN.fieldVarGroups.get(newD.fieldName)==null) {
                                        HashSet hs = new HashSet();
                                        hs.add(newD.threadName+"#"+newD.className+"."+newD.methodName+"."+var);
                                        newN.fieldVarGroups.put(newD.fieldName, hs);
                                    }else {
                                        newN.fieldVarGroups.get(newD.fieldName).add(newD.threadName+"#"+newD.className+"."+newD.methodName+"."+var);
                                    }
                                }    
                                
                            }
                        }

                    //    if (newD.fieldName != null && newD.fieldName.compareTo("gr.uop.gr.javamethodsjpf.ReentrantLock.num") == 0 && newD.writeOperation) {
                            if (newD.sourceLine!=null && newD.sourceLine.contains("lock()")) {
                             //   newN.addThreadLock(newD, newD.threadName, newD.instance);
                                //    System.out.println("-------- : " + newD.instance);
                                newN.threadLocks.get(ti.getName()).add(newD.fieldName);
                            } else if (newD.sourceLine!=null && newD.sourceLine.contains("unlock()")) {
                             /*   if (newN.removeThreadLock(newD, newD.threadName, newD.instance)) {
                                    if (newD.lockRemovals.get(newD.instance) != null) {
                                        newD.lockRemovals.put(newD.instance, (int) newD.lockRemovals.get(newD.instance) + 1);
                                    } else {
                                        newD.lockRemovals.put(newD.instance, 1);
                                    }
                                }*/
                                newN.threadLocks.get(ti.getName()).remove(newD.fieldName);

                            }
                   //     }
                        if (newD.fieldName != null) {
                            newN.data.add(newD);
                        //    printData(newD);
                        }
               //     }
                }
                    
                /*    if(insn instanceof LocalVariableInstruction) {
                        System.out.println("LocalVariableInstruction " + ((LocalVariableInstruction) insn).getVariableId() + " linenumber " + insn.getLineNumber() + " " + insn.getSourceLine() + " " + insn.getSourceLocation());
                    
                        Data newD = new Data();
                        newD.locks = newN.getParentLockInfo(ti.getName(), current);
                        newD.lockRemovals = parentLockRemovals;

                        newD.fileLocation = insn.getFileLocation();
                        newD.lineNumber = insn.getLineNumber();
                        newD.methodName = insn.getMethodInfo().getName();
                        newD.isSynchronized = insn.getMethodInfo().isSynchronized();
                        newD.threadName = ti.getName();
                        if (!newN.threadAccessed.contains(ti.getName())) {
                            newN.threadAccessed.add(ti.getName());
                        }
                        newD.threadId = ti.getId();
                        newD.instance = insn.getMethodInfo().getClassInfo().getUniqueId();

                        LocalVariableInstruction lvinsn = (LocalVariableInstruction) insn;

                        
                        LocalVarInfo vi = lvinsn.getLocalVarInfo();

                        newD.threadName = ti.getName();
                        newD.threadId = ti.getId();
                        newD.instance = insn.getMethodInfo().getClassInfo().getUniqueId();
                        newD.className = insn.getMethodInfo().getClassInfo().getSimpleName();
                        newD.packageName = insn.getMethodInfo().getClassInfo().getPackageName();
                        newD.variableName = vi.getName();
                        newD.isVar = true;
                        newD.value = lvinsn.getVariableId();
                        
                        newD.type = vi.getType();
                        newD.sourceLine = insn.getSourceLine();

                        String part1 = newD.sourceLine.split("=")[0].trim();
                        String part2 = newD.sourceLine.split("=")[1].trim();
                        if (part2.contains(newD.variableName)) {
                            newD.readOperation = true;
                        } else if(part1.contains(newD.variableName)) {
                            newD.writeOperation = true;
                        }

                        if (newD.variableName != null) {
                            newN.data.add(newD);
                        }
                    }*/

                }
                if (newN.data != null && newN.data.size() != 0) {
                    current.children.add(newN);
                    current = newN;
               //     statesIncluded.add(cg.getStateId());
                /*    String nodeMap = newN.data.get(0).threadName + " " + newN.data.get(0).fieldName;
                    stateGroupMap2.put(cg.getStateId(), nodeMap);
                    if (!stateGroupMap.containsKey(nodeMap)) {
                        stateGroupMap.put(nodeMap, cg.getStateId());
                        stateGroups.put(cg.getStateId(), cg.getStateId());
                    } else {
                        if (!stateGroups.containsKey(cg.getStateId())) {
                            int keyNode = stateGroupMap.get(nodeMap);
                            stateGroups.put(cg.getStateId(), keyNode);
                        }
                    }
                    nodesIncluded.put(cg.getStateId(), newN);*/
                } else {
                    current.children.add(newN);
                    current = newN;
               //     statesExcluded.add(cg.getStateId());
                }
            }

            previousId = id;
        }
    }

    //--- the ones we are interested in
    @Override
    public synchronized void searchStarted(Search search) {
        System.out.println("----------------------------------- search started");
    }

    @Override
    public synchronized void stateAdvanced(Search search) {

     //   synchronized (this) {
            /*        ChoiceGenerator<?> cg = search.getVM().getChoiceGenerator();
            boolean ignore = false;
            System.out.println("0");
            if (cg instanceof ThreadChoiceFromSet) {
                ThreadInfo[] threads = ((ThreadChoiceFromSet) cg).getAllThreadChoices();
                for (int i = 0; i < threads.length; i++) {
                    ThreadInfo ti = threads[i];
                 //   if (!ti.hasChanged() && (threadsDepMap == null || threadsDepMap.get(search.getVM().getCurrentThread().getName()) == null)) {
                //       continue;
                 //   }
                    Instruction insn = ti.getPC();
System.out.println("1");
                    if(insn instanceof FieldInstruction) {
System.out.println("2");
                            FieldInstruction finsn = (FieldInstruction) insn;
                            FieldInfo fi = finsn.getFieldInfo();
                            if(fieldNames!=null) {
                                String name = fi.getFullName();
                            if(name.contains(".")) 
                                name=name.substring(name.lastIndexOf(".")+1);
                            if(fieldNames.contains(name)) {
                                System.out.println("3");
                                ignore = false;
                            }else{
                                System.out.println("4");
                                ignore = true;
                                }
                        }
                    }
                }
                if(ignore)
            search.getVM().ignoreState();
            }
            
             */
        //    statesHistory.add(search.getVM().getStateId());
        //    statesAction.add("advanced " + search.getVM().isEndState());
         //   System.out.println("0 " + search.getVM().isEndState());
   //     }

        if (allowThreads != null) {
            if (!allowThreads.contains(search.getVM().getCurrentThread().getName()) && (threadsDepMap == null || threadsDepMap.get(search.getVM().getCurrentThread().getName()) == null)) {

                search.getVM().ignoreState();
            } else if (!allowThreads.contains(search.getVM().getCurrentThread().getName())) {
                if (threadsDepMap != null && threadsDepMap.get(search.getVM().getCurrentThread().getName()) != null) {
                    current.findNode(search.getStateId(), search.getDepth());
                    boolean canBeTerminated = true;
                    for (String t : threadsDepMap.get(search.getVM().getCurrentThread().getName())) {
                        //        System.out.println("t " + t);
                        if (!current.threadAccessed.contains(t)) {
                            canBeTerminated = false;
                            break;
                        }
                    }
                    if (canBeTerminated) {
                        search.getVM().ignoreState();

                    }
                }
            }
        }
    }

    @Override
    public synchronized void stateBacktracked(Search search) {
        synchronized (this) {
        //    statesHistory.add(search.getVM().getStateId());
        //    statesAction.add("backtracked " + search.getVM().isEndState());
        }

    }

    int rootId = -100;

    @Override
    public synchronized void searchFinished(Search search) {
        System.out.println("----------------------------------- search finished");

        //    root = null;
        //    current = null;
   /*     rootNode.stateId = 0;
        stateMap.put(0, rootNode);
        HashMap<Integer, HashMap<Integer, Boolean>> stateGraph = new HashMap();
        HashMap<Integer, Boolean> isUsed = new HashMap<>();

        HashMap<Integer, Boolean> isRootParent = new HashMap<>();
        HashMap<Integer, ArrayList<Integer>> reUsed = new HashMap<>();

        int parentId = -100;

        int x = 0;
        System.out.println("************* " + statesHistory.size());
        for (int state : statesHistory) {
         //   System.out.println("state : " + state + " parentId : " + parentId);
            String action = statesAction.get(x);

            if (state >= 0) {
                if (action.contains("advanced") && state
                        > parentId) {
                    if (stateGraph.get(state) == null) {
                        stateGraph.put(state,
                                new HashMap<>());
                    }

                    if (parentId >= 0) {
                        stateGraph.get(parentId).put(state,
                                statesIncluded.contains(state));
                        isRootParent.put(state,
                                Boolean.FALSE);
                    } else {
                        isRootParent.put(state, Boolean.TRUE);
                        rootId = parentId;
                    //    System.out.println("rootId " + rootId);
                    }

                    if (statesIncluded.contains(state)) {
                        isUsed.put(state,
                                Boolean.TRUE);
                    } else {
                        isUsed.put(state, Boolean.FALSE);
                    }

                    if (action.contains("true")) {
                        isEndState.put(state, Boolean.TRUE);
                        endNodes = endNodes + 1;
                    } else {
                        isEndState.put(state, Boolean.FALSE);
                    }

                    parentId = state;

                } else if (action.contains("advanced") && state <= parentId) {
                    if (reUsed.get(state) == null) {
                        reUsed.put(state, new ArrayList<>());
                    }
                    reUsed.get(state).add(parentId);

                    if (statesIncluded.contains(state)
                            && !statesIncluded.contains(parentId)) {
                        for (int k
                                : stateGraph.get(state).keySet()) {
                            if (!stateGraph.get(parentId).keySet().contains(k)) {
                                stateGraph.get(parentId).put(k, stateGraph.get(state).get(k));
                            }
                        }
                     //   System.out.println("state matching 1");
                    } else if (!statesIncluded.contains(state)
                            && statesIncluded.contains(parentId)) {
                        stateGraph.get(parentId).put(state, statesIncluded.contains(state));
                    //    System.out.println("state matching 2");
                    } else {

                        for (int k : stateGraph.get(state).keySet()) {
                            if (!stateGraph.get(parentId).keySet().contains(k)) {
                                stateGraph.get(parentId).put(k, stateGraph.get(state).get(k));
                            }
                        }
                    }

                 //   System.out.println("state matching : " + parentId + " " + state);
                    parentId = state;

                }

                if (action.contains("backtracked")) {
                //    System.out.println("backtrack... ");

                    parentId = state;

                }

            }
            x++;
        }

        HashMap<Integer, HashMap<Integer, Boolean>> stateGraph2 = new HashMap();
        stateGraph2 = stateGraph;
*/
        /*     for (Integer key : stateGraph2.keySet()) {
            if(!isEndState.get(key)){
                for (Integer key2 : stateGraph2.get(key).keySet()) {
                    if(key==key2){
                        stateGraph2.get(key).remove(key2);
                        stateGraph2.get(key).putAll(stateGraph2.get(key));
                    }
                }
            }
        }*/
        // for (Integer key : stateGraph2.keySet()) {
        //   if(!statesIncluded.contains(key) && key!=0)
        //      stateGraph2.remove(key);
        //   System.out.println("kkk " + stateGraph2.get(key).keySet().toString());
        //  }
        /*
        ArrayList<ArrayList<Integer>> paths = new ArrayList(); for (Integer
        key : stateGraph2.keySet()) { if(isRootParent.get(key)) {
        ArrayList<Integer> path = new ArrayList(); if(isUsed.get(key))
        path.add(key); calculatePaths(stateGraph2,path,paths,key,isUsed); } }
         
        System.out.println("firstElements " + firstElements.toString());
        
        SubSet rootSet = new SubSet();
        rootSet.childElements.addAll(firstElements); //
        rootSet.classify(stateGraph2, stateGroupMap2); SubSet set = rootSet;
        createSubSets(set,stateGraph2, stateGroupMap2);
         
         */
        /*
        ArrayList<ArrayList<Node>> nodePaths = new ArrayList();
        int ss = paths.size();
        System.out.println("ss : " + ss);
        for (int n=0; n < ss; n++) {
            ArrayList<Integer> pathI = paths.get(n);
            
                
                    ArrayList<Node> nodePath = new ArrayList<>();
                    for(int i=0; i<pathI.size(); i++) {
                        nodePath.add(nodesIncluded.get(pathI.get(i)));
                    }
                    
                    int snp = nodePaths.size();
                    boolean exclude = false;
                    for(int m=0; m<snp; m++) {
                        if(!exclude && nodePaths.get(m).size()==nodePath.size()) {
                            int nps = nodePath.size();
                            int exclNum = 0;
                            for(int nn=0; nn<nps; nn++) {
                                if(nodePaths.get(m).get(nn).data.get(0).threadName.compareTo(nodePath.get(nn).data.get(0).threadName)==0 &&
                                   nodePaths.get(m).get(nn).data.get(0).fieldName.compareTo(nodePath.get(nn).data.get(0).fieldName)==0 ){
                                   exclNum++;
                                }
                                if(exclNum==nps) {
                                   exclude = true;
                                   break;
                                }
                            }
                            
                        }
                    }
                    
                    if(!exclude) {
                        nodePaths.add(nodePath);
                    }

            
        }
        
        System.out.println("@@@@@@ Paths Size : " + paths.size() + " " + nodePaths.size());
        
  
        int snp = nodePaths.size();
        for(int m=0; m<snp; m++) {
            int nps = nodePaths.get(m).size();
            for(int nn=0; nn<nps; nn++) {
                System.out.print(nodePaths.get(m).get(nn).data.get(0).threadName + "," + nodePaths.get(m).get(nn).data.get(0).fieldName + " ");
            }
            System.out.println();
        }

         */
 /*       System.out.println("used vs unused : " + stateMap.size() + " "
                + statesExcluded.size());

        rootNode.depth = 0;

        System.out.println(rootNode.stateId + " root children : "
                + rootNode.children.size());

        System.out.println("End Node Num : " + endNodes);

        rootNode.currentSubpathNodes = 0;

        System.out.println("Path Num : " + finalSequences.size());
*/
 System.out.println("Search finished ....");
        try {
            MongoClient mongoClient = new MongoClient(new MongoClientURI("mongodb://localhost:27017"));
            DB database = mongoClient.getDB("jpf");
            collection = database.getCollection("jpfdata"); 
       //     File fout = new File("out.txt");
       //     FileOutputStream fos = new FileOutputStream(fout);

      //      bw = new BufferedWriter(new OutputStreamWriter(fos));
            
            printTree(root);
            Thread.sleep(10000);
            
      //      bw.close();
            //      printGraph();

            //       checkFieldRule(root,new HashMap<String,FieldState>());
            checkFieldRule2(root, new HashMap<String, HashMap<String, FieldState>>());

            System.out.println(errors.toString());
//
//

        } catch (Exception ex) {
            Logger.getLogger(MyListener.class.getName()).log(Level.SEVERE, null, ex);
        }

    }

    private void createSubSets(SubSet set, HashMap<Integer, HashMap<Integer, Boolean>> stateGraph2, HashMap<Integer, String> stateGroupMap2) {
        set.classify(stateGraph2, stateGroupMap2);
        if (set.children.keySet().size() != 0) {
            for (String key : set.children.keySet()) {
                //   if(key!=null) {
                //    System.out.println("kkk " + key);
                SubSet set2 = set.children.get(key);
                createSubSets(set2, stateGraph2, stateGroupMap2);
                set2.childElements.clear();
                set2.children.clear();
                set2.childrenStateGroups.clear();
                set2.elements.clear();
                set2.groups.clear();
                set2 = null;
                //   }else{
                //    System.out.println("seq : " + set.allGroups);
                //   }
            }
        } else {
            //    System.out.println("seq : " + set.allGroups);
        }
    }

    private HashSet<Integer> calculatePaths(HashMap<Integer, HashMap<Integer, Boolean>> stateGraph2, ArrayList<Integer> path, ArrayList<ArrayList<Integer>> paths, int key, HashMap<Integer, Boolean> isUsed) {

        /*    ArrayList<Integer> path2 = new ArrayList();
        for(int x : path){
            path2.add(x);
        }
        
         */
        HashMap<Integer, Boolean> neighbours = stateGraph2.get(key);

        if (!neighbours.keySet().isEmpty()) {
            for (int x : neighbours.keySet()) {
                //     if(!statesIncluded.contains(x) || x==stateGroups.get(x)){
                //   System.out.println("x " + x);
                if (isUsed.get(x)) {
                    firstElements.add(x);
                } else {
                    calculatePaths(stateGraph2, null, paths, x, isUsed);
                }
                /*       path2.add(x);
                    if(!isEndState.get(x)) {
                        calculatePaths(stateGraph2,path2,paths,x);

                        path2.remove(path2.get(path2.size()-1));
                    }else if(isEndState.get(x)){
                        int s = path2.size();

                        for(int ii = 0; ii < s; ii++ ) {
                                int value = path2.get(ii);
                                if(!statesIncluded.contains(value)) {
                                    path2.remove(ii);
                                    ii--;
                                    s--;

                                }else{
                                    int node = path2.remove(ii);
                                    path2.add(ii, stateGroups.get(node));

                                }
                            }

                        s = path2.size();

                            boolean exists = false;
                            for(int m=0; m<paths.size(); m++) {
                                if(paths.get(m).equals(path2)) {
                                    exists=true;
                                    break;
                                }
                            }
                            if(!exists && path2.size()!=0) {
                                paths.add(path2);
                            }

                    }*/
            }
            //   }
        }

        return firstElements;
    }
    
    public DBObject toDBObject(Node myNode, Data d) {
       
        BasicDBObject bo = new BasicDBObject();  
        
        bo.append("objectCount",myNode.objectCount);
        
        bo.append("objectPerThreadCountKeys", Arrays.toString(myNode.objectPerThreadCount.keySet().toArray()));
        for(String k : myNode.objectPerThreadCount.keySet())
            bo.append(k, myNode.objectPerThreadCount.get(k));
        
        bo.append("id", myNode.id)
                     .append("previousId", myNode.previousid)
                     .append("depth", myNode.depth)
                     .append("data", new BasicDBObject("fieldName", d.fieldName)
                                                  .append("lineNumber", d.lineNumber)
                                                  .append("methodName", d.methodName)
                                                  .append("className", d.className)
                                                  .append("packageName", d.packageName)
                                                  .append("readOperation", d.readOperation)
                                                  .append("writeOperation", d.writeOperation)
                                                  .append("sourceLine", d.sourceLine)
                                                  .append("threadId", d.threadId)
                                                  .append("threadName", d.threadName)
                                                  .append("value", d.value));
                     
        
        if(myNode.fieldVarGroups.get(d.fieldName)!=null) {
            bo.append("fieldVarGroups", Arrays.toString(myNode.fieldVarGroups.get(d.fieldName).toArray()));
        }
        
        if(d.fieldName!=null && myNode.relationOfFieldsAndVarsMap!=null && myNode.relationOfFieldsAndVarsMap.get(d.fieldName)!=null) {  
                                    int i=0;
                                    for(RelationOfFieldsAndVars rofv:myNode.relationOfFieldsAndVarsMap.get(d.fieldName)) {
                                        bo.append("relationOfFieldsAndVarsMap" + i, new BasicDBObject("fieldName", rofv.fieldName)
                                                  .append("lineNumber", rofv.lineNumber)
                                                  .append("methodName", rofv.methodName)
                                                  .append("className", rofv.className)
                                                  .append("packageName", rofv.packageName)
                                                  .append("sourceLine", rofv.sourceLine)
                                                  .append("threadName", rofv.threadName));
                                        i++;
                                    }
                                
                            }
             
            HashMap<String,ArrayList<VariableData>> vdt = myNode.varData.get(d.threadName);
            
            if(vdt!=null) {
                for(String vdv : vdt.keySet()) {
                    if(vdt.get(vdv)!=null) {
                        for(VariableData vd:vdt.get(vdv)) {  
                            if(vd!=null) {
                                bo.append("variableData"+vd.hashCode(), new BasicDBObject("variableName", vd.variableName)
                                                  .append("lineNumber", vd.lineNumber)
                                                  .append("methodName", vd.methodName)
                                                  .append("className", vd.className)
                                                  .append("packageName", vd.packageName)
                                                  .append("readOperation", vd.readOperation)
                                                  .append("writeOperation", vd.writeOperation)
                                                  .append("sourceLine", vd.sourceLine)
                                                  .append("threadId", vd.threadId)
                                                  .append("threadName", vd.threadName)
                                                  .append("value", vd.value));
                            }

                                
                        }
                    }
                }
            }
            
            if(myNode.prevDBObject!=null) {
        //        bo.append("prevDBObject",myNode.prevDBObject);
            }
                    
        return bo;
    }
   
    public void printTree(Node myNode)  {
        try {
        List<Data> ld = myNode.data;

     //   String store="";
        
        System.out.println();
        System.out.print("id : " + myNode.id);
 //       store += "id : " + myNode.id;
        System.out.print(" depth : " + myNode.depth);
 //       store += " depth : " + myNode.depth;

        for (Data d : ld) {
            if(d.fieldName!=null) {

            System.out.print(" fieldName : " + d.fieldName);
   //         store += " fieldName : " + d.fieldName;
            System.out.print(" lineNumber : " + d.lineNumber);
  //          store += " lineNumber : " + d.lineNumber;
            System.out.print(" methodName : " + d.methodName);
   //         store += " methodName : " + d.methodName;
            System.out.print(" className : " + d.className);
    //        store += " className : " + d.className;
            System.out.print(" instance : " + d.instance);
   //         store += " instance : " + d.instance;
            System.out.print(" writeOperation : " + d.writeOperation);
    //        store += " writeOperation : " + d.writeOperation;
            System.out.print(" readOperation : " + d.readOperation);
    //        store += " readOperation : " + d.readOperation;
            System.out.print(" threadName : " + d.threadName);
    //        store += " threadName : " + d.threadName;
            System.out.print(" isSynchronized : " + d.isSynchronized);
    //        store += " isSynchronized : " + d.isSynchronized;
            System.out.print(" packageName : " + d.packageName);
     //       store += " packageName : " + d.packageName;
            System.out.print(" fileLocation : " + d.fileLocation);
     //       store += " fileLocation : " + d.fileLocation;
            System.out.print(" isMonitorEnter : " + d.isMonitorEnter);
     //       store += " isMonitorEnter : " + d.isMonitorEnter;
            System.out.print(" isMonitorExit : " + d.isMonitorExit);
     //       store += " isMonitorExit : " + d.isMonitorExit;
            System.out.print(" lockRef : " + d.lockRef);
     //       store += " lockRef : " + d.lockRef;
            System.out.print(" value : " + d.value);
     //       store += " value : " + d.value;
            System.out.print(" type : " + d.type);
     //       store += " type : " + d.type;
            System.out.print(" sourceLine : " + d.sourceLine);
    //        store += " sourceLine : " + d.sourceLine;
            System.out.print(" threadLocks : " + Arrays.toString(myNode.threadLocks.get(d.threadName).toArray()));
    //        store += " threadLocks : " + Arrays.toString(myNode.threadLocks.get(d.threadName).toArray());
            if(myNode.fieldVarGroups.get(d.fieldName)!=null) {
                System.out.print(" fieldVarGroups : " + Arrays.toString(myNode.fieldVarGroups.get(d.fieldName).toArray()));
    //            store += " fieldVarGroups : " + Arrays.toString(myNode.fieldVarGroups.get(d.fieldName).toArray());
            }
            
            HashMap<String,ArrayList<VariableData>> vdt = myNode.parent.varData.get(d.threadName);
            HashSet<String> rvars = new HashSet();
            if(vdt!=null) {
                for(String vdv : vdt.keySet()) {
                    for(VariableData vd:vdt.get(vdv)) {  
                        if(d.lineNumber==vd.lineNumber) {
                            rvars.add(vd.variableName);
                        }
                    }
                }
            }
            for(String vd : myNode.relationOfFieldsAndVarsMap.keySet())
            if(rvars.contains(vd) && myNode.relationOfFieldsAndVarsMap.get(vd)!=null) {  
                                    System.out.print(" 111111111 : " + vd + " " + myNode.relationOfFieldsAndVarsMap.get(vd).size());
                                    ArrayList<RelationOfFieldsAndVars> rvs = null;
                                    if(myNode.relationOfFieldsAndVarsMap.get(d.fieldName)==null)
                                        rvs = new ArrayList<>();
                                    else
                                        rvs = myNode.relationOfFieldsAndVarsMap.get(d.fieldName);
                                    
                                    for(RelationOfFieldsAndVars rofv:myNode.relationOfFieldsAndVarsMap.get(vd)) {
                                       rvs.add(rofv);
                                        System.out.print(" relationOfFieldsAndVarsMap : " + rofv.fieldName + " " + rofv.variableName + " " + rofv.threadName + " " + rofv.sourceLine + " " + rofv.lineNumber);
           //                             store += " relationOfFieldsAndVarsMap : " + rofv.fieldName + " " + rofv.variableName + " " + rofv.threadName + " " + rofv.sourceLine + " " + rofv.lineNumber;
                                    }   
                                    myNode.relationOfFieldsAndVarsMap.put(d.fieldName, rvs);
                                }
            System.out.print(" locks : " + (d.locks != null ? d.locks.toString() : null));
            System.out.print(" lockRemovals : " + (d.lockRemovals != null ? Arrays.asList(d.lockRemovals) : null));
            
            vdt = myNode.varData.get(d.threadName);
            
            if(vdt!=null) {
                for(String vdv : vdt.keySet()) {
                    if(vdt.get(vdv)!=null) {
                        for(VariableData vd:vdt.get(vdv)) {  
                            if(vd!=null) {
                                System.out.println(" Variable data : ");
           //                     store += " Variable data : ";
                                System.out.print(" variableName : " + vd.variableName);
         //                       store += " variableName : " + vd.variableName;
                                System.out.print(" lineNumber : " + vd.lineNumber);
          //                      store += " lineNumber : " + vd.lineNumber;
                                System.out.print(" methodName : " + vd.methodName);
          //                      store += " methodName : " + vd.methodName;
                                System.out.print(" className : " + vd.className);
          //                      store += " className : " + vd.className;
                                System.out.print(" writeOperation : " + vd.writeOperation);
          //                      store += " writeOperation : " + vd.writeOperation;
                                System.out.print(" readOperation : " + vd.readOperation);
         //                       store += " readOperation : " + vd.readOperation;
                                System.out.print(" isSynchronized : " + vd.isSynchronized);
          //                      store += " isSynchronized : " + vd.isSynchronized;
                                System.out.print(" fileLocation : " + vd.fileLocation);
          //                      store += " fileLocation : " + vd.fileLocation;
                                System.out.print(" packageName : " + vd.packageName);
          //                      store += " packageName : " + vd.packageName;
                                System.out.print(" sourceLine : " + vd.sourceLine);
          //                      store += " sourceLine : " + vd.sourceLine;
                                System.out.print(" threadName : " + vd.threadName);
           //                     store += " threadName : " + vd.threadName;
                                System.out.print(" threadLocks : " + Arrays.toString(myNode.threadLocks.get(vd.threadName).toArray()));
            //                    store += " threadLocks : " + Arrays.toString(myNode.threadLocks.get(vd.threadName).toArray());
                                if(myNode.relationOfFieldsAndVarsMap.get(vd.variableName)!=null) {  
                                    System.out.print(" 111111111 : " + vd.variableName + " " + myNode.relationOfFieldsAndVarsMap.get(vd.variableName).size());
                                    for(RelationOfFieldsAndVars rofv:myNode.relationOfFieldsAndVarsMap.get(vd.variableName)) {
                                        System.out.print(" relationOfFieldsAndVarsMap : " + rofv.fieldName + " " + rofv.variableName + " " + rofv.threadName + " " + rofv.sourceLine + " " + rofv.lineNumber);
           //                             store += " relationOfFieldsAndVarsMap : " + rofv.fieldName + " " + rofv.variableName + " " + rofv.threadName + " " + rofv.sourceLine + " " + rofv.lineNumber;
                                    }    
                                }
                                    
                                    
                                System.out.print(" type : " + vd.type);
          //                      store += " type : " + vd.type;
                                System.out.print(" value : " + vd.value);
          //                      store += " value : " + vd.value;
                            }
                        }
                    }
                }
            }
            
      //      bw.write(store);
      //      bw.newLine();
            DBObject prevDBObject = toDBObject(myNode,d);
      //      myNode.prevDBObject = prevDBObject;
      //      System.out.println("out..." + prevDBObject);
            collection.insert(prevDBObject);
            prevDBObject = null;
            }
        }
        

        for (Node nd : myNode.children) {
            nd.previousid=myNode.id;
         //   nd.prevDBObject=myNode.prevDBObject;
         //   System.out.println("DBObjects .... ");
            printTree(nd);
        }
        }catch(Exception e){
            e.printStackTrace();
            
        }
    }

    public void printData(Data d) {

        System.out.println();
        System.out.print(" fieldName : " + d.fieldName);
        System.out.print(" lineNumber : " + d.lineNumber);
        System.out.print(" methodName : " + d.methodName);
        System.out.print(" className : " + d.className);
        System.out.print(" instance : " + d.instance);
        System.out.print(" writeOperation : " + d.writeOperation);
        System.out.print(" readOperation : " + d.readOperation);
        System.out.print(" threadName : " + d.threadName);
        System.out.print(" isSynchronized : " + d.isSynchronized);
        System.out.print(" packageName : " + d.packageName);
        System.out.print(" fileLocation : " + d.fileLocation);
        System.out.print(" isMonitorEnter : " + d.isMonitorEnter);
        System.out.print(" isMonitorExit : " + d.isMonitorExit);
        System.out.print(" lockRef : " + d.lockRef);
        System.out.print(" value : " + d.value);
        System.out.print(" type : " + d.type);
        System.out.print(" sourceLine : " + d.sourceLine);
        System.out.print(" locks : " + (d.locks != null ? d.locks.toString() : null));
        System.out.print(" lockRemovals : " + (d.lockRemovals != null ? Arrays.asList(d.lockRemovals) : null));

    }
    
    public void printVarData(VariableData d) {

        System.out.println();
        System.out.print(" varName : " + d.variableName);
        System.out.print(" lineNumber : " + d.lineNumber);
        System.out.print(" methodName : " + d.methodName);
        System.out.print(" className : " + d.className);
        System.out.print(" instance : " + d.instance);
        System.out.print(" writeOperation : " + d.writeOperation);
        System.out.print(" readOperation : " + d.readOperation);
        System.out.print(" threadName : " + d.threadName);
        System.out.print(" isSynchronized : " + d.isSynchronized);
        System.out.print(" packageName : " + d.packageName);
        System.out.print(" fileLocation : " + d.fileLocation);
        System.out.print(" value : " + d.value);
        System.out.print(" type : " + d.type);
        System.out.print(" sourceLine : " + d.sourceLine);

    }

    public void checkRule(Node myNode, Rule checkRule, HashMap<String, Rule> states) {

        List<Data> ld = myNode.data;
        Rule state;

        for (Data d : ld) {
            if (states.containsKey(d.threadName)) {
                state = states.get(d.threadName);
            } else {
                states.put(d.threadName, new Rule());
                state = states.get(d.threadName);
                state.accessSeq = (ArrayList<String>) checkRule.accessSeq.clone();
            }

            if (d.fieldName != null && d.fieldName.compareTo(checkRule.field) == 0 && state.isIfIncluded == false && d.sourceLine.contains("if")) {
                state.field = d.fieldName;
                state.isIfIncluded = true;
            }

            if (state.isIfIncluded) {
                if (d.fieldName != null && d.fieldName.compareTo(checkRule.field) == 0) {
                    if (state.accessSeq.isEmpty() == false && state.accessSeq.get(0).compareTo("r") == 0 && d.readOperation == true) {
                        state.accessSeq.remove(0);
                    } else if (state.accessSeq.isEmpty() == false && state.accessSeq.get(0).compareTo("w") == 0 && d.writeOperation == true) {
                        state.accessSeq.remove(0);
                    } else if (state.accessSeq.isEmpty() == false && state.accessSeq.get(0).compareTo("r") == 0 && d.writeOperation == true) {
                        state = new Rule();
                        state.accessSeq = (ArrayList<String>) checkRule.accessSeq.clone();
                        continue;
                    }
                }

                if (d.fieldName != null && d.fieldName.compareTo(checkRule.lock) == 0) {
                    if (state.accessSeq.isEmpty() == false && state.accessSeq.get(0).compareTo("u") == 0 && d.sourceLine.contains("unlock")) {
                        state.accessSeq.remove(0);
                    } else if (state.accessSeq.isEmpty() == false && state.accessSeq.get(0).compareTo("l") == 0 && d.sourceLine.contains("lock")) {
                        state.accessSeq.remove(0);
                    }
                }
            }

            if (state.accessSeq.isEmpty() && state.isIfIncluded == checkRule.isIfIncluded && state.field.compareTo(checkRule.field) == 0) {
                System.out.println("Error pattern detected... " + d.lineNumber + " " + d.className);
                System.exit(-1);
            }
        }

        for (Node nd : myNode.children) {
            checkRule(nd, checkRule, states);
        }
    }

    class Rule {

        String threadName = null;
        String field = null;
        String lock = null;
        boolean isIfIncluded = false;
        ArrayList<String> accessSeq = new ArrayList<>();

        public void check() {

        }
    }

    class StateNode {

        int stateId = -1;
        int depth = -1;
        int currentSubpathNodes = 0;
        boolean visited = false;
        boolean isEndState = false;
        boolean isStateMatch = false;
        int realParent = -1;
        ArrayList<Integer> parrents = new ArrayList<>();
        ArrayList<Integer> children = new ArrayList<>();
    }

    private StateNode deepCloneStateNode(StateNode origin) {
        StateNode clone = new StateNode();
        clone.stateId = origin.stateId;
        clone.depth = origin.depth;
        clone.currentSubpathNodes = origin.currentSubpathNodes;
        clone.visited = origin.visited;
        clone.isEndState = origin.isEndState;
        clone.parrents = DeepClone.deepClone(origin.parrents);
        clone.children = DeepClone.deepClone(origin.children);

        return clone;
    }

    class Node {

        protected List<Data> data = new ArrayList<Data>();
        protected ArrayList<String> threadAccessed = new ArrayList<>();
        protected Node parent = null;
        protected List<Node> children = new ArrayList<Node>();
        protected int id = 0;
        protected int previousid = -100;
        protected int depth = 0;
        protected boolean locksSearched = false;
        protected DBObject prevDBObject = null;
        protected int objectCount = 0;
        protected HashMap<String,Integer> objectPerThreadCount = new HashMap<>();
        HashMap<String, HashSet<String>> threadLocks = new HashMap<>();
        HashMap<String, HashMap<String,ArrayList<VariableData>>> varData = new HashMap<>();
        ConcurrentHashMap<String,ArrayList<RelationOfFieldsAndVars>> relationOfFieldsAndVarsMap = new ConcurrentHashMap<>();
        HashMap<String,HashSet<String>> fieldVarGroups = new HashMap<>();
        
        public HashMap<String, HashSet<String>> getParentThreadLocks() {            
            if(parent!=null)
                for(String key:parent.threadLocks.keySet()) {
                    threadLocks.put(key,new HashSet<>());
                    for(String elem:parent.threadLocks.get(key)) {
                        threadLocks.get(key).add(elem); 
                    }
                }
            
            return threadLocks;
        }
        
        public HashMap<String, HashSet<String>> getFieldVarGroups() {            
            if(parent!=null)
                for(String key:parent.fieldVarGroups.keySet()) {
                    fieldVarGroups.put(key,new HashSet<>());
                    for(String elem:parent.fieldVarGroups.get(key)) {
                        fieldVarGroups.get(key).add(elem); 
                    }
                }
            
            return fieldVarGroups;
        }
        
        public ConcurrentHashMap<String,ArrayList<RelationOfFieldsAndVars>> getRelationOfFieldsAndVarsMap() {         
            if(parent!=null)
            //    System.out.println("pppppppp " + parent.id);
                for(String key:parent.relationOfFieldsAndVarsMap.keySet()) {
                    relationOfFieldsAndVarsMap.put(key,new ArrayList<>());
                    for(RelationOfFieldsAndVars elem:parent.relationOfFieldsAndVarsMap.get(key)) {
                        relationOfFieldsAndVarsMap.get(key).add(elem.copy()); 
                    }
                }
            
            return relationOfFieldsAndVarsMap;
        }
            

        public ArrayList<Long> getParentLockInfo(String thread, Node parent) {
            ArrayList<Long> parentLocks = null;

            if (parent != null) {
                Node nd = parent;

                for (Data d : nd.data) {
                    if (d.threadName.compareTo(thread) == 0 && d.locks != null) {
                        parentLocks = (ArrayList<Long>) d.locks.clone();
                        parentLockRemovals = new HashMap<>();
                        if (d.lockRemovals != null) {
                            parentLockRemovals.putAll(d.lockRemovals);
                        }
                        //    System.out.println("parentLocks : " + parentLocks.toString());
                        break;
                    }
                }

                if (parentLocks == null && nd.parent != null && !locksSearched) {
                    locksSearched = true;
                    parentLocks = getParentLockInfo(thread, nd.parent);
                    locksSearched = false;
                }
            }

            return parentLocks;
        }

        public void addThreadLock(Data d, String thread, long lockInstance) {
            ArrayList<Long> locks = d.locks;
            if (locks == null) {
                locks = new ArrayList<>();
                d.locks = locks;
            }

            if (!locks.contains(lockInstance)) {
                locks.add(lockInstance);
            }
        }

        public boolean removeThreadLock(Data d, String thread, long lockInstance) {
            boolean removal = false;
            ArrayList<Long> locks = d.locks;
            if (locks != null) {
                if (locks.remove(lockInstance)) {
                    removal = true;
                }
            }

            return removal;

        }

        public boolean findNode(int id, int depth) {
            boolean found = false;

            while (current.depth >= depth && current.depth != 0) {
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

        public Node findNode(int id, int depth, Node parentNode) {
            Node found = parentNode;

            if (found.id != id) {
                for (Node nd : found.children) {
                    if (nd.id == id) {
                        found = nd;
                        //    System.out.println("Found .....");
                        break;
                    } else {
                        if (nd.depth > depth) {
                            break;
                        }
                        found = findNode(id, depth, nd);
                    }
                }
            }

            return found;
        }
    }

    class Data {

        String fieldName = null;
        String className = null;
        long instance = 0;
        boolean writeOperation = false;
        boolean readOperation = false;
        String threadName = null;
        String methodName = null;
        int threadId = -1;
        boolean isSynchronized = false;
        String fileLocation = null;
        int lineNumber = -1;
        String packageName = null;
        String value = null;
        String type = null;
        boolean isMonitorEnter = false;
        boolean isMonitorExit = false;
        int lockRef = -1;
        String sourceLine = null;
        ArrayList<Long> locks = new ArrayList<>();
        HashMap<Long, Integer> lockRemovals = new HashMap<>();
    }
    
    class VariableData {

        String variableName = null;
        String className = null;
        long instance = 0;
        boolean writeOperation = false;
        boolean readOperation = false;
        String threadName = null;
        String methodName = null;
        int threadId = -1;
        boolean isSynchronized = false;
        String fileLocation = null;
        int lineNumber = -1;
        String packageName = null;
        String value = null;
        String type = null;
        String sourceLine = null;
    }
    
    class RelationOfFieldsAndVars {

        String fieldName = null;
        String variableName = null;
        String className = null;
        String threadName = null;
        String methodName = null;
        String packageName = null;
        String type = null;
        String sourceLine = null;
        int lineNumber = -1;
        
        public RelationOfFieldsAndVars copy() {
            RelationOfFieldsAndVars cp = new RelationOfFieldsAndVars();
            
            cp.fieldName=this.fieldName;
            cp.variableName=this.variableName;
            cp.className=this.className;
            cp.threadName=this.threadName;
            cp.methodName=this.methodName;
            cp.packageName=this.packageName;
            cp.type=this.type;
            cp.sourceLine=this.sourceLine;
            cp.lineNumber=this.lineNumber;
            
            return cp;
        }
    }


    /*
    public void checkFieldRule(Node myNode, HashMap<String, FieldState> fieldStates) {
        // Set the field rule to check
        ArrayList<String> checkFieldRule = new ArrayList<>();
        checkFieldRule.add("readField");
        checkFieldRule.add("threadChange");
        checkFieldRule.add("writeField");
        checkFieldRule.add("threadBack");
        checkFieldRule.add("writeField");

        List<Data> ld = myNode.data;
        FieldState state = null;

        for (Data d : ld) {
            System.out.println();
            System.out.print("id : " + myNode.id);
            System.out.print(" depth : " + myNode.depth);
            printData(d);
            if (d.fieldName != null) {
                if (fieldStates.containsKey(d.fieldName)) {
                    state = fieldStates.get(d.fieldName);
                } else {
                    fieldStates.put(d.fieldName, new FieldState());
                    state = fieldStates.get(d.fieldName);
                    state.resetFieldRule(checkFieldRule);
        

                }//1916-27,1909-20,1222-7

                if (d.readOperation && state.checkFieldRule.size() != 0 && state.checkFieldRule.get(0).compareTo("readField") == 0) {
                    state.threadSeq.add(d.threadName);
                    state.checkFieldRule.remove(0);
                    state.lineNumberSeq.add(d.lineNumber);
                    state.allThreadSeq.add(d.threadName);
                    state.parentId = myNode.id;
                    state.parentDepth = myNode.depth;
                    fieldStates.replace(d.fieldName, state);
                    System.out.println("phase 1... " + d.lineNumber + " " + d.className + " " + d.fieldName + state.lineNumberSeq.toString() + " " + state.allThreadSeq.toString() + " " + state.log);
              
                } else if (state.checkFieldRule.size() != 0 && state.checkFieldRule.get(0).compareTo("threadChange") == 0 && state.checkFieldRule.get(1).compareTo("writeField") == 0) {
                    if (!state.threadSeq.contains(d.threadName) && d.writeOperation) {
                    //    for (Node nd : myNode.children) {
                    //        checkFieldRule(nd, deepCloneStates(fieldStates));
                    //    }
                        state.checkFieldRule.remove(0);
                        state.checkFieldRule.remove(0);
                        state.lineNumberSeq.add(d.lineNumber);
                        state.allThreadSeq.add(d.threadName);
                        System.out.println("phase 2... " + d.lineNumber + " " + d.className + " " + d.fieldName + state.lineNumberSeq.toString() + " " + state.allThreadSeq.toString() + " " + state.log);
          
                    } *//*else if (state.threadSeq.contains(d.threadName) && d.writeOperation) {
                        state.resetFieldRule(checkFieldRule);
                        if (state.parentId != -1) {
                            Node parentNd = myNode.findNode(state.parentId, state.parentDepth, root);
                            for (Node nd : parentNd.children) {
                                checkFieldRule(nd, deepCloneStates(fieldStates));
                            }
                        }
                        state.parentId = -1;
                        
                    }*/
 /*            } else if (state.checkFieldRule.size() != 0 && state.checkFieldRule.get(0).compareTo("threadBack") == 0 && state.checkFieldRule.get(1).compareTo("writeField") == 0) {
                    if (state.threadSeq.get(0).compareTo(d.threadName) == 0 && d.writeOperation) {
                        state.checkFieldRule.remove(0);
                        state.checkFieldRule.remove(0);
                        state.lineNumberSeq.add(d.lineNumber);
                        state.allThreadSeq.add(d.threadName);
                        System.out.println("phase 3... " + d.lineNumber + " " + d.className + " " + d.fieldName + state.lineNumberSeq.toString() + " " + state.allThreadSeq.toString() + " " + state.log);
                 
                    }
                }

                if (state != null && state.checkFieldRule.isEmpty()) {
                    //    if(d.fieldName.compareTo("gr.uop.intermittent.faults.symbiosistest.TestClass.filled")==0) 
                    System.out.println("Error pattern detected... " + d.lineNumber + " " + d.className + " " + d.fieldName + state.lineNumberSeq.toString() + " " + state.allThreadSeq.toString() + " " + state.log);
                    state.resetFieldRule(checkFieldRule);
                    //  System.out.println("========= : " + state.parentId);
                    if (state.parentId != -1) {
                        Node parentNd = myNode.findNode(state.parentId, state.parentDepth, root);
                        for (Node nd : parentNd.children) {
                            checkFieldRule(nd, deepCloneStates(fieldStates));
                        }
                    }
                    state.parentId = -1;

                }
            }
        }

        for (Node nd : myNode.children) {
            checkFieldRule(nd, deepCloneStates(fieldStates));
        }

    }*/

    public void checkFieldRule(Node myNode, HashMap<String, HashMap<String, FieldState>> fieldStates) {
        // Set the field rule to check
        ArrayList<String> checkFieldRule = new ArrayList<>();
        checkFieldRule.add("readField");
        checkFieldRule.add("threadChange");
        checkFieldRule.add("writeField");
        checkFieldRule.add("threadBack");
        checkFieldRule.add("writeField");

        List<Data> ld = myNode.data;
        FieldState state = null;

// System.out.println("========= 1 : ");
        for (Data d : ld) {
            //    System.out.println();
            //    System.out.print("id : " + myNode.id);
            //    System.out.print(" depth : " + myNode.depth);
            //    printData(d);
            //    System.out.println("========= 2 : " + d.fieldName);
            if (threadNames.containsKey(d.fieldName)/* && d.fieldName.contains("filled")*/) {
                threadNames.get(d.fieldName).add(d.threadName);
            } else {//if(d.fieldName.contains("filled")) {
                HashSet<String> threadSet = new HashSet<>();
                threadSet.add(d.threadName);
                threadNames.put(d.fieldName, threadSet);
            }
// System.out.println("========= 3 : ");
            //         if (d.fieldName != null && d.fieldName.contains("filled"))
            for (String threadN : threadNames.get(d.fieldName)) {
                if (d.fieldName != null/* && d.fieldName.contains("filled")*/) {
                    //    System.out.println("========= 4 : ");
                    if (fieldStates.containsKey(d.fieldName)) {
                        if (fieldStates.get(d.fieldName).containsKey(threadN)) {
                            state = fieldStates.get(d.fieldName).get(threadN);
                        } else {
                            fieldStates.get(d.fieldName).put(threadN, new FieldState());
                            state = fieldStates.get(d.fieldName).get(threadN);
                            state.resetFieldRule(checkFieldRule);
                        }

                    } else {
                        fieldStates.put(d.fieldName, new HashMap<String, FieldState>());
                        fieldStates.get(d.fieldName).put(threadN, new FieldState());
                        state = fieldStates.get(d.fieldName).get(threadN);
                        state.resetFieldRule(checkFieldRule);

                    }
                    if (state.allThreadSeq.size() <= 1 || (state.allThreadSeq.size() == 2 && state.allThreadSeq.contains(d.threadName))) {
//System.out.println("========= 5 : " + d.fieldName + " " + d.threadName + " " + " " + threadN + " " + state.threadSeq + " " + fieldStates.get(d.fieldName).get(threadN).checkFieldRule + " " + d.writeOperation + " " + d.readOperation);
                        if (d.threadName.compareTo(threadN) == 0 && d.readOperation && state.checkFieldRule.size() != 0 && state.checkFieldRule.get(0).compareTo("readField") == 0) {
                            state.threadSeq.add(d.threadName);
                            state.checkFieldRule.remove(0);
                            state.lineNumberSeq.add(d.lineNumber);
                            state.allThreadSeq.add(d.threadName);
                            state.parentId = myNode.id;
                            state.parentDepth = myNode.depth;
                            if (VM.getVM().getConfig().get("vm.compilerop") != null && d.sourceLine != null) {
                                d.sourceLine = d.sourceLine.trim();
                                String fieldN = d.fieldName;
                                if (fieldN.contains(".")) {
                                    fieldN = fieldN.substring(fieldN.lastIndexOf(".") + 1);
                                }
                                if (d.sourceLine.contains("=")) {
                                    String[] fields = d.sourceLine.split("=");
                                    if (fields[0].contains(fieldN) && fields[1].contains(fieldN)) {
                                        state.resetFieldRule(checkFieldRule);
                                    }
                                } else if (d.sourceLine.contains(fieldN + "++") || d.sourceLine.contains(fieldN + "--")) {
                                    state.resetFieldRule(checkFieldRule);
                                }

                            }
                            //     System.out.println("========= 11 : " + d.threadName + " " + threadN + " " + state.checkFieldRule + " " + fieldStates.get(d.fieldName).get(threadN).checkFieldRule);
                            //     fieldStates.get(d.fieldName).replace(threadN, state);

                        } else if (d.threadName.compareTo(threadN) != 0 && state.checkFieldRule.size() != 0 && state.checkFieldRule.get(0).compareTo("threadChange") == 0 && state.checkFieldRule.get(1).compareTo("writeField") == 0) {
                            if (!state.threadSeq.contains(d.threadName) && d.writeOperation) {
                                //    for (Node nd : myNode.children) {
                                //        checkFieldRule(nd, deepCloneStates(fieldStates));
                                //    }
                                state.checkFieldRule.remove(0);
                                state.checkFieldRule.remove(0);
                                state.lineNumberSeq.add(d.lineNumber);
                                state.allThreadSeq.add(d.threadName);
                                //         System.out.println("========= 22 : " + d.threadName + " " + threadN + " " + state.checkFieldRule + " " + fieldStates.get(d.fieldName).get(threadN).checkFieldRule);

                            }
                        } else if (d.threadName.compareTo(threadN) == 0 && state.checkFieldRule.size() != 0 && state.checkFieldRule.get(0).compareTo("threadBack") == 0 && state.checkFieldRule.get(1).compareTo("writeField") == 0) {
                            if (state.threadSeq.get(0).compareTo(d.threadName) == 0 && d.writeOperation) {
                                state.checkFieldRule.remove(0);
                                state.checkFieldRule.remove(0);
                                state.lineNumberSeq.add(d.lineNumber);
                                state.allThreadSeq.add(d.threadName);
                                //          System.out.println("========= 33 : " + d.threadName + " " + threadN + " " + state.checkFieldRule + " " + fieldStates.get(d.fieldName).get(threadN).checkFieldRule);

                            } else if (state.threadSeq.get(0).compareTo(d.threadName) == 0 && d.readOperation) {
                                boolean ignore = false;
                                if (VM.getVM().getConfig().get("vm.compilerop") != null && d.sourceLine != null) {
                                    d.sourceLine = d.sourceLine.trim();
                                    String fieldN = d.fieldName;
                                    if (fieldN.contains(".")) {
                                        fieldN = fieldN.substring(fieldN.lastIndexOf(".") + 1);
                                    }
                                    if (d.sourceLine.contains("=")) {
                                        String[] fields = d.sourceLine.split("=");
                                        if (fields[0].contains(fieldN) && fields[1].contains(fieldN)) {
                                            ignore = true;
                                        }
                                    } else if (d.sourceLine.contains(fieldN + "++") || d.sourceLine.contains(fieldN + "--")) {
                                        ignore = true;
                                    }

                                }
                                if (!ignore) {
                                    state.resetFieldRule(checkFieldRule);
                                }

                            }
                            /*    if (state.threadSeq.get(0).compareTo(d.threadName) == 0 && d.readOperation && state.threadSeq.contains("wr")) {
                        state.resetFieldRule(checkFieldRule);
              //          System.out.println("========= 33 : " + d.threadName + " " + threadN + " " + state.checkFieldRule + " " + fieldStates.get(d.fieldName).get(threadN).checkFieldRule);

                 
                    }}*///else if (state.threadSeq.contains(d.threadName) && d.readOperation) {
                            //    state.resetFieldRule(checkFieldRule);
                            //    state.checkFieldRule.remove(0);
                            //    state.checkFieldRule.remove(0);
                            //     if (state.parentId != -1) {
                            //         Node parentNd = myNode.findNode(state.parentId, state.parentDepth, root);
                            //         for (Node nd : parentNd.children) {
                            //             checkFieldRule(nd, deepCloneStates(fieldStates));
                            //         }
                            //     }
                            //     state.parentId = -1;

                            //   }
                        }

                        if (state != null && state.checkFieldRule.isEmpty()) {
                            //    if(d.fieldName.compareTo("gr.uop.intermittent.faults.symbiosistest.TestClass.filled")==0) 
                            errors.add("Error pattern detected... " + d.lineNumber + " " + d.className + " " + d.fieldName + state.lineNumberSeq.toString() + " " + state.allThreadSeq.toString() + " " + state.log);
                            state.resetFieldRule(checkFieldRule);
                            //  System.out.println("========= : " + state.parentId);
                            //    if (state.parentId != -1) {
                            //        Node parentNd = myNode.findNode(state.parentId, state.parentDepth, root);
                            //        for (Node nd : parentNd.children) {
                            //            checkFieldRule(nd, deepCloneStates(fieldStates));
                            //        }
                            //    }
                            //    state.parentId = -1;

                        }
                    }
                }
            }
        }
//System.out.println("========= 6 : ");
        for (Node nd : myNode.children) {
            checkFieldRule(nd, deepCloneStates(fieldStates));
        }

        for (HashMap.Entry<String, HashMap<String, FieldState>> entry : fieldStates.entrySet()) {

            for (HashMap.Entry<String, FieldState> entry2 : entry.getValue().entrySet()) {
                String key2 = entry2.getKey();
                FieldState value = entry2.getValue();
                value.allThreadSeq = null;
                value.checkFieldRule = null;
                value.threadSeq = null;
                value.lineNumberSeq = null;
                value = null;
            }
            entry = null;
        }
        fieldStates = null;
    }

    public void checkFieldRule2(Node myNode, HashMap<String, HashMap<String, FieldState>> fieldStates) {
        // Set the field rule to check
        ArrayList<String> checkFieldRule = new ArrayList<>();
        checkFieldRule.add("readField");
        checkFieldRule.add("threadChange");
        checkFieldRule.add("writeField");
        checkFieldRule.add("threadBack");
        checkFieldRule.add("readField");

        List<Data> ld = myNode.data;
        FieldState state = null;
//System.out.println("========= 33 : " + ld.size());
        for (Data d : ld) {
            ////  System.out.println("========= 32 : ");
            if (threadNames.containsKey(d.fieldName)/* && d.fieldName.contains("filled")*/) {
                threadNames.get(d.fieldName).add(d.threadName);
            } else {//if(d.fieldName.contains("filled")) {
                HashSet<String> threadSet = new HashSet<>();
                threadSet.add(d.threadName);
                threadNames.put(d.fieldName, threadSet);
            }
            //System.out.println("========= 3 : ");
            //         if (d.fieldName != null && d.fieldName.contains("filled"))
            for (String threadN : threadNames.get(d.fieldName)) {
                if (d.fieldName != null/* && d.fieldName.contains("filled")*/) {
                    //    System.out.println("========= 4 : ");
                    if (fieldStates.containsKey(d.fieldName)) {
                        if (fieldStates.get(d.fieldName).containsKey(threadN)) {
                            state = fieldStates.get(d.fieldName).get(threadN);
                        } else {
                            fieldStates.get(d.fieldName).put(threadN, new FieldState());
                            state = fieldStates.get(d.fieldName).get(threadN);
                            state.resetFieldRule(checkFieldRule);
                        }

                    } else {
                        fieldStates.put(d.fieldName, new HashMap<String, FieldState>());
                        fieldStates.get(d.fieldName).put(threadN, new FieldState());
                        state = fieldStates.get(d.fieldName).get(threadN);
                        state.resetFieldRule(checkFieldRule);

                    }

                    if (state.allThreadSeq.size() <= 1 || (state.allThreadSeq.size() == 2 && state.allThreadSeq.contains(d.threadName))) {
                        if (d.threadName.compareTo(threadN) == 0 && d.readOperation && state.checkFieldRule.size() != 0 && state.checkFieldRule.get(0).compareTo("readField") == 0) {
                            state.threadSeq.add(d.threadName);
                            state.checkFieldRule.remove(0);
                            state.lineNumberSeq.add(d.lineNumber);
                            state.allThreadSeq.add(d.threadName);
                            state.parentId = myNode.id;
                            state.parentDepth = myNode.depth;
                            //    System.out.println("========= 1 : ");
                            //     fieldStates.replace(d.fieldName, state);

                        } else if (d.threadName.compareTo(threadN) != 0 && state.checkFieldRule.size() != 0 && state.checkFieldRule.get(0).compareTo("threadChange") == 0 && state.checkFieldRule.get(1).compareTo("writeField") == 0) {
                            if (!state.threadSeq.contains(d.threadName) && d.writeOperation) {
                                //     for (Node nd : myNode.children) {
                                //         checkFieldRule(nd, deepCloneStates(fieldStates));
                                //     }
                                state.checkFieldRule.remove(0);
                                state.checkFieldRule.remove(0);
                                state.lineNumberSeq.add(d.lineNumber);
                                state.allThreadSeq.add(d.threadName);
                                state.threadSeq.add(d.threadName);
                                //      System.out.println("========= 2 : ");

                            }
                        } else if (d.threadName.compareTo(threadN) == 0 && state.checkFieldRule.size() != 0 && state.checkFieldRule.get(0).compareTo("threadChange") == 0 && state.checkFieldRule.get(1).compareTo("writeField") == 0) {
                            if (state.threadSeq.contains(d.threadName) && d.writeOperation) {
                                //    for (Node nd : myNode.children) {
                                //        checkFieldRule(nd, deepCloneStates(fieldStates));
                                //    }
                                //      state.allThreadSeq.add("wr");
                                state.resetFieldRule(checkFieldRule);
                                //         System.out.println("========= 22 : " + d.threadName + " " + threadN + " " + state.checkFieldRule + " " + fieldStates.get(d.fieldName).get(threadN).checkFieldRule);

                            }
                        } else if (d.threadName.compareTo(threadN) == 0 && state.checkFieldRule.size() != 0 && state.checkFieldRule.get(0).compareTo("threadBack") == 0 && state.checkFieldRule.get(1).compareTo("readField") == 0) {
                            if (state.threadSeq.get(0).compareTo(d.threadName) == 0 && d.readOperation) {
                                state.checkFieldRule.remove(0);
                                state.checkFieldRule.remove(0);
                                state.lineNumberSeq.add(d.lineNumber);
                                state.allThreadSeq.add(d.threadName);
                                //       System.out.println("========= 3 : ");

                            } else if (state.threadSeq.get(0).compareTo(d.threadName) == 0 && d.writeOperation) {
                                state.resetFieldRule(checkFieldRule);

                                //  if (state.parentId != -1) {
                                //     Node parentNd = myNode.findNode(state.parentId, state.parentDepth, root);
                                //      for (Node nd : parentNd.children) {
                                //          checkFieldRule(nd, deepCloneStates(fieldStates));
                                //      }
                                //     }
                                //  state.parentId = -1;
                            }
                        }

                        if (state != null && state.checkFieldRule.isEmpty()) {
                            //    if(d.fieldName.compareTo("gr.uop.intermittent.faults.symbiosistest.TestClass.filled")==0) 
                            errors.add("Error pattern detected... " + d.lineNumber + " " + d.className + " " + d.fieldName + state.lineNumberSeq.toString() + " " + state.allThreadSeq.toString() + " " + state.log);
                            state.resetFieldRule(checkFieldRule);
                            //  System.out.println("========= : " + state.parentId);
                            //     if (state.parentId != -1) {
                            //      Node parentNd = myNode.findNode(state.parentId, state.parentDepth, root);
                            //      for (Node nd : parentNd.children) {
                            //          checkFieldRule(nd, deepCloneStates(fieldStates));
                            //      }
                            //  }
                            //      state.parentId = -1;

                        }
                    }
                }
            }
        }

        for (Node nd : myNode.children) {
            checkFieldRule2(nd, deepCloneStates(fieldStates));
        }

        for (HashMap.Entry<String, HashMap<String, FieldState>> entry : fieldStates.entrySet()) {

            for (HashMap.Entry<String, FieldState> entry2 : entry.getValue().entrySet()) {
                String key2 = entry2.getKey();
                FieldState value = entry2.getValue();
                value.allThreadSeq = null;
                value.checkFieldRule = null;
                value.threadSeq = null;
                value.lineNumberSeq = null;
                value = null;
            }
            entry = null;
        }
        fieldStates = null;

    }

    /*
    public void checkFieldRule2(Node myNode, HashMap<String, FieldState> fieldStates) {
        // Set the field rule to check
        ArrayList<String> checkFieldRule = new ArrayList<>();
        checkFieldRule.add("readField");
        checkFieldRule.add("threadChange");
        checkFieldRule.add("writeField");
        checkFieldRule.add("threadBack");
        checkFieldRule.add("readField");

        List<Data> ld = myNode.data;
        FieldState state = null;

        for (Data d : ld) {
            if (d.fieldName != null) {
                if (fieldStates.containsKey(d.fieldName)) {
                    state = fieldStates.get(d.fieldName);
                } else {
                    fieldStates.put(d.fieldName, new FieldState());
                    state = fieldStates.get(d.fieldName);
                    state.resetFieldRule(checkFieldRule);
           

                }

                if (d.readOperation && state.checkFieldRule.size() != 0 && state.checkFieldRule.get(0).compareTo("readField") == 0) {
                    state.threadSeq.add(d.threadName);
                    state.checkFieldRule.remove(0);
                    state.lineNumberSeq.add(d.lineNumber);
                    state.allThreadSeq.add(d.threadName);
                    state.parentId = myNode.id;
                    state.parentDepth = myNode.depth;
                    fieldStates.replace(d.fieldName, state);
     
                } else if (state.checkFieldRule.size() != 0 && state.checkFieldRule.get(0).compareTo("threadChange") == 0 && state.checkFieldRule.get(1).compareTo("writeField") == 0) {
                    if (!state.threadSeq.contains(d.threadName) && d.writeOperation) {
                   //     for (Node nd : myNode.children) {
                   //         checkFieldRule(nd, deepCloneStates(fieldStates));
                   //     }
                        state.checkFieldRule.remove(0);
                        state.checkFieldRule.remove(0);
                        state.lineNumberSeq.add(d.lineNumber);
                        state.allThreadSeq.add(d.threadName);
                        state.threadSeq.add(d.threadName);
                
                    } else if (state.threadSeq.contains(d.threadName) && d.writeOperation) {
                        state.resetFieldRule(checkFieldRule);
                        //     System.out.println("========= : " + state.parentId);
                        if (state.parentId != -1) {
                    //        Node parentNd = myNode.findNode(state.parentId, state.parentDepth, root);
                   //         for (Node nd : parentNd.children) {
                   //             checkFieldRule(nd, deepCloneStates(fieldStates));
                   //         }
                        }
                        state.parentId = -1;
                 
                    }
                } else if (state.checkFieldRule.size() != 0 && state.checkFieldRule.get(0).compareTo("threadBack") == 0 && state.checkFieldRule.get(1).compareTo("readField") == 0) {
                    if (state.threadSeq.get(0).compareTo(d.threadName) == 0 && d.readOperation) {
                        state.checkFieldRule.remove(0);
                        state.checkFieldRule.remove(0);
                        state.lineNumberSeq.add(d.lineNumber);
                        state.allThreadSeq.add(d.threadName);
          
                    } else if (state.threadSeq.get(0).compareTo(d.threadName) == 0 && d.writeOperation) {
                        state.resetFieldRule(checkFieldRule);

                        if (state.parentId != -1) {
                       //     Node parentNd = myNode.findNode(state.parentId, state.parentDepth, root);
                      //      for (Node nd : parentNd.children) {
                      //          checkFieldRule(nd, deepCloneStates(fieldStates));
                      //      }
                        }
                        state.parentId = -1;
                   
                    }
                }

                if (state != null && state.checkFieldRule.isEmpty()) {
                    //    if(d.fieldName.compareTo("gr.uop.intermittent.faults.symbiosistest.TestClass.filled")==0) 
                    System.out.println("Error pattern detected... " + d.lineNumber + " " + d.className + " " + d.fieldName + state.lineNumberSeq.toString() + " " + state.allThreadSeq.toString() + " " + state.log);
                    state.resetFieldRule(checkFieldRule);
                    //  System.out.println("========= : " + state.parentId);
                    if (state.parentId != -1) {
                  //      Node parentNd = myNode.findNode(state.parentId, state.parentDepth, root);
                  //      for (Node nd : parentNd.children) {
                  //          checkFieldRule(nd, deepCloneStates(fieldStates));
                  //      }
                    }
                    state.parentId = -1;

                }
            }
        }

        for (Node nd : myNode.children) {
            checkFieldRule(nd, deepCloneStates(fieldStates));
        }
        

    }
     */
    private HashMap<String, HashMap<String, FieldState>> deepCloneStates(HashMap<String, HashMap<String, FieldState>> fieldStates) {
        HashMap<String, HashMap<String, FieldState>> fieldStatesCloned = new HashMap<>();

        for (HashMap.Entry<String, HashMap<String, FieldState>> entry : fieldStates.entrySet()) {

            HashMap<String, FieldState> fieldStatesClonedPerThread = new HashMap<>();
            String key = entry.getKey();
            for (HashMap.Entry<String, FieldState> entry2 : entry.getValue().entrySet()) {
                FieldState fieldStateCloned = new FieldState();
                String key2 = entry2.getKey();
                FieldState value2 = entry2.getValue();
                fieldStateCloned.allThreadSeq = DeepClone.deepClone(value2.allThreadSeq);
                fieldStateCloned.checkFieldRule = DeepClone.deepClone(value2.checkFieldRule);
                fieldStateCloned.threadSeq = DeepClone.deepClone(value2.threadSeq);
                fieldStateCloned.lineNumberSeq = DeepClone.deepClone(value2.lineNumberSeq);
                fieldStateCloned.log = value2.log;
                fieldStateCloned.fType = value2.fType;
                fieldStateCloned.parentId = value2.parentId;
                fieldStateCloned.parentDepth = value2.parentDepth;
                fieldStatesClonedPerThread.put(key2, fieldStateCloned);
            }
            //   System.out.println("========= : " + fieldStatesClonedPerThread.keySet());
            fieldStatesCloned.put(key, fieldStatesClonedPerThread);
        }

        return fieldStatesCloned;
    }

    /*    private HashMap<String, FieldState> deepCloneStates(HashMap<String, FieldState> fieldStates) {
        HashMap<String, FieldState> fieldStatesCloned = new HashMap<>();

        for (HashMap.Entry<String, FieldState> entry : fieldStates.entrySet()) {
            FieldState fieldStateCloned = new FieldState();
            String key = entry.getKey();
            FieldState value = entry.getValue();
            fieldStateCloned.allThreadSeq = DeepClone.deepClone(value.allThreadSeq);
            fieldStateCloned.checkFieldRule = DeepClone.deepClone(value.checkFieldRule);
            fieldStateCloned.threadSeq = DeepClone.deepClone(value.threadSeq);
            fieldStateCloned.lineNumberSeq = DeepClone.deepClone(value.lineNumberSeq);
            fieldStateCloned.log = value.log;
            fieldStateCloned.parentId = value.parentId;
            fieldStateCloned.parentDepth = value.parentDepth;
            fieldStatesCloned.put(key, fieldStateCloned);
        }

        return fieldStatesCloned;
    }*/
    class FieldState {

        public int parentId = -1;
        public int parentDepth = -1;
        ArrayList<String> checkFieldRule = new ArrayList<String>();
        ArrayList<String> threadSeq = new ArrayList<String>();
        ArrayList<Integer> lineNumberSeq = new ArrayList<Integer>();
        ArrayList<String> allThreadSeq = new ArrayList<String>();
        String log = "";
        String fType = null;

        public void resetFieldRule(ArrayList<String> fieldRule) {
            checkFieldRule = DeepClone.deepClone(fieldRule);
            threadSeq = new ArrayList<String>();
            lineNumberSeq = new ArrayList<Integer>();
            allThreadSeq = new ArrayList<String>();
            fType = null;
        }

        public void initializeFieldRule() {
            checkFieldRule = new ArrayList<String>();
            threadSeq = new ArrayList<String>();
            lineNumberSeq = new ArrayList<Integer>();
            allThreadSeq = new ArrayList<String>();
        }

        public FieldState deepClone() {
            FieldState fs = new FieldState();
            fs.checkFieldRule = (ArrayList<String>) DeepClone.deepClone(checkFieldRule);
            fs.threadSeq = (ArrayList<String>) DeepClone.deepClone(threadSeq);
            fs.lineNumberSeq = (ArrayList<Integer>) DeepClone.deepClone(lineNumberSeq);
            fs.allThreadSeq = (ArrayList<String>) DeepClone.deepClone(allThreadSeq);
            fs.log = this.log;
            fs.fType = this.fType;

            return fs;
        }

    }

    class SubSet {

        String stateGroup = null;
        String allGroups = "";
        HashSet<Integer> elements = new HashSet<>();
        HashSet<Integer> childElements = new HashSet<>();
        HashSet<String> groups = new HashSet<>();
        SubSet parent = null;
        HashMap<String, SubSet> children = new HashMap<>();
        HashMap<Integer, String> childrenStateGroups = new HashMap<>();

        public void classify(HashMap<Integer, HashMap<Integer, Boolean>> stateGraph, HashMap<Integer, String> stateGroupMap2) {
            for (int el : childElements) {
                //      System.out.println("childElement " + el);
                if (isEndState.get(el)) {
                    //   System.out.println("seq : " + allGroups);
                    finalSequences.add(allGroups);
                    continue;
                }
                String gName = stateGroupMap2.get(el);
                SubSet child = null;
                if (!groups.contains(gName)) {
                    groups.add(gName);
                    child = new SubSet();
                    if (gName != null) {
                        child.allGroups = allGroups + " " + gName;
                    } else {
                        child.allGroups = allGroups;
                    }
                    child.stateGroup = gName;
                    child.elements.add(el);
                    child.childElements.addAll(stateGraph.get(el).keySet());
                    child.parent = this;
                    children.put(gName, child);
                } else {
                    child = children.get(gName);
                    child.elements.add(el);
                    child.childElements.addAll(stateGraph.get(el).keySet());
                }
                childrenStateGroups.put(el, gName);
            }
        }
    }

}
