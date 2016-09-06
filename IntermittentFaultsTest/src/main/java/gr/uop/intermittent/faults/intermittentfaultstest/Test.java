/*
 * Copyleft 2015 Red Hat, Inc. and/or its affiliates
 * and other contributors as indicated by the @author tags.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *    http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package gr.uop.intermittent.faults.intermittentfaultstest;

import gr.uop.intermittent.faults.utils.CacheApi;
import gr.uop.intermittent.faults.utils.CacheCollection;

/**
 *
 * @author Panagiotis Sotiropoulos
 */
public class Test {

    private static String groupName2 = "myTestGroup";
    /**
     * @param args the command line arguments
     */
    
    public static void main(String[] args) {
        try {
            TestClass mTC = new TestClass();
            TestThreads mTreads =  new TestThreads("1",mTC);
            mTreads.start();
         
            TestThreads mTreads2 =  new TestThreads("2",mTC);
            mTreads2.start();
            
            TestThreads mTreads3 =  new TestThreads("3",mTC);
            mTreads3.start();
            
        //    while (mTreads.getT().isAlive() || mTreads2.getT().isAlive() || mTreads3.getT().isAlive());
            
       //     if (CacheCollection.getCacheCollection().getCacheInstance(groupName2)!=null)
        //        System.out.println(CacheApi.printCache(groupName2));

        } catch (Exception e) {
            e.printStackTrace();
        }
    }
    
}