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

import gr.uop.intermittent.faults.utils.CacheStore;
import java.util.concurrent.locks.Lock;
import java.util.concurrent.locks.ReentrantLock;

/**
 *
 * @author Panagiotis Sotiropoulos
 */
public class TestClass {

    private int count = 0;
    private  int count2 = 0;
    private int count3 = 0;
    
    private final static Object countlock = new Object();
    private final static Object count2lock = new Object();
    private final static Lock l = new ReentrantLock();
    
    public void countMethod() throws Exception {

        for (int i=0; i<1; i++) {
            l.lock();
       //   synchronized(countlock) {
                count += 1;
                count3++;
        //    }
            l.unlock();
            

            synchronized(count2lock) {
                count2 += 2;
                count3++;
            }
            
            CacheStore.cacheStore(this,count,"count","myTestGroup"); 
            CacheStore.cacheStore(this,count2,"count2","myTestGroup");
            
        }
               
    } 

}
