package ch.ethz.rse.integration.tests;

import ch.ethz.rse.Store;

// expected results:
// NON_NEGATIVE UNSAFE
// FITS_IN_TROLLEY UNSAFE
// FITS_IN_RESERVE SAFE

public class Negative_Store_Test {
    public static void m(int i){
        Store s = new Store(-10, 20);
        if(i > 0){                  // i in [1, infty]
            s.get_delivery(i);      // non_negative safe, 
            i = i - 2; // range [-1, infty]
            s.get_delivery(i); // unsafe 
            if(i > 0){

                i = i - 1; // range [-1, ...]
                s.get_delivery(i);
            }
        }
        
        
    }
}
