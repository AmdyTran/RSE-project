package ch.ethz.rse.integration.tests;

import ch.ethz.rse.Store;

// expected results:
// NON_NEGATIVE UNSAFE
// FITS_IN_TROLLEY UNSAFE
// FITS_IN_RESERVE SAFE

public class Multiplication_Test {

  public static void m1(int i, int j) {
    Store s = new Store(10, 50);
    if(i < 5){
      if(j < 5){
        int k = i*j;
        s.get_delivery(k);
    }
  }
  }
}