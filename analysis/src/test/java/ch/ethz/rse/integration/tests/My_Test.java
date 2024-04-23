package ch.ethz.rse.integration.tests;

import ch.ethz.rse.Store;

// expected results:
// NON_NEGATIVE SAFE
// FITS_IN_TROLLEY SAFE
// FITS_IN_RESERVE UNSAFE

public class My_Test {

  public static void m1(int i, int j) {
    Store s = new Store(100, -1);
    s.get_delivery(5);
  }
}

// val = i2
// z = i3