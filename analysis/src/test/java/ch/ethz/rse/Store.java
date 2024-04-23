package ch.ethz.rse;

/**
 * We are verifying calls into this class
 * 
 */
public final class Store {

	// Trolley and reserve size for the store
	private final int trolley_size, reserve_size;
	// Amount of product received so far
	int received_amount;
  
	public Store(int trolley_size, int reserve_size) {
	  this.trolley_size = trolley_size;
	  this.reserve_size = reserve_size;
	  this.received_amount = 0;
	}
  
	public void get_delivery(int volume) {
	   // check NON_NEGATIVE
	  assert 0 <= volume;
	  // check FITS_IN_TROLLEY
	  assert volume <= this.trolley_size;
	  // check FITS_IN_RESERVE
	  assert this.received_amount + volume <= this.reserve_size;
	  this.received_amount += volume;
	  
	}
  }