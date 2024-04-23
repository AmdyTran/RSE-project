package ch.ethz.rse.pointer;

import soot.jimple.internal.JInvokeStmt;

/**
 * 
 * Contains information about the initializer of a Store object
 *
 */
public class StoreInitializer {

	/**
	 * statement that performs the initialization
	 */
	private final JInvokeStmt statement;

	/**
	 * Unique identifier of the initializer
	 */
	private final int uniqueNumber;

	/**
	 * first argument in the constructor
	 */
	public final int trolley_size;

	/**
	 * second argument in the constructor
	 */
	public final int reserve_size;


	/**
	 * 
	 * @param statement    piece of code running the initializer
	 * @param uniqueNumber unique identifier of the initializer
	 * @param argment      argument in the constructor
	 */
	public StoreInitializer(JInvokeStmt statement, int uniqueNumber, int trolley_size, int reserve_size) {
		this.statement = statement;
		this.uniqueNumber = uniqueNumber;
		this.trolley_size = trolley_size;
		this.reserve_size = reserve_size;
	}

	/**
	 * 
	 * @return piece of code running the initializer
	 */
	public JInvokeStmt getStatement() {
		return statement;
	}

	/**
	 * 
	 * @return unique identifier of the initializer
	 */
	private int getUniqueNumber() {
		return this.uniqueNumber;
	}

	/**
	 * 
	 * @return unique label of this initializer
	 */
	public String getUniqueLabel() {
		return "AbstractObject" + this.getUniqueNumber() + ".end";
	}

	public String toString() {
		return "AbstractObject" + this.getUniqueNumber();
	}

	public int getNumber(){
		return this.uniqueNumber;
	}


}