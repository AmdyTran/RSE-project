package ch.ethz.rse.numerical;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import apron.*;
import apron.Abstract1;
import apron.ApronException;
import apron.Environment;
import apron.Manager;
import apron.MpqScalar;
import apron.Polka;
import apron.Tcons1;
import apron.Texpr1BinNode;
import apron.Texpr1CstNode;
import apron.Texpr1Intern;
import apron.Texpr1Node;
import apron.Texpr1VarNode;
import ch.ethz.rse.VerificationProperty;
import ch.ethz.rse.pointer.StoreInitializer;
import ch.ethz.rse.pointer.PointsToInitializer;
import ch.ethz.rse.utils.Constants;
import ch.ethz.rse.verify.EnvironmentGenerator;
import ch.ethz.rse.verify.StoreInit;
import gmp.Mpq;
import soot.ArrayType;
import soot.DoubleType;
import soot.Local;
import soot.RefType;
import soot.SootHelper;
import soot.SootMethod;
import soot.SootMethodRef;
import soot.Unit;
import soot.Value;
import soot.ValueBox;
import soot.jimple.AddExpr;
import soot.jimple.BinopExpr;
import soot.jimple.ConditionExpr;
import soot.jimple.DefinitionStmt;
import soot.jimple.IfStmt;
import soot.jimple.IntConstant;
import soot.jimple.InvokeExpr;
import soot.jimple.Jimple;
import soot.jimple.MulExpr;
import soot.jimple.ParameterRef;
import soot.jimple.Stmt;
import soot.jimple.SubExpr;
import soot.jimple.internal.AbstractBinopExpr;
import soot.jimple.internal.JAddExpr;
import soot.jimple.internal.JArrayRef;
import soot.jimple.internal.JAssignStmt;
import soot.jimple.internal.JEqExpr;
import soot.jimple.internal.JGeExpr;
import soot.jimple.internal.JGotoStmt;
import soot.jimple.internal.JGtExpr;
import soot.jimple.internal.JIfStmt;
import soot.jimple.internal.JInstanceFieldRef;
import soot.jimple.internal.JInvokeStmt;
import soot.jimple.internal.JLeExpr;
import soot.jimple.internal.JLtExpr;
import soot.jimple.internal.JMulExpr;
import soot.jimple.internal.JNeExpr;
import soot.jimple.internal.JReturnVoidStmt;
import soot.jimple.internal.JSpecialInvokeExpr;
import soot.jimple.internal.JSubExpr;
import soot.jimple.internal.JVirtualInvokeExpr;
import soot.jimple.internal.JimpleLocal;
import soot.jimple.toolkits.annotation.logic.Loop;
import soot.toolkits.graph.LoopNestTree;
import soot.toolkits.graph.UnitGraph;
import soot.toolkits.scalar.ForwardBranchedFlowAnalysis;

/**
 * Convenience class running a numerical analysis on a given {@link SootMethod}
 */
public class NumericalAnalysis extends ForwardBranchedFlowAnalysis<NumericalStateWrapper> {

	private static final Logger logger = LoggerFactory.getLogger(NumericalAnalysis.class);

	private final SootMethod method;

	/**
	 * the property we are verifying
	 */
	private final VerificationProperty property;

	/**
	 * the pointer analysis result we are verifying
	 */
	private final PointsToInitializer pointsTo;

	/**
	 * all store initializers encountered until now
	 */
	private Set<StoreInitializer> alreadyInit;


	/**
	 * Hashmap between store and reservesize currently left
	 */

	public HashMap<String, Interval> storageStore = new HashMap<String, Interval>();

	/**
	 * number of times this loop head was encountered during analysis
	 */
	private HashMap<Unit, IntegerWrapper> loopHeads = new HashMap<Unit, IntegerWrapper>();
	/**
	 * Previously seen abstract state for each loop head
	 */
	private HashMap<Unit, NumericalStateWrapper> loopHeadState = new HashMap<Unit, NumericalStateWrapper>();

	/**
	 * Numerical abstract domain to use for analysis: Convex polyhedra
	 */
	public final Manager man = new Polka(true);

	public final Environment env;

	/**
	 * We apply widening after updating the state at a given merge point for the
	 * {@link WIDENING_THRESHOLD}th time
	 */
	private static final int WIDENING_THRESHOLD = 6;


	// Verification Property result
	public boolean nonNegativeResult = true;
	public boolean fitsInTrolley = true;
	public boolean fitsInReserve = true;

	/**
	 * 
	 * @param method   method to analyze
	 * @param property the property we are verifying
	 */
	public NumericalAnalysis(SootMethod method, VerificationProperty property, PointsToInitializer pointsTo) {
		super(SootHelper.getUnitGraph(method));

		UnitGraph g = SootHelper.getUnitGraph(method);

		this.property = property;

		this.pointsTo = pointsTo;
		
		this.method = method;

		this.alreadyInit = new HashSet<StoreInitializer>();

		this.env = new EnvironmentGenerator(method, pointsTo).getEnvironment();

		// initialize counts for loop heads
		for (Loop l : new LoopNestTree(g.getBody())) {
			loopHeads.put(l.getHead(), new IntegerWrapper(0));
		}

		// perform analysis by calling into super-class
		logger.info("Analyzing {} in {}", method.getName(), method.getDeclaringClass().getName());
		// TODO: remove comment below - testing RIGHT NOW
		doAnalysis(); // calls newInitialFlow, entryInitialFlow, merge, flowThrough, and stops when a fixed point is reached
	}

	/**
	 * Report unhandled instructions, types, cases, etc.
	 * 
	 * @param task description of current task
	 * @param what
	 */
	public static void unhandled(String task, Object what, boolean raiseException) {
		String description = task + ": Can't handle " + what.toString() + " of type " + what.getClass().getName();

		if (raiseException) {
			logger.error("Raising exception " + description);
			throw new UnsupportedOperationException(description);
		} else {
			logger.error(description);

			// print stack trace
			StackTraceElement[] stackTrace = Thread.currentThread().getStackTrace();
			for (int i = 1; i < stackTrace.length; i++) {
				logger.error(stackTrace[i].toString());
			}
		}
	}

	@Override
	protected void copy(NumericalStateWrapper source, NumericalStateWrapper dest) {
		source.copyInto(dest);
	}

	@Override
	protected NumericalStateWrapper newInitialFlow() {
		// should be bottom (only entry flows are not bottom originally)
		return NumericalStateWrapper.bottom(man, env);
	}

	@Override
	protected NumericalStateWrapper entryInitialFlow() {
		// state of entry points into function
		NumericalStateWrapper ret = NumericalStateWrapper.top(man, env);

		// TODO: MAYBE FILL THIS OUT

		return ret;
	}

	@Override
	protected void merge(Unit succNode, NumericalStateWrapper w1, NumericalStateWrapper w2, NumericalStateWrapper w3) {
		// merge the two states from w1 and w2 and store the result into w3
		logger.debug("Merging NSW w1, w2, and putting into w3");
		if (!loopHeads.containsKey(succNode)){
			loopHeads.put(succNode, new IntegerWrapper(0));
		}

		IntegerWrapper count = loopHeads.get(succNode);
		count.value++;

		try {
			Abstract1 approximation = w1.get().joinCopy(man, w2.get());
			if (count.value >= WIDENING_THRESHOLD) {  // Apply widening
				logger.info("Widening is applied");
				w3.set(loopHeadState.get(succNode).get().widening(man, approximation));
			} else { 
				w3.set(approximation);
				loopHeadState.put(succNode, new NumericalStateWrapper(man, approximation));
			}
		} catch (ApronException e) {
			e.printStackTrace();
		}
		
	}

	
	@Override
	protected void merge(NumericalStateWrapper src1, NumericalStateWrapper src2, NumericalStateWrapper trg) {
		// this method is never called, we are using the other merge instead
		throw new UnsupportedOperationException();
	}

	@Override
	protected void flowThrough(NumericalStateWrapper inWrapper, Unit op, List<NumericalStateWrapper> fallOutWrappers,
			List<NumericalStateWrapper> branchOutWrappers) {
		logger.debug(inWrapper + " " + op + " => ?");

		Stmt s = (Stmt) op;

		// fallOutWrapper is the wrapper for the state after running op,
		// assuming we move to the next statement. Do not overwrite
		// fallOutWrapper, but use its .set method instead
		assert fallOutWrappers.size() <= 1;
		NumericalStateWrapper fallOutWrapper = null;
		if (fallOutWrappers.size() == 1) {
			fallOutWrapper = fallOutWrappers.get(0);
			inWrapper.copyInto(fallOutWrapper);
		}

		// branchOutWrapper is the wrapper for the state after running op,
		// assuming we follow a conditional jump. It is therefore only relevant
		// if op is a conditional jump. In this case, (i) fallOutWrapper
		// contains the state after "falling out" of the statement, i.e., if the
		// condition is false, and (ii) branchOutWrapper contains the state
		// after "branching out" of the statement, i.e., if the condition is
		// true.
		assert branchOutWrappers.size() <= 1;
		NumericalStateWrapper branchOutWrapper = null;
		if (branchOutWrappers.size() == 1) {
			branchOutWrapper = branchOutWrappers.get(0);
			inWrapper.copyInto(branchOutWrapper);
		}

		try {
			// Get class of s and log it
			String className = s.getClass().getName();
			logger.debug("Class of s: " + className);
			if (s instanceof DefinitionStmt) {
				// handle assignment

				DefinitionStmt sd = (DefinitionStmt) s;
				Value left = sd.getLeftOp();
				Value right = sd.getRightOp();

				// We are not handling these cases:
				if (!(left instanceof JimpleLocal)) {
					unhandled("Assignment to non-local variable", left, true);
				} else if (left instanceof JArrayRef) {
					unhandled("Assignment to a non-local array variable", left, true);
				} else if (left.getType() instanceof ArrayType) {
					unhandled("Assignment to Array", left, true);
				} else if (left.getType() instanceof DoubleType) {
					unhandled("Assignment to double", left, true);
				} else if (left instanceof JInstanceFieldRef) {
					unhandled("Assignment to field", left, true);
				}

				if (left.getType() instanceof RefType) {
					// assignments to references are handled by pointer analysis
					// no action necessary
				} else {
					// handle assignment
					handleDef(fallOutWrapper, left, right);
				}

			} else if (s instanceof JIfStmt) {
				// handle if

				// TODO: FILL THIS OUT
				// TODO: I tried it out
				

				logger.info("We have an JIFStmt " + s);
				logger.info("Branchout was " + branchOutWrapper);
				logger.info("Fallout was " + fallOutWrapper);
				JIfStmt sJif = (JIfStmt) s;
				Value c = sJif.getCondition();
				ConditionExpr condition = (ConditionExpr) c;

				// Get class of c and log it
				String classNameC = c.getClass().getName();
				logger.debug("Class of c: " + classNameC);

				Lincons1 consBranchout = null; // We branchout when the condition holds
				Lincons1 consFallout = null; // We fallout when the condition doesn't hold
				// Condition must be of type, JEqExpr, JGeExpr, JGtExpr, JLeExpr, JLtExpr, JNeExpr

				if (condition instanceof JEqExpr){
					consBranchout = linconsGen(condition, "EQ");
					consFallout = linconsGen(condition, "NE");
				}
				else if(condition instanceof JGeExpr){
					consBranchout = linconsGen(condition, "GEQ");
					consFallout = linconsGen(condition, "L");
					logger.info("Consbranchout is " + consBranchout);
					logger.info("Consfallout is " + consFallout);
				}
				else if(condition instanceof JGtExpr){
					consBranchout = linconsGen(condition, "G");
					consFallout = linconsGen(condition, "LEQ");
				}
				else if(condition instanceof JLeExpr){
					consBranchout = linconsGen(condition, "LEQ");
					consFallout = linconsGen(condition, "G");
				}
				else if(condition instanceof JLtExpr){

					logger.info("We have a JLEExpr");
					consBranchout = linconsGen(condition, "L");
					consFallout = linconsGen(condition, "GEQ");
				}
				else if(condition instanceof JNeExpr){
					consBranchout = linconsGen(condition, "NEQ");
					consFallout = linconsGen(condition, "EQ");

				}
				else{
					unhandled("Unhandled condition", condition, true);
				}	
				branchOutWrapper.set(branchOutWrapper.get().meetCopy(man, consBranchout));
				fallOutWrapper.set(fallOutWrapper.get().meetCopy(man, consFallout));

				logger.info("Branchout is now" + branchOutWrapper.toString());
				logger.info("Fallout is now" + fallOutWrapper.toString());

				


			} else if (s instanceof JInvokeStmt) {
				// handle invocations
				JInvokeStmt jInvStmt = (JInvokeStmt) s;
				InvokeExpr invokeExpr = jInvStmt.getInvokeExpr();
				if (invokeExpr instanceof JVirtualInvokeExpr) {
					// Call of get_delivery
					handleInvoke(jInvStmt, fallOutWrapper);
				} else if (invokeExpr instanceof JSpecialInvokeExpr) {
					// initializer for object
					// call of initialize new store
					handleInitialize(jInvStmt, fallOutWrapper);
				} else {
					unhandled("Unhandled invoke statement", invokeExpr, true);
				}
			} else if (s instanceof JGotoStmt) {
				// safe to ignore
			} else if (s instanceof JReturnVoidStmt) {
				// safe to ignore
			} else {
				unhandled("Unhandled statement", s, true);
			}

			// log outcome
			if (fallOutWrapper != null) {
				logger.debug(inWrapper.get() + " " + s + " =>[fallout] " + fallOutWrapper);
			}
			if (branchOutWrapper != null) {
				logger.debug(inWrapper.get() + " " + s + " =>[branchout] " + branchOutWrapper);
			}

		} catch (ApronException e) {
			throw new RuntimeException(e);
		}
	}

	public void handleInvoke(JInvokeStmt jInvStmt, NumericalStateWrapper fallOutWrapper) throws ApronException {
		// TODO: MAYBE FILL THIS OUT
		logger.info("We are in handleInvoke, jInvStmt is " + jInvStmt); // we are doing getDelivery
		// log JInvokeStmt
		loopHeadState.put(jInvStmt, fallOutWrapper);
		InvokeExpr invExpr = jInvStmt.getInvokeExpr();
		logger.info("invExpr: " + invExpr); 
		Value arg1 = invExpr.getArg(0); 
		logger.info("(The size we call, or rather put in) arg1: " + arg1);

		// We need the storeName
		Value storeName = invExpr.getUseBoxes().get(1).getValue();
		Abstract1 out = fallOutWrapper.get();

		// Two cases of arg1, either its IntConstant or JimpleLocal
		Interval bounds = getInterval(arg1, out);


		
		Collection<StoreInitializer> storeInitializers = pointsTo.getInitializers(method);
		logger.info("Out wasz : " + out);

		//We have a case of Subtract, because we subtract it from the reserve size:
		for(StoreInitializer store : storeInitializers){
			if(storeName.hashCode() == store.getNumber()){
				Texpr1Node texpr = new Texpr1VarNode(store.getUniqueLabel());
				Texpr1Node sub = valTexpr1Node(arg1);
				Texpr1Node res = new Texpr1BinNode(Texpr1BinNode.OP_SUB, texpr, sub);
				out.assign(man, store.getUniqueLabel(), new Texpr1Intern(env, res), null);
			}
		}

		logger.info("Out is now: " + out);
		

		if(this.property == VerificationProperty.NON_NEGATIVE){
			logger.info("Verification: NON_NEGATIVE?");
			if(bounds.inf().cmp(0) == -1){
				nonNegativeResult = false;
				logger.info("Non negative property is: " + nonNegativeResult);
			}
		}
		
		if(this.property == VerificationProperty.FITS_IN_TROLLEY){
			for(StoreInitializer store : storeInitializers){
				if(storeName.hashCode() == store.getNumber()){
					logger.info("Trolley size is " + store.trolley_size + " and our bounds are " + bounds);
					if(bounds.sup().cmp(store.trolley_size) == 1) fitsInTrolley = false;
				}
			}
		}
		if(this.property == VerificationProperty.FITS_IN_RESERVE){
			for(StoreInitializer store : storeInitializers){
				if(storeName.hashCode() == store.getNumber()){
					Interval i = out.getBound(man, store.getUniqueLabel());
					if(i.sup().cmp(0) == -1){
						fitsInReserve = false;
						logger.info("Doesnt fit in reserve");
					} 
				}
			}

		}
		


	}

	public void handleInitialize(JInvokeStmt jInvStmt, NumericalStateWrapper fallOutWrapper) throws ApronException {
		logger.info("We are in handleInitialize: store gets created, save the reserve size");

		Abstract1 out = fallOutWrapper.get();
		logger.info("Out was: " + out);
		for(StoreInitializer si : pointsTo.getInitializers(method)){
			if(jInvStmt.equals(si.getStatement())){
				IntConstant a = IntConstant.v(si.reserve_size);
				logger.info("Intconstant a i s" + a);
				out.assign(man, si.getUniqueLabel(), new Texpr1Intern(env, valTexpr1Node(IntConstant.v(si.reserve_size))), null);
				
			}
		}
		logger.info("Out is now: " + out);
		
	}

	// returns state of in after assignment
	private void handleDef(NumericalStateWrapper outWrapper, Value left, Value right) throws ApronException {
		Abstract1 out = outWrapper.get();
		String leftName = left.toString();
		logger.info("We are in handleDef");
		logger.info("outWrapper.get() gives (beforeState): " + out);
		logger.info("leftName = rightName: " + left + " = " + right);

		// IntConstant or JimpleLocal:
		if(right instanceof IntConstant || right instanceof JimpleLocal){
			logger.info("Right is instanceOf IntConstant or JimpleLocal");
			Interval interval = getInterval(right, out);
			Abstract1 newAbs = new Abstract1(man, env, new String[]{leftName}, new Interval[]{interval});
			out.meet(man, newAbs);
		}
		
		// JMulExpr:
		else if(right instanceof JMulExpr){
			Texpr1Node leftNode = valTexpr1Node(((JMulExpr) right).getOp1());
			Texpr1Node rightNode = valTexpr1Node(((JMulExpr) right).getOp2());
			Texpr1Node res = new Texpr1BinNode(Texpr1BinNode.OP_MUL, leftNode, rightNode);
			out.assign(man, leftName, new Texpr1Intern(env, res), null);
			logger.info("New out is after add:" + out);
		}

		// JAddExpr:
		else if(right instanceof JAddExpr){
			logger.info("right is JAddExpr");
			Texpr1Node leftNode = valTexpr1Node(((JAddExpr) right).getOp1());
			Texpr1Node rightNode = valTexpr1Node(((JAddExpr) right).getOp2());
			Texpr1Node res = new Texpr1BinNode(Texpr1BinNode.OP_ADD, leftNode, rightNode);
			out.assign(man, leftName, new Texpr1Intern(env, res), null);
			logger.info("New out is after add:" + out);

		}
		
		// JSubExpr:
		else if(right instanceof JSubExpr){
			logger.info("right is Jsubexpr");
			Texpr1Node leftNode = valTexpr1Node(((JSubExpr) right).getOp1());
			Texpr1Node rightNode = valTexpr1Node(((JSubExpr) right).getOp2());
			Texpr1Node res = new Texpr1BinNode(Texpr1BinNode.OP_SUB, leftNode, rightNode);
			out.assign(man, leftName, new Texpr1Intern(env, res), null);
			logger.info("New out is after sub:" + out);
		}

		else{
			logger.error("Something is wrong with right, we don't have the instanceof");
		}


	}

	// TODO: MAYBE FILL THIS OUT: add convenience methods

	public Lincons1 linconsGen(ConditionExpr condition, String op){
		Lincons1 lincons = null;
		Linexpr1 linexpr1 = new Linexpr1(env);
		Value a = condition.getOp1();
		Value b = condition.getOp2();

		// Create the linexpr1 a - b
		if(op.equals("EQ") || op.equals("NEQ") || op.equals("GEQ") || op.equals("G")){
			if (a instanceof IntConstant){
				linexpr1.setCst(new MpqScalar(((IntConstant) a).value));
			}
			else{
				linexpr1.setCoeff(new StringVar(((JimpleLocal) a).getName()), new MpqScalar(1));
			}
	
			if (b instanceof IntConstant){
				linexpr1.setCst(new MpqScalar(-((IntConstant) b).value));
			}
			else{
				linexpr1.setCoeff(new StringVar(((JimpleLocal) b).getName()), new MpqScalar(-1));
			}
		}
		else{
			if (a instanceof IntConstant){
				linexpr1.setCst(new MpqScalar(-((IntConstant) a).value));
			}
			else{
				linexpr1.setCoeff(new StringVar(((JimpleLocal) a).getName()), new MpqScalar(-1));
			}
	
			if (b instanceof IntConstant){
				linexpr1.setCst(new MpqScalar(((IntConstant) b).value));
			}
			else{
				linexpr1.setCoeff(new StringVar(((JimpleLocal) b).getName()), new MpqScalar(1));
			}
		}

		if(op.equals("EQ")){
			lincons = new Lincons1(Lincons1.EQ, linexpr1);
		}
		else if (op.equals("NEQ")){
			lincons = new Lincons1(Lincons1.DISEQ, linexpr1);
		}
		else if (op.equals("GEQ") || op.equals("LEQ")){
			lincons = new Lincons1(Lincons1.SUPEQ, linexpr1);
		}
		else if (op.equals("G") || op.equals("L")){
			lincons = new Lincons1(Lincons1.SUP, linexpr1);
		}

		return lincons;
	}

	public Interval getInterval(Value value, Abstract1 abs){
		Interval interval = null;

		if(value instanceof IntConstant){
			interval = new Interval(((IntConstant) value).value, ((IntConstant) value).value);
		}

		if(value instanceof JimpleLocal){
			try {
				interval = abs.getBound(man, new StringVar(((JimpleLocal) value).getName()));
			} catch (ApronException e) {
				e.printStackTrace();
				throw new RuntimeException();
			}
		}

		return interval;
	}

	public Texpr1Node valTexpr1Node(Value value){
		Texpr1Node texpr = null;
		if(value instanceof IntConstant) texpr = new Texpr1CstNode(new MpqScalar(((IntConstant) value).value));
		if(value instanceof JimpleLocal) texpr = new Texpr1VarNode(((JimpleLocal) value).getName());
		return texpr;
	}
}
