package ch.ethz.rse.verify;

import java.util.Collection;
import java.util.LinkedList;
import java.util.List;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import apron.MpqScalar;
import apron.Texpr1CstNode;
import apron.Texpr1Node;
import apron.Texpr1VarNode;
import ch.ethz.rse.VerificationProperty;
import ch.ethz.rse.numerical.NumericalAnalysis;
import ch.ethz.rse.numerical.NumericalStateWrapper;
import ch.ethz.rse.pointer.StoreInitializer;
import ch.ethz.rse.pointer.PointsToInitializer;
import ch.ethz.rse.utils.Constants;
import polyglot.ast.Call;
import soot.Local;
import soot.SootClass;
import soot.SootHelper;
import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.jimple.internal.JInvokeStmt;
import soot.jimple.internal.JSpecialInvokeExpr;
import soot.jimple.internal.JVirtualInvokeExpr;
import soot.toolkits.graph.UnitGraph;

/**
 * Main class handling verification
 * 
 */
public class Verifier extends AVerifier {

	private static final Logger logger = LoggerFactory.getLogger(Verifier.class);

	/**
	 * class to be verified
	 */
	private final SootClass c;

	/**
	 * points to analysis for verified class
	 */
	private final PointsToInitializer pointsTo;

	// All the analyses for one program
	private List<NumericalAnalysis> analyses = new LinkedList<>();

	/**
	 * 
	 * @param c class to verify
	 */
	public Verifier(SootClass c) {
		logger.debug("Analyzing {}", c.getName());

		this.c = c;

		// pointer analysis
		this.pointsTo = new PointsToInitializer(this.c);
	}

	protected void runNumericalAnalysis(VerificationProperty property) {
		// TODO: Tried -  FILL THIS OUT
		List<SootMethod> methods = c.getMethods();
		for(SootMethod method : methods){
			if(method.getName().contains("<init>")){
				continue;
			}
			NumericalAnalysis a = new NumericalAnalysis(method, property, pointsTo);
			analyses.add(a);
		}
	}

	@Override
	public boolean checksNonNegative() {
		boolean property = true;
		for(NumericalAnalysis a : analyses){
			property = property && a.nonNegativeResult;
		}

		return property;
	}

	@Override
	public boolean checkFitsInTrolley() {
		boolean property = true;
		for(NumericalAnalysis a : analyses){
			property = property && a.fitsInTrolley;
		}
		return property;
	}

	@Override
	public boolean checkFitsInReserve() {
		boolean property = true;
		for(NumericalAnalysis a : analyses){
			property = property && a.fitsInReserve;
		}
		return property;
	}

	// TODO: MAYBE FILL THIS OUT: add convenience methods

}
