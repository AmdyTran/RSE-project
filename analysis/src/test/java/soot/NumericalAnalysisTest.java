package soot;

import java.util.List;


import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

import ch.ethz.rse.VerificationProperty;
import ch.ethz.rse.testing.VerificationTestCase;
import ch.ethz.rse.verify.ClassToVerify;
import soot.util.Chain;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import ch.ethz.rse.pointer.PointsToInitializer;
import ch.ethz.rse.numerical.NumericalAnalysis;


public class NumericalAnalysisTest{
	private static final Logger logger = LoggerFactory.getLogger(NumericalAnalysisTest.class);

    PointsToInitializer  pointsTo;
	
	//private static final Logger logger = LoggerFactory.getLogger(NumericalAnalysisTest.class);
	//private static Logger log = Logger.getLogger(LoggingObject.class);


    public ClassToVerify getExampleClassToVerify() {
		String packageName = "ch.ethz.rse.integration.tests.My_Test";
		VerificationTestCase c = new VerificationTestCase(packageName, VerificationProperty.NON_NEGATIVE, false);
		return c.getTestClass();
	}
	@Test
	public void testInit() {
		ClassToVerify c = this.getExampleClassToVerify();
		SootClass sc = SootHelper.loadClassAndAnalyze(c);


		// extract methods
		List<SootMethod> methods = sc.getMethods();

		SootMethod method1 = methods.get(1);
		logger.debug("we have a logger here");

		Chain<Local> locals = method1.retrieveActiveBody().getLocals();
		for(Local loc : locals){
			logger.debug("local: " + loc.getName());
		}


		
		// expect both init method and m1
		Assertions.assertEquals(2, methods.size());
		//Assertions.assertEquals("", methods.get(2));


        PointsToInitializer pt = new PointsToInitializer(sc);
        //check all methods of package
        for(int i=0; i<methods.size(); i++){
            //NumericalAnalysis numAn = new NumericalAnalysis(methods.get(i), VerificationProperty.NON_NEGATIVE, pt);
        }

		NumericalAnalysis numAn = new NumericalAnalysis(methods.get(1), VerificationProperty.NON_NEGATIVE, pt);
        

	}



}
