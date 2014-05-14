package tests;

import static org.junit.Assert.*;

import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.Reader;
import org.junit.Test;

import configuration.Settings;

import externaltools.DLVSolver;
import externaltools.ExternalSolver;

import parser.ASTprogram;
import parser.ASTprogramRules;
import parser.ParseException;
import parser.SimpleNode;
import parser.ElpsTranslator;
import translating.InstanceGenerator;
import translating.Translator;
import typechecking.TypeChecker;

public class TestError {

	@Test
	public void testError1() throws FileNotFoundException {
		assertEquals("Error message was wrong",
				getError("../test/errors/error1.sp"),
				"sort s at line 4 column 2 was already defined");
	}

	@Test
	public void testError2() throws FileNotFoundException {
		assertEquals("Error message was wrong",
				getError("../test/errors/error2.sp"),
				"sort s1 at line 3 column 5 was not defined");
	}

	@Test
	public void testError3() throws FileNotFoundException {
		assertEquals(
				"Error message was wrong",
				getError("../test/errors/error3.sp"),
				"ERROR: the first identifier in identifier range should be lexicographically smaller or equal to  the second one at line 3, column 4");
	}

	@Test
	public void testError4() throws FileNotFoundException {
		assertEquals("Error message was wrong",
				getError("../test/errors/error4.sp"),
				"ERROR: the first number in numeric  range should be smaller or equal to  the second one at line 3, column 7");
	}

	@Test
	public void testError5() throws FileNotFoundException {
		assertEquals("Error message was wrong",
				getError("../test/errors/error5.sp"),
				"ERROR: Constant 'c5' at line 3, column 7 was not defined");
	}

	@Test
	public void testError6() throws FileNotFoundException {
		assertEquals("Error message was wrong",
				getError("../test/errors/error6.sp"),
				"ERROR: the length of the first identifier in identifier range should be smaller or equal to the length of the second one at line 3, column 4");
	}

	@Test
	public void testError7() throws FileNotFoundException {
		assertEquals("Error message was wrong",
				getError("../test/errors/error7.sp"),
				"ERROR: Sort 's' at line 5, column 9 is not a basic sort");
	}

	@Test
	public void testError8() throws FileNotFoundException {
		assertEquals("Error message was wrong",
				getError("../test/errors/error9.sp"),
				"the definition of record f() at line 4 column 5 has a condition which involves checking less/greater relations on elements of non-basic sorts");
	}

	@Test
	public void testError9() throws FileNotFoundException {
		assertEquals("Error message was wrong",
				getError("../test/errors/error9.sp"),
				"the definition of record f() at line 4 column 5 has a condition which involves checking less/greater relations on elements of non-basic sorts");
	}

	@Test
	public void testError10() throws FileNotFoundException {
		assertEquals("Error message was wrong",
				getError("../test/errors/error10.sp"),
				"variable X at line 4, column 16 is used more than once in record definition");
	}

	@Test
	public void testError11() throws FileNotFoundException {
		assertEquals("Error message was wrong",
				getError("../test/errors/error11.sp"),
				"sort s1 defined at line 5 column 2 is empty");
	}

	@Test
	public void testError12() throws FileNotFoundException {
		assertEquals("Error message was wrong",
				getError("../test/errors/error12.sp"),
				"Line 6, column 4: sort 's1' was not defined");
	}

	@Test
	public void testError13() throws FileNotFoundException {
		assertEquals("Error message was wrong",
				getError("../test/errors/error13.sp"),
				"Line 7, column 1: predicate p was already declared");
	}

	@Test
	public void testError14_1() throws FileNotFoundException {
		assertEquals("Error message was wrong",
				getError("../test/errors/error14(1).sp"),
				": argument number 1 of predicate p/1, \"7-3\", at line 8, column 1 violates definition of sort \"s\"");
	}

	@Test
	public void testError14_2() throws FileNotFoundException {
		assertEquals("Error message was wrong",
				getError("../test/errors/error14(2).sp"),
				": non-ground term \"g(X)\" occuring  in program as 1 argument of predicate p/1 at line 7, column 1 is not a program term");
	}

	@Test
	public void testError14_3() throws FileNotFoundException {
		assertEquals("Error message was wrong",
				getError("../test/errors/error14(3).sp"),
				": non-ground term \"f(X,c)\" occuring  in program as 1 argument of predicate p/1 at line 7, column 1 is not a program term");
	}

	@Test
	public void testError15() throws FileNotFoundException {
		assertEquals("Error message was wrong",
				getError("../test/errors/error15.sp"),
				": argument number 1 of predicate p/1, \"f(b)\", at line 8, column 1 violates definition of sort \"s\"");
	}

	@Test
	public void testError16() throws FileNotFoundException {
		assertEquals("Error message was wrong",
				getError("../test/errors/error16.sp"),
				": argument number 1 of predicate p/1, \"1*2\", at line 8, column 1 violates definition of sort \"s\"");
	}

	@Test
	public void testError17() throws FileNotFoundException {
		assertEquals("Error message was wrong",
				getError("../test/errors/error17.sp"),
				": argument number 1 of predicate p/1, \"X+1\", at line 8, column 1 is an arithmetic term and not a variable, but \"s\" does not contain a number");
	}

	@Test
	public void testErrorRange() throws FileNotFoundException {
		assertEquals("Error message was wrong",
				getError("../test/errors/errorRange.sp"),
				": Argument number 1 of predicate p/1, \"1..6\", at line 6, column 1 violates definition of sort \"s\"");
	}

	@Test
	public void testUnrestr() throws FileNotFoundException {
		assertEquals("Error message was wrong",
				getError("../test/errors/unrestr.sp"),
				"null: program rule p(f(X)):-Y<2,Z<2,F>3,#count{Q:Q<W,p(W),T<2},p(Y). at line 6, column 1 contains unrestricted global variables F,T,Z and unrestricted local variables Q");
	}

	private String getError(String filePath) throws FileNotFoundException {
		Reader sr = null;
		try {
			sr = new FileReader(filePath);
		} catch (FileNotFoundException e) {
			e.printStackTrace();
		}
		ElpsTranslator p = new ElpsTranslator(sr);
		try {
			SimpleNode e = p.program();
			InstanceGenerator gen = new InstanceGenerator(
					p.sortNameToExpression);
			TypeChecker tc = new TypeChecker(p.sortNameToExpression,
					p.predicateArgumentSorts, p.constantsMapping,
					p.curlyBracketTerms, p.definedRecordNames, gen);
			Translator tr = new Translator( p, gen, true, true);
			tc.checkRules((ASTprogramRules) e.jjtGetChild(2));
			StringBuilder translatedProgram = new StringBuilder();
			translatedProgram.append(tr.translateProgram((ASTprogram) e,
					p.generatingSorts, true));
			System.out.println(translatedProgram);
			ExternalSolver solver = new DLVSolver(translatedProgram.toString());
			Settings.getSingletonInstance().setOptions(" -n=1 ");
			System.out.println(solver.run(false));
		} catch (ParseException ex) {
			return ex.getMessage();
		}
		return null;
	}
}
