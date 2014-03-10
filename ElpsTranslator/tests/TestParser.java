package tests;

import org.junit.Test;

import parser.ParseException;
import parser.ElpsTranslator;


import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.Reader;



public class TestParser {
 @Test 
 public void testAggregatesAndChoices() throws ParseException
 {	
		testFile("test/choices_and_aggregates.sp");  
 }
 
 @Test 
 public void testMysteryPuzzle() throws ParseException
 {	
	testFile("test/mys.sp");  
 }
 
 @Test public void testHamiltonPath() throws ParseException
 {
	
	testFile("test/ham.sp");
	  
 }
 
 @Test public void testSudoku() throws ParseException
 {
	
	testFile("test/sudoku.sp");
	  
 }
 
 @Test public void testUsaSmart() throws ParseException
 {
	
	testFile("test/usa.sp");
	  
 }
 private void testFile(String filePath) throws ParseException
 {
	  Reader sr = null;
	  try {  
	        sr = new FileReader(filePath);
	  } catch (FileNotFoundException e) {
	        e.printStackTrace();
	  }
	  ElpsTranslator p= new ElpsTranslator(sr);
	  p.program();
 }

 
}
