package parser;

public class ArrayUtils {
	
   public static String[] removeNthElement (String [] elements,int n) {
	   String [] newElements=new String[elements.length-1];
	   int shift=0;
	   for(int i=0;i<elements.length;i++) {
		   if(i==n) {
			   shift=1;
		   }
		   else {
			   newElements[i-shift]=elements[i];
		   }
	   }
	   return newElements;
   }
}
