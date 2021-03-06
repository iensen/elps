/* Generated By:JJTree: Do not edit this line. ASTmultiplicativeArithmeticTerm.java Version 4.3 */
/* JavaCCOptions:MULTI=true,NODE_USES_PARSER=false,VISITOR=true,TRACK_TOKENS=false,NODE_PREFIX=AST,NODE_EXTENDS=,NODE_FACTORY=,SUPPORT_CLASS_VISIBILITY_PUBLIC=true */
package parser;
/**
 * Class for representing an abstract syntax tree node of a multiplicative term
 * @author Evgenii
 *
 */
public
class ASTmultiplicativeArithmeticTerm extends SimpleNode {
  public ASTmultiplicativeArithmeticTerm(int id) {
    super(id);
  }

  /**
   * Standard JAVACC AST node constructor
   * @param p
   * @param id
   */
  public ASTmultiplicativeArithmeticTerm(ElpsTranslator p, int id) {
    super(p, id);
  }



  /**
   * Return the string representation of the term
   * @param useOriginalImage must be set to true if the original strings 
   * (returned by ElpsTranslator) should be used
   */
	
  public String toString(boolean useOriginalImages) {
	  String result="";
	  for(int i=0;i<this.jjtGetNumChildren();i++) {
		if(i!=0) {
			result +=image.charAt(i-1);
		}
		result+=((SimpleNode)(this.jjtGetChild(i))).toString(useOriginalImages);
	  }
	  return result;
  }
  
  /**
   * String representation of the term
   */
  public String toString() {
	  return toString(false);
  }
}
/* JavaCC - OriginalChecksum=f21cc8998855598aedb30cd5d044a91f (do not edit this line) */
