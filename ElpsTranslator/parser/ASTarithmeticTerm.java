/* Generated By:JJTree: Do not edit this line. ASTarithmeticTerm.java Version 4.3 */
/* JavaCCOptions:MULTI=true,NODE_USES_PARSER=false,VISITOR=true,TRACK_TOKENS=false,NODE_PREFIX=AST,NODE_EXTENDS=,NODE_FACTORY=,SUPPORT_CLASS_VISIBILITY_PUBLIC=true */
package parser;


/**
 * The class implements AST node for arithmetic terms
 * @author Evgenii Balai
 *
 */
public class ASTarithmeticTerm extends SimpleNode {
	public ASTarithmeticTerm(int id) {
		super(id);
	}
    
	/**
	 * Construct a term node from given constant value
	 * @param value
	 */
	public ASTarithmeticTerm(long value) {
		super(ElpsTranslatorTreeConstants.JJTARITHMETICTERM);
		this.jjtAddChild(new ASTadditiveArithmeticTerm(value), 0);
	}
	
	/**
	 * Standard JAVACC constructor
	 * @param p
	 * @param id
	 */
	public ASTarithmeticTerm(ElpsTranslator p, int id) {
		super(p, id);
	}




    /**
     * String representation of the term
     * @param useOriginalImage must be set to true if the original strings 
     * (returned by ElpsTranslator) should be used
     */
	public String toString(boolean useOriginalImages) {
		if(this.jjtGetNumChildren()==0) {
			return this.image;
		}
		return ((SimpleNode) (this.jjtGetChild(0))).toString(useOriginalImages);
	}
	
	/**
	 * String representation of the term
	 */
	public String toString() {
		return toString(false);
	}
	
	

}
/*
 * JavaCC - OriginalChecksum=39ed3c6f16ab9054babef12ef8f45fd6 (do not edit this
 * line)
 */
