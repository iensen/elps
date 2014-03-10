package sorts;

import java.util.HashMap;

import parser.ASTsetExpression;
import parser.ASTsortExpression;
import parser.SimpleNode;
import parser.ElpsTranslatorTreeConstants;

//TODO add comments
public class BasicSortChecker {
	public static boolean isBasic(ASTsortExpression se,
			HashMap<String, ASTsortExpression> sortNameToExpression) {
		int id = ((SimpleNode) se.jjtGetChild(0)).getId();
		switch (id) {
		case ElpsTranslatorTreeConstants.JJTNUMERICRANGE:
			return true;
		case ElpsTranslatorTreeConstants.JJTIDENTIFIERRANGE:
			return true;
		case ElpsTranslatorTreeConstants.JJTCONCATENATION:
			return true;
		case ElpsTranslatorTreeConstants.JJTSETEXPRESSION:
			return checkSetExpression((ASTsetExpression) se.jjtGetChild(0),
					sortNameToExpression);
		default:
			return false;
		}
	}

	private static boolean checkSetExpression(SimpleNode se,
			HashMap<String, ASTsortExpression> sortNameToExpression) {
		if (se.getId() == ElpsTranslatorTreeConstants.JJTSORTNAME) {
			return isBasic(sortNameToExpression.get(se.image),
					sortNameToExpression);
		}
		if (se.getId() == ElpsTranslatorTreeConstants.JJTCURLYBRACKETS) {
			return checkCurlyBrackets((SimpleNode) se);
		}
		boolean result = true;
		for (int i = 0; i < se.jjtGetNumChildren(); i++) {
			result = result
					& checkSetExpression((SimpleNode) se.jjtGetChild(i),
							sortNameToExpression);
		}
		return result;
	}

	private static boolean checkCurlyBrackets(SimpleNode se) {
		if (se.getId() == ElpsTranslatorTreeConstants.JJTCONSTANTTERM) {
			if (se.jjtGetNumChildren() == 1) {
				SimpleNode child = (SimpleNode) se.jjtGetChild(0);
				if (child.getId() == ElpsTranslatorTreeConstants.JJTCONSTANTTERMLIST) {
					return false;
				}
			}
			//if(se.jjtGetNumChildren()==0 && se.image.indexOf('_')!=-1)
			//	return false;
		}
		boolean result = true;
		for (int i = 0; i < se.jjtGetNumChildren(); i++) {
			result = result
					& checkCurlyBrackets((SimpleNode) se.jjtGetChild(i));
		}
		return result;
	}
}
