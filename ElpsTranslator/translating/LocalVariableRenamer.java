package translating;

import java.util.HashMap;
import java.util.HashSet;

import parser.ASTaggregateElement;
import parser.ASTchoice_element;
import parser.SimpleNode;
import parser.ElpsTranslatorTreeConstants;
/**
 * Class for renaming variables in program structures (aggregates,choice rules)
 *
 */
public class LocalVariableRenamer {

	HashSet<String> bodyVariables;

	public LocalVariableRenamer() {
		
	}

	public void setBodyVariables(HashSet<String> bodyVariables) {
		this.bodyVariables = bodyVariables;
	}

	public void renameLocalVariables(ASTchoice_element choice_element,int idx,HashMap<String,String> originalNamesMapping) {
		HashSet<String> localVariables = new HashSet<String>();
		for (int i = 0; i < choice_element.jjtGetNumChildren(); i++) {
			if (((SimpleNode) (choice_element.jjtGetChild(i))).getId() == ElpsTranslatorTreeConstants.JJTNONRELATOM) {
				localVariables
				.addAll(fetchVariableNames((SimpleNode) (choice_element
						.jjtGetChild(i))));
			}
		}
		// remove variable which do not occur in the body of the aggregate but occur in the body of the corresponding rule
		for(String var: bodyVariables) {
			// check if the variable does not occur in the body of the aggregate
			boolean varToRemove = true;
			for(int i=0;i<choice_element.jjtGetNumChildren();i++) {
				if (((SimpleNode) (choice_element.jjtGetChild(i))).getId() == ElpsTranslatorTreeConstants.JJTEXTENDEDSIMPLEATOMLIST) {
					if(fetchVariableNames((SimpleNode) (choice_element
							.jjtGetChild(i))).contains(var)) {
						varToRemove = false;
					}
				}
			}
			if(varToRemove) {
				localVariables.remove(var);
			}
		}
		renameLocalVariables(choice_element, "_L" + idx,
				localVariables,originalNamesMapping);

	}


	public void renameLocalVariables(ASTaggregateElement agrelem,int idx,HashMap<String,String> originalNamesMapping) {
		HashSet<String> localVariables = new HashSet<String>();
		for (int i = 0; i < agrelem.jjtGetNumChildren(); i++) {
			if (((SimpleNode) (agrelem.jjtGetChild(i))).getId() == ElpsTranslatorTreeConstants.JJTNONRELATOM
					|| ((SimpleNode) (agrelem.jjtGetChild(i))).getId() == ElpsTranslatorTreeConstants.JJTARITHMETICTERM) {
				localVariables.addAll(fetchVariableNames((SimpleNode) (agrelem
						.jjtGetChild(i))));
			}
		}

		// remove variable which do not occur in the body of the aggregate but occur in the body of the corresponding rule
		for(String var: bodyVariables) {
			// check if the variable does not occur in the body of the aggregate
			boolean varToRemove = true;
			for(int i=0;i<agrelem.jjtGetNumChildren();i++) {
				if (((SimpleNode) (agrelem.jjtGetChild(i))).getId() == ElpsTranslatorTreeConstants.JJTEXTENDEDSIMPLEATOMLIST) {
					if(fetchVariableNames((SimpleNode) (agrelem
							.jjtGetChild(i))).contains(var)) {
						varToRemove = false;
					}
				}
			}
			if(varToRemove) {
				localVariables.remove(var);
			}
		}

		renameLocalVariables(agrelem, "_L" + idx, localVariables,originalNamesMapping);
	}

	/**
	 * Rename all local variables in given AST subtree(n) by adding a suffix
	 * 
	 * @param n
	 *            AST subtree
	 * @param addSuffix
	 *            string to be appended to each local variable
	 * @param localVariables
	 *            set of local variables in given AST subtree to be renamed
	 */
	private void renameLocalVariables(SimpleNode n, String addSuffix,
			HashSet<String> localVariables,HashMap<String,String> originalNamesMapping) {
		if (n.getId() == ElpsTranslatorTreeConstants.JJTVAR
				&& localVariables.contains(n.image)) {
			originalNamesMapping.put(n.image+addSuffix,originalNamesMapping.get(n.image));
			n.image = n.image + addSuffix;

		}

		for (int i = 0; i < n.jjtGetNumChildren(); i++) {
			renameLocalVariables((SimpleNode) (n.jjtGetChild(i)), addSuffix,
					localVariables,originalNamesMapping);
		}
		if (n.getId() == ElpsTranslatorTreeConstants.JJTTERM) {
			originalNamesMapping.put(n.toString(false), n.toString(true));
		}
	}

	/**
	 * Fetch variables from given node
	 * 
	 * @param n
	 *            node to explore
	 * @return variable->sort_expression mapping, where sort expression
	 *         describes a language of string each of which may be used as a
	 *         substitution for given variable
	 */
	private HashSet<String> fetchVariableNames(SimpleNode n) {
		HashSet<String> result = new HashSet<String>();
		if (n.getId() == ElpsTranslatorTreeConstants.JJTVAR) {
			result.add(n.image);
		}
		for (int i = 0; i < n.jjtGetNumChildren(); i++) {
			result.addAll((fetchVariableNames((SimpleNode) (n.jjtGetChild(i)))));
		}
		return result;
	}

}
