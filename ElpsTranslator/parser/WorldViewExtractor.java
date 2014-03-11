package parser;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;

public class WorldViewExtractor {

	public ArrayList<ArrayList<AnswerSet>> extractWorldViews(ArrayList<AnswerSet> answerSets) {
		HashMap<HashSet<String>, ArrayList<AnswerSet>> groups = new HashMap<HashSet<String>, ArrayList<AnswerSet>>();

		String [] filterPrefixes = {"k0_","k1_","m0_","m1_"};
		String [] subjPrefixes = {"k0_","k1_","m0_","m1_", "m_","k_","-k0_","-k1_","-m0_","-m1_", "-m_","-k_"};

		for (AnswerSet answerSet : answerSets) {
			HashSet<String> prefixes = answerSet.filterByPrefix(filterPrefixes);
			if(!groups.containsKey(prefixes)) {
				groups.put(prefixes, new ArrayList<AnswerSet>());        			  
			}
			groups.get(prefixes).add(new AnswerSet(answerSet.removePrefixes(subjPrefixes)));
		}

		ArrayList<ArrayList<AnswerSet>> result = new ArrayList<ArrayList<AnswerSet>>();
		for (HashSet<String> subjGroup: groups.keySet()) {
			if(isValid(subjGroup, groups.get(subjGroup))) {
				result.add(groups.get(subjGroup));
			}
		}
		
		return result;
	}

	// Replace  0l with -l
	private String getASPLiteral(String lit) {
		if(lit.startsWith("0")) {
			return "-"+lit.substring(1);
		} else {
			return lit;
		}
	}

	private boolean isValid(HashSet<String> subjLiterals,ArrayList<AnswerSet> worldCandidate) {

		boolean isValid = true;

		// (a) if k1_l is in the sets of W, then l is in every set of W
		k1Loop: for(String subjLiteral: subjLiterals) {
			if(subjLiteral.startsWith("k1_")) {
				// then l is in every set of W
				String l = getASPLiteral(subjLiteral.substring(3));
				for(AnswerSet answerSet: worldCandidate) {
					if(!answerSet.atoms.contains(l)) {
						isValid = false;
						break k1Loop;
					}
				}
			}
		}

		if(!isValid)
			return false;

		// (b) if k0_l' is in the sets of W, then l is missing from at least one of the set of W

		for(String subjLiteral: subjLiterals) {

			if(subjLiteral.startsWith("k0_")) {
				isValid = false;
				// then l is in every set of W
				String l = getASPLiteral(subjLiteral.substring(3));
				for(AnswerSet answerSet: worldCandidate) {
					if(!answerSet.atoms.contains(l)) {
						isValid = true;  
						break;
					}
				}

				if(!isValid) break;
			}
		}

		if(!isValid)
			return false;

		// (c) if m1_l is in the sets of W, then l is at least one set of W


		for(String subjLiteral: subjLiterals) {

			if(subjLiteral.startsWith("m1_")) {
				isValid = false;
				// then l is in every set of W
				String l = getASPLiteral(subjLiteral.substring(3));
				for(AnswerSet answerSet: worldCandidate) {
					if(answerSet.atoms.contains(l)) {
						isValid = true;  
						break;
					}
				}

				if(!isValid) break;
			}
		}

		if(!isValid)
			return false;

		// (d) if m0_l' is in the sets of W , then l is missing from every set of W

		m0Loop: for(String subjLiteral: subjLiterals) {
			if(subjLiteral.startsWith("m0_")) {
				// then l is in every set of W
				String l = getASPLiteral(subjLiteral.substring(3));
				for(AnswerSet answerSet: worldCandidate) {
					if(answerSet.atoms.contains(l)) {
						isValid = false;
						break m0Loop;
					}
				}
			}
		}
		
		return isValid;
	}
}
