package parser;


import java.util.HashSet;


public class AnswerSet {
    public HashSet<String> atoms;
    public AnswerSet() {
        atoms=new HashSet<String>();
    }
    
    public AnswerSet(HashSet<String> atoms) {
    	this.atoms = atoms;
    }
    
    public HashSet<String> removePrefixes(String [] prefixes) {
    	@SuppressWarnings("unchecked")
		HashSet<String> result = (HashSet<String>)atoms.clone();
        result.removeAll(filterByPrefix(prefixes));
        return result;
    }
    
    public HashSet<String> filterByPrefix(String [] prefixes) {
    	HashSet<String> result = new HashSet<String> ();
    	for (String atom : atoms) {
    		boolean startsWithOKprefix = false;
    		for (String prefix : prefixes) {
    			if(atom.startsWith(prefix)) {
    				startsWithOKprefix = true;
    			}
    		}
    		if(startsWithOKprefix) {
    			result.add(atom);
    		}
    	}
    	return result;
    }
}