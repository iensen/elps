package parser;
public class ASTpredSymbol extends SimpleNode {

	public boolean negative = false;
	public boolean hasPoundSign = false;
	String translatedImage = null;
	public int subj = 0;
	public boolean negatedSubj;

	public ASTpredSymbol(int id) {
		super(id);
	}

	public ASTpredSymbol(ElpsTranslator p, int id) {
		super(p, id);
	}

	public void setPoundSign(boolean p) {
		this.hasPoundSign = p;
	}

	public boolean hasPoundSign() {
		return hasPoundSign;
	}



	public void setTranslatedImage(String image) {
		this.translatedImage = image;
	}

	public String toString() {
		StringBuilder result = new StringBuilder();
		if (negative) {
			result.append("-");
		}
		if (translatedImage != null) {
			result.append(translatedImage);
		} else {
			result.append(image);
		}

		return result.toString();
	}
}