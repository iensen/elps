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
	
	/**
	   * Copy fields and children, but not parent.
	   * @param that node to copy from
	   * @return this for convenience.
	   */
	  public SimpleNode copyFields(SimpleNode that) {
	      this.id = that.id;
	      this.parser = that.parser;
	      this.beginLine = that.beginLine;
	      this.beginColumn = that.beginColumn;
	  	  this.negative = ((ASTpredSymbol)that).negative;
		 this.hasPoundSign = ((ASTpredSymbol)that).hasPoundSign;;
	      if(that.image!=null)
	         this.image = new String(that.image);
	      if(that.children !=null) {    
	      this.children = new Node[that.children.length];
	      this.parent = that.parent;
	      for (int i=0; i<that.children.length; i++) {
	          this.children[i] =  ((SimpleNode)that.children[i]).deepCopy();
	      }
	      }
	      return this;
	  }
}