package parser;

import java.util.ArrayList;


public abstract class AnswerSetParser {
    public abstract ArrayList<AnswerSet> getAnswerSets(String output);
}