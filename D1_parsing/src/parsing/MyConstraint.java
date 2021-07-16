package parsing;


import org.eclipse.xtext.xbase.lib.Pair;

import tau.smlab.syntech.gameinput.model.Constraint;
import tau.smlab.syntech.gameinput.spec.*;

public class MyConstraint {

	private String name;
	private String LTLProp;
	
	public MyConstraint(Constraint cons, String clockKind, int propertyNumber) {
		if (cons.isInitial()) {
			buildInitial(cons.getSpec(), clockKind);
		} else if (cons.isSafety()) {
			buildSafety(cons.getSpec(), clockKind, propertyNumber);
		} else if (cons.isJustice()) {
			buildJustice(cons.getSpec(), clockKind, propertyNumber);
		} else {
			throw new Error("we neec to translate a new type of constraint");
		}
	}

	public Pair<String, String> subParse(Spec spec) {
		String name = "";
		String LTLProp = "";
		if(spec instanceof VariableReference) {
			VariableReference varRef = (VariableReference) spec;
			name = varRef.getReferenceName();
			LTLProp = varRef.getReferenceName().toUpperCase();
		} else if(spec instanceof SpecExp) {
			SpecExp specification = (SpecExp) spec;
			if(specification.getOperator().equals(Operator.EQUALS)) {
				VariableReference left = (VariableReference) specification.getChildren()[0]; 
				name = left.getReferenceName();
				LTLProp = subParse(specification.getChildren()[1]).getValue(); //only "right", not "left=right" because we have fluents, not variables in MTSA
			} else if(specification.getOperator().equals(Operator.NOT)) {
				Pair<String, String> answer = subParse(specification.getChildren()[0]);
				name = answer.getKey();
				LTLProp = "!"+answer.getValue();
			} else if(specification.getOperator().equals(Operator.IMPLIES)) {
				Pair<String, String> left = subParse(specification.getChildren()[0]);
				name = left.getKey();
				Pair<String, String> right = subParse(specification.getChildren()[1]);
				LTLProp = left.getValue() + " -> " + right.getValue();
			} else {
				throw new Error("new kind of SpecExp");
			}
		} else if (spec instanceof PrimitiveValue) {
			PrimitiveValue val = (PrimitiveValue) spec;
			name = val.getValue();
			LTLProp = val.getValue();
		} else {
			throw new Error("we need another type of Spec to parse");
		}		
		return new Pair<String, String>(name, "("+LTLProp+")");
	}
	
	private void buildJustice(Spec toParse, String clockKind, Integer propertyNumber) {
		Pair<String, String> answer = subParse(toParse);
		this.name = clockKind == "tock" ? "A_l" : "G_l";
		this.name = this.name + propertyNumber.toString();
		this.LTLProp = "(" + clockKind + " && " +answer.getValue()+")";
	}
	
	private void buildSafety(Spec toParse, String clockKind, Integer propertyNumber) {
		Pair<String, String> answer = subParse(toParse);
		this.name = clockKind == "tock" ? "A" : "G";
		this.name = this.name + propertyNumber.toString();
		this.LTLProp = "[](" + clockKind + " -> " +answer.getValue()+")";
	}
	
	private void buildInitial(Spec toParse, String clockKind) {
		Pair<String, String> answer = subParse(toParse);
		this.name = answer.getKey();
		this.LTLProp = "(!"+clockKind+" W ("+clockKind+" && "+answer.getValue()+"))";
	}
	
	public String getLTLProp() {
		return LTLProp;
	}

	public String getName() {
		return name;
	}
}
