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

	public Pair<String, String> subParse(Spec spec, String clockKind) {
		String name = "";
		String LTLProp = "";
		if(spec instanceof VariableReference) {
			VariableReference varRef = (VariableReference) spec;
			name = makeVarName(varRef.getReferenceName());
			if(checkIfIsNextVar(varRef)) {
				name = name.substring(0, name.length()-1);
				LTLProp = "X(!" + clockKind + " W (" + clockKind + " && " + name + "))";
			}else {
				LTLProp = clockKind + " && " + name;
			}
		} else if(spec instanceof SpecExp) {
			SpecExp specification = (SpecExp) spec;
			if(specification.getOperator().equals(Operator.EQUALS)) {
				VariableReference left = (VariableReference) specification.getChildren()[0]; 
				name = makeVarName(left.getReferenceName());
				LTLProp = clockKind + " && " + subParse(specification.getChildren()[1], clockKind).getValue(); //only "right", not "left=right" because we have fluents, not variables in MTSA
			} else if(specification.getOperator().equals(Operator.NOT)) {
				Pair<String, String> answer = subParse(specification.getChildren()[0], clockKind);
				name = answer.getKey();
				LTLProp = clockKind + " && !" + answer.getKey();
			} else if(specification.getOperator().equals(Operator.IMPLIES)) {
				Pair<String, String> left = subParse(specification.getChildren()[0], clockKind);
				name = left.getKey();
				Pair<String, String> right = subParse(specification.getChildren()[1], clockKind);
				String leftVal;
				if (specification.getChildren()[0] instanceof VariableReference
						&& !checkIfIsNextVar((VariableReference) specification.getChildren()[0])) {
					leftVal = left.getKey();
				}else {
					leftVal = left.getValue();
				}
				String rightVal;
				if (specification.getChildren()[1] instanceof VariableReference
						&& !checkIfIsNextVar((VariableReference) specification.getChildren()[1])) {
					rightVal = right.getKey();
				}else {
					rightVal = right.getValue();
				}
				LTLProp = leftVal + " -> " + rightVal;
			} else if(specification.getOperator().equals(Operator.AND)) {
				Pair<String, String> left = subParse(specification.getChildren()[0], clockKind);
				name = left.getKey();
				Pair<String, String> right = subParse(specification.getChildren()[1], clockKind);
				//TODO abstraer lo que hice en el IMPLIES, de ver si es varRef el caso recursivo para agarrar key o value.
				LTLProp = clockKind + " && " + subParse(specification.getChildren()[1], clockKind).getValue();
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
		Pair<String, String> answer = subParse(toParse, clockKind);
		this.name = clockKind == "tock" ? "A_l" : "G_l";
		this.name = this.name + propertyNumber.toString();
		this.LTLProp = answer.getValue();
	}
	
	private void buildSafety(Spec toParse, String clockKind, Integer propertyNumber) {
		Pair<String, String> answer = subParse(toParse, clockKind);
		this.name = clockKind == "tock" ? "A" : "G";
		this.name = this.name + propertyNumber.toString();
		this.LTLProp = "[](" + clockKind + " -> " +answer.getValue()+")";
	}
	
	private void buildInitial(Spec toParse, String clockKind) {
		Pair<String, String> answer = subParse(toParse, clockKind);
		this.name = answer.getKey();
		this.LTLProp = "(!"+clockKind+" W "+answer.getValue()+")";
	}
	
	private boolean checkIfIsNextVar(VariableReference var) {
		//if VAR reference name ends with ', its actually NEXT(VAR).
		String auxName = var.getReferenceName();
		return auxName.charAt(auxName.length() - 1) == '\'';
	}
	
	private String makeVarName(String name) {
		return name.toUpperCase();
	}
	
	public String getLTLProp() {
		return LTLProp;
	}

	public String getName() {
		return name;
	}
}
