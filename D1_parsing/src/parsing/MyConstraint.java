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

	public String subParse(Spec spec, String clockKind) {
		if(spec instanceof VariableReference) {
			VariableReference varRef = (VariableReference) spec;
			name = makeVarName(varRef.getReferenceName());
			if(checkIfIsNextVar(varRef)) {
				name = name.substring(0, name.length()-1);
				return "X(!" + clockKind + " W (" + clockKind + " && " + name + "))";
			}else {
				return name;
			}
		} else if(spec instanceof SpecExp) {
			SpecExp specification = (SpecExp) spec;
			if(specification.getOperator().equals(Operator.EQUALS)) {
				return subParse(specification.getChildren()[1], clockKind); //only "right", not "left=right" because we have fluents, not variables in MTSA
			} else if(specification.getOperator().equals(Operator.NOT)) {
				String answer = subParse(specification.getChildren()[0], clockKind);
				return "!" + answer;
			} else if(specification.getOperator().equals(Operator.PRIME)) {
				String answer = subParse(specification.getChildren()[0], clockKind);
				return "X(!" + clockKind + " W (" + clockKind + " && " + answer + "))";
			} else {
				String left = subParse(specification.getChildren()[0], clockKind);
				String right = subParse(specification.getChildren()[1], clockKind);
				return "(" + left + MTSAOperator(specification.getOperator()) + right + ")";
			}
		} else if (spec instanceof PrimitiveValue) {
			PrimitiveValue val = (PrimitiveValue) spec;
			return val.getValue();
		} else {
			throw new Error("we need another type of Spec to parse");
		}		
	}
		
	public Pair<String, String> initialParse(Spec spec, String clockKind) {
		String name = ""; //only matters for varRefs, primitiveVals and operator NOT, since it's for initial constraints
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
				LTLProp = clockKind + " && " + subParse(specification.getChildren()[1], clockKind); //only "right", not "left=right" because we have fluents, not variables in MTSA
			} else if(specification.getOperator().equals(Operator.NOT)) {
				String answer = subParse(specification.getChildren()[0], clockKind);
				name = answer;
				LTLProp = clockKind + " && !" + answer;
			} else if(specification.getOperator().equals(Operator.PRIME)) {
				String answer = subParse(specification.getChildren()[0], clockKind);
				LTLProp = "X(!" + clockKind + " W (" + clockKind + " && " + answer + "))";
			} else {
				String left = subParse(specification.getChildren()[0], clockKind);
				String right = subParse(specification.getChildren()[1], clockKind);
				LTLProp = left + MTSAOperator(specification.getOperator()) + right;
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
	

	private String MTSAOperator(Operator op) {
		switch(op) {
			case IMPLIES:
				return " -> ";
			case AND:
				return " && ";
			case OR:
				return " || ";
			default:
				throw new Error("new kind of SpecExp");
		}
	}
	
	private void buildJustice(Spec toParse, String clockKind, Integer propertyNumber) {
		Pair<String, String> answer = initialParse(toParse, clockKind);
		this.name = clockKind == "tock" ? "A_l" : "G_l";
		this.name = this.name + propertyNumber.toString();
		this.LTLProp = answer.getValue();
	}
	
	private void buildSafety(Spec toParse, String clockKind, Integer propertyNumber) {
		Pair<String, String> answer = initialParse(toParse, clockKind);
		this.name = clockKind == "tock" ? "A" : "G";
		this.name = this.name + propertyNumber.toString();
		this.LTLProp = "[](" + clockKind + " -> " +answer.getValue()+")";
	}
	
	private void buildInitial(Spec toParse, String clockKind) {
		Pair<String, String> answer = initialParse(toParse, clockKind);
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
