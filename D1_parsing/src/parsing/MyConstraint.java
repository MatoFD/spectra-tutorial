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
			//only in safety constraints we have problems to translate NOT(Next(Subspec))
			cons.setSpec(fixNotNext(cons.getSpec()));
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
				throw new Error("should never happen, we removed PRIME translators.");
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
				throw new Error("should never happen, we removed PRIME translators.");
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
			case IFF:
				return " <-> ";
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
	
	private Spec fixNotNext(Spec s) {
		if(!(s instanceof SpecExp )){
			return s;
		}		
		if (hasNotNext(s, false)) {
			//we check if hasNotNext so we only modify the constraints when needed.
			//because modifying the constraints makes understanding them harder.
			s = changeNotOrder(s, false);
		}
		return s;
	}
	
	private Spec changeNotOrder(Spec s, boolean insideNot) {
		if(!(s instanceof SpecExp )){
			if(insideNot) {
				return new SpecExp(Operator.NOT, s);
			}else {
				return s;
			}
		}
		SpecExp e = (SpecExp) s;
		switch(e.getOperator()) {
			case PRIME:
				Spec recursive = changeNotOrder(e.getChildren()[0], insideNot);
				return new SpecExp(Operator.PRIME, recursive);
			case NOT:
				if (insideNot) {
					//negation cancels another negation
					return changeNotOrder(e.getChildren()[0], false);
				}else {
					return changeNotOrder(e.getChildren()[0], true);
				}
			case IFF:
				Spec[] fixedChildrenIFF = new Spec[2];
				for (int i = 0; i < e.getChildren().length; i++) {
					fixedChildrenIFF[i] = changeNotOrder(e.getChildren()[i], insideNot);
				}
				//a <-> b is equivalent to (a -> b) && (b -> a), which we fix below.
				//we are removing implications, because if "a" has a PRIME, it will be wrongly translated
				Spec leftIFF = new SpecExp(Operator.IMPLIES, fixedChildrenIFF[0], fixedChildrenIFF[1]);
				Spec rightIFF = new SpecExp(Operator.IMPLIES, fixedChildrenIFF[1], fixedChildrenIFF[0]);
				return new SpecExp(Operator.AND, leftIFF, rightIFF);
			case IMPLIES: 
				Spec left = changeNotOrder(e.getChildren()[0], !insideNot);
				Spec right = changeNotOrder(e.getChildren()[1], insideNot);
				// a -> b is equivalent to !a || b
				return new SpecExp(Operator.OR, left, right);
			default:
				Spec[] fixedChildren = new Spec[2];
				for (int i = 0; i < e.getChildren().length; i++) {
					fixedChildren[i] = changeNotOrder(e.getChildren()[i], insideNot);
				}
				return new SpecExp(e.getOperator(), fixedChildren[0], fixedChildren[1]);
		}
	}
	
	private boolean hasNotNext(Spec s, boolean insideNot) {
		if(!(s instanceof SpecExp )){
			return false;
		}
		SpecExp e = (SpecExp) s; 
		switch(e.getOperator()) {
			case NOT:
			case IMPLIES:
				return hasNotNext(e.getChildren()[0], true);
			case IFF:
				for (int i = 0; i < e.getChildren().length; i++) {
					if (hasNotNext(e.getChildren()[i], true)) {
						return true;
					}
				}
				return false;
			case PRIME:
				return insideNot;
			default:
				for (int i = 0; i < e.getChildren().length; i++) {
					if (hasNotNext(e.getChildren()[i], false)) {
						return true;
					}
				}
				return false;
		}
	}
	
	private boolean checkIfIsNextVar(VariableReference var) {
		//if VAR reference name ends with ', its actually NEXT(VAR).
		return var.getReferenceName().endsWith("'");
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
