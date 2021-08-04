package parsing;


import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.stream.Collectors;

import org.eclipse.xtext.xbase.lib.Pair;

import tau.smlab.syntech.gameinput.model.Constraint;
import tau.smlab.syntech.gameinput.model.Variable;
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
			String varName = makeVarName(varRef.getReferenceName());
			if(checkIfIsNextVar(varRef)) {
				throw new Error("should never happen, we removed PRIME translators.");
			}else {
				return varName;
			}
		} else if(spec instanceof SpecExp) {
			SpecExp specification = (SpecExp) spec;
			if(specification.getOperator().equals(Operator.EQUALS)) {
				if (!isPrimitiveEqual(specification)) {
					throw new Error("occurence of notPrimitiveEqual");
//					return subParse(new SpecExp(Operator.IFF, specification.getChildren()[0], specification.getChildren()[1]), clockKind);
				}
				//translate "left=right" to "left_right", because we have fluents, not variables in MTSA.
				return primitiveEqualProp(specification, clockKind, false);
			} else if(specification.getOperator().equals(Operator.NOT)) {
				if ( specification.getChildren()[0] instanceof SpecExp
						&& ((SpecExp) specification.getChildren()[0]).getOperator().equals(Operator.EQUALS)) {
					SpecExp subSpecEqual = (SpecExp) specification.getChildren()[0];
					if (!isPrimitiveEqual(subSpecEqual)) {
						throw new Error("occurence of notPrimitiveEqual");
					}
					return primitiveEqualProp(subSpecEqual, clockKind, true);
				}else {
					return "!" + subParse(specification.getChildren()[0], clockKind);	
				}
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
		String varName = ""; //only matters for varRefs, primitiveVals and operator NOT, since it's for initial constraints
		String LTLProp = "";
		if(spec instanceof VariableReference) {
			VariableReference varRef = (VariableReference) spec;
			varName = makeVarName(varRef.getReferenceName());
			if(checkIfIsNextVar(varRef)) {
				throw new Error("should never happen, we removed PRIME translators.");
			}else {
				LTLProp = clockKind + " && " + varName;
			}
		} else if(spec instanceof SpecExp) {
			SpecExp specification = (SpecExp) spec;
			if(specification.getOperator().equals(Operator.EQUALS)) {
				if (!isPrimitiveEqual(specification)) {
					throw new Error("New type of equal, replace with IFF, as in subParse?");
				}
				VariableReference left = (VariableReference) specification.getChildren()[0];
				varName = makeVarName(left.getReferenceName());
				LTLProp = clockKind + " && " + subParse(specification, clockKind); //only "right", not "left=right" because we have fluents, not variables in MTSA
			} else if(specification.getOperator().equals(Operator.NOT)) {
				String answer = subParse(specification, clockKind);
				varName = answer.substring(1); //remove the initial "!" 
				LTLProp = clockKind + " && " + answer; //the NOT is processed in the subParse
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
			varName = val.getValue();
			LTLProp = val.getValue();
		} else {
			throw new Error("we need another type of Spec to parse");
		}		
		return new Pair<String, String>(varName, "("+LTLProp+")");
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
		this.name = clockKind == "tock" ? "A_l" : "G_l";
		this.name = this.name + propertyNumber.toString();
		Pair<String, String> answer = initialParse(toParse, clockKind);
		this.LTLProp = answer.getValue();
	}
	
	private void buildSafety(Spec toParse, String clockKind, Integer propertyNumber) {
		String comment = "";
		this.name = clockKind == "tock" ? "A" : "G";
		this.name = this.name + propertyNumber.toString();
		//only in safety constraints we have problems to translate NOT(Next(Subspec))
		if (hasNotNext(toParse, false)) {
			//we check if hasNotNext so we only modify the constraints when needed.
			//because modifying the constraints makes understanding them harder.
			
			//we put a comment with the original constraint so the translation is understandable
			Pair<String, String> commentAux = initialParse(toParse, clockKind);
			comment += "\n //"+commentAux.getValue() + "\n";
			
			toParse = changeNotOrder(toParse, false);
		}
		
		Pair<String, String> answer = initialParse(toParse, clockKind);
		this.LTLProp = "[](" + clockKind + " -> " +answer.getValue()+")";
		this.LTLProp += comment;
	}
	
	private void buildInitial(Spec toParse, String clockKind) {
		Pair<String, String> answer = initialParse(toParse, clockKind);
		this.name = answer.getKey();
		this.LTLProp = "(!"+clockKind+" W "+answer.getValue()+")";
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
				Spec leftToRight = new SpecExp(Operator.IMPLIES, e.getChildren()[0], e.getChildren()[1]);
				Spec rightToLeft = new SpecExp(Operator.IMPLIES, e.getChildren()[1], e.getChildren()[0]);
				Spec fixedLeftToRight = changeNotOrder(leftToRight, insideNot);
				Spec fixedrightToLeft = changeNotOrder(rightToLeft, insideNot);
				if(insideNot) {
					//!(a <-> b) is equivalent to !(a -> b) || !(b -> a), which we fix below.
					return new SpecExp(Operator.OR, fixedLeftToRight, fixedrightToLeft);
				}else {
					//a <-> b is equivalent to (a -> b) && (b -> a), which we fix below.
					//we are removing implications, because if "a" has a PRIME, it will be wrongly translated
					return new SpecExp(Operator.AND, fixedLeftToRight, fixedrightToLeft);
				}
			case IMPLIES: 
				Spec left = changeNotOrder(e.getChildren()[0], !insideNot);
				Spec right = changeNotOrder(e.getChildren()[1], insideNot);
				if (insideNot) {
					// !(a -> b) is equivalent to a && !b
					return new SpecExp(Operator.AND, left, right);
				}else {
					// a -> b is equivalent to !a || b
					return new SpecExp(Operator.OR, left, right);
				}
			case AND:
				Spec leftAND = changeNotOrder(e.getChildren()[0], insideNot);
				Spec rightAND = changeNotOrder(e.getChildren()[1], insideNot);
				if (insideNot) {
					// !(a && b) is equivalent to !a || !b
					return new SpecExp(Operator.OR, leftAND, rightAND);
				} else {
					return new SpecExp(Operator.AND, leftAND, rightAND);
				}
			case OR:
				Spec leftOR = changeNotOrder(e.getChildren()[0], insideNot);
				Spec rightOR = changeNotOrder(e.getChildren()[1], insideNot);
				if (insideNot) {
					// !(a || b) is equivalent to !a && !b
					return new SpecExp(Operator.AND, leftOR, rightOR);
				} else {
					return new SpecExp(Operator.OR, leftOR, rightOR);
				}
			case EQUALS:
				if (!isPrimitiveEqual(e)) {
					throw new Error("EQUAL is not VarRef = PrimitiveVal");
//					return changeNotOrder(new SpecExp(Operator.IFF, e.getChildren()[0], e.getChildren()[1]), insideNot);
				}
				if(insideNot) {
					return new SpecExp(Operator.NOT, e);	
				}else {
					return e;
				}
			default:
				throw new Error("new kind of SpecExp");
		}
	}
	
	private String primitiveEqualProp(SpecExp e, String clockKind, boolean insideNot) {
		Spec left = e.getChildren()[0];
		Spec right = e.getChildren()[1];
		
		//cases of var1=var2 or the same but one is next(var)
		if (isVarOrNextVar(left) && isVarOrNextVar(right)){
			return var1EQvar2(left, right, clockKind, insideNot);
		}
		
		//at this point we know one of the childs is a primValue
		PrimitiveValue prim;
		Spec varExp;
		if (left instanceof PrimitiveValue) {
			prim = (PrimitiveValue) left;
			varExp = right;
		} else if(right instanceof PrimitiveValue) {
			prim = (PrimitiveValue) right;
			varExp = left;
		} else {//one of the two is a primVal, otherwise e is not a primitiveEqual
			throw new Error("e is not a primitiveEqual"); 
		}
		
		String negation = insideNot ? "!" : "";
		if (varExp instanceof VariableReference) {
			//cases of varRef = primVal
			VariableReference var = (VariableReference) varExp;
			return negation + var.getReferenceName().toUpperCase()+"_"+prim.getValue();
		} else if(varExp instanceof SpecExp) {
			//cases of next(VarRef) = primVal
			SpecExp exp = (SpecExp) varExp;
			if(exp.getOperator().equals(Operator.PRIME) &&
					exp.getChildren()[0] instanceof VariableReference) {
				//return next(var_primval)
				String fluentName = ((VariableReference) exp.getChildren()[0]).getReferenceName().toUpperCase()+"_"+prim.getValue();
				return "X(!" + clockKind + " W (" + clockKind + " && " + negation + fluentName + "))";
			} else {
				throw new Error("new primitiveEqual");
			}
		}else {
			throw new Error("the other child of primitiveEqual is a new type"); 
		}		
	}
	
	private String var1EQvar2(Spec left, Spec right, String clockKind, boolean insideNot) {
		//translate var1=next(var2) to  (var1_1 <-> next(var2_1) && var1_2 <-> next(var2_2) &&...)
		Variable leftVar;
		if (left instanceof VariableReference) {
			leftVar = ((VariableReference) left).getVariable();
		}else {
			//we know left is PRIME(var)
			leftVar = ((VariableReference)(((SpecExp) left).getChildren()[0])).getVariable();
		}
		Variable rightVar;
		if (right instanceof VariableReference) {
			rightVar = ((VariableReference) right).getVariable();
		}else {
			//we know right is PRIME(var)
			rightVar = ((VariableReference)(((SpecExp) right).getChildren()[0])).getVariable();
		}
			
		List<String> leftFluents = leftVar.getNoNameActions(); 
		Collections.sort(leftFluents);
		List<String> rightFluents = rightVar.getNoNameActions();
		Collections.sort(rightFluents);
		if(!leftFluents.equals(rightFluents)) {
			throw new Error("two vars cannot be equal if their possible values don't match");
		}else {
			//the variables are booleans or have the same possible values, they are compatible.
			List<String> equals = new ArrayList<String>();
			for(String f : leftFluents) {
				String fixedF = f.replaceAll("\\.", "_");
				if (!leftVar.getType().isInteger()) {//it's enum
					fixedF = "_"+fixedF;
				}
				String leftAnswer = (leftVar.getName()+fixedF).toUpperCase();
				String rightAnswer = (rightVar.getName()+fixedF).toUpperCase();
				if(leftVar.getType().isBoolean() && rightVar.getType().isBoolean()){
					leftAnswer = (new MyVar(leftVar)).getFluents().get(0);
					rightAnswer = (new MyVar(rightVar)).getFluents().get(0);
				}
				
				String notLeft = "!"+leftAnswer;
				String notRight = "!"+rightAnswer;
				boolean hasNoNext = false;
				if(left instanceof SpecExp) {//if it's actually PRIME(leftVar)
					leftAnswer = "X(!" + clockKind + " W (" + clockKind + " && (" + leftAnswer + ")))";
					notLeft = "X(!" + clockKind + " W (" + clockKind + " && (" + notLeft + ")))";
					hasNoNext = true;
				}
				if(right instanceof SpecExp) {//if it's actually PRIME(rightVar)
					rightAnswer = "X(!" + clockKind + " W (" + clockKind + " && (" + rightAnswer + ")))";
					notLeft = "X(!" + clockKind + " W (" + clockKind + " && (" + notRight + ")))";
					hasNoNext = true;
				}
				if(hasNoNext) {
					if(insideNot) {
						//!(var1=var2) is !(var1_1 <-> next(var2_1) ||  !(var1_2 <-> next(var2_2)) ||...)
						//and  !(a <-> b) is equivalent to !(a -> b) || !(b -> a).     !(a -> b) is equivalent to a && !b
						equals.add("(("+leftAnswer+" && "+notRight+") || ("+rightAnswer+" && "+notLeft+"))");
					}else {
						equals.add("(("+notLeft+" || "+rightAnswer+") && ("+notRight+" || "+leftAnswer+"))");
					}
				}else {
					String negation = insideNot ? "!" : "";
					equals.add(negation+"("+leftAnswer+" <-> "+rightAnswer+")");
				}
			}
			if(insideNot) {
				return "("+equals.stream().collect(Collectors.joining(" || "))+")";
			}else {
				return "("+equals.stream().collect(Collectors.joining(" && "))+")";
			}
		}
	}
	
	private boolean isPrimitiveEqual(SpecExp e) {
		Spec left = e.getChildren()[0];
		Spec right = e.getChildren()[1];
		
		//cases of varRef = primVal
		if ((left instanceof VariableReference && right instanceof PrimitiveValue)
				|| (right instanceof VariableReference && left instanceof PrimitiveValue)) {
			return true;
		}
		
		//cases of var1=var2 or the same but one is next(var)
		if (isVarOrNextVar(left) && isVarOrNextVar(right)){
			return true;
		}
		
		//cases of next(VarRef) = primVal
		if (left instanceof PrimitiveValue) {
			SpecExp rightE = (SpecExp) right;
			if(rightE.getOperator().equals(Operator.PRIME) &&
					rightE.getChildren()[0] instanceof VariableReference) {
				return true;
			} else {
				throw new Error("new primitiveEqual");
			}
		}
		if (right instanceof PrimitiveValue) {
			SpecExp leftE = (SpecExp) left;
			if(leftE.getOperator().equals(Operator.PRIME) &&
					leftE.getChildren()[0] instanceof VariableReference) {
				return true;
			} else {
				throw new Error("new primitiveEqual");
			}
		}
		
		return false;
	}
	
	private boolean isVarOrNextVar(Spec s) {
		return (s instanceof VariableReference || (s instanceof SpecExp && 
				((SpecExp) s).getOperator().equals(Operator.PRIME) && (((SpecExp) s).getChildren()[0] instanceof VariableReference)));
	}
	
	private boolean hasNotNext(Spec s, boolean insideNot) {
		if(!(s instanceof SpecExp )){
			return false;
		}
		SpecExp e = (SpecExp) s; 
		switch(e.getOperator()) {
			case NOT:
				return hasNotNext(e.getChildren()[0], !insideNot);
			case IMPLIES:
				return hasNotNext(e.getChildren()[0], !insideNot) ||
						hasNotNext(e.getChildren()[1], insideNot);
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
					if (hasNotNext(e.getChildren()[i], insideNot)) {
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
		return name.toUpperCase().replaceAll("\\.", "_");
	}
	
	public String getLTLProp() {
		return LTLProp;
	}

	public String getName() {
		return name;
	}
}
