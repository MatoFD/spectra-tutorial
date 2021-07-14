package parsing;

import tau.smlab.syntech.gameinput.model.Constraint;
import tau.smlab.syntech.gameinput.spec.*;

public class MyConstraint {

	private String name;
	private String LTLProp;
	
	public MyConstraint(Constraint cons) {
		if (cons.isInitial()) {
			buildInitial(cons.getSpec());
		} else if (cons.isSafety()) {
			buildSafety(cons.getSpec());
		} else if (cons.isJustice()) {
			buildJustice(cons.getSpec());
		} else {
			throw new Error("we neec to translate a new type of constraint");
		}
	}

	public MyConstraint(String type, Spec spec) {
		switch(type) {
			case "initial":
				buildInitial(spec);
			case "safety":
				buildSafety(spec);
			case "justice":
				buildJustice(spec);
		}
	}
	
	private void buildJustice(Spec toParse) {
		
	}
	
	private void buildSafety(Spec toParse) {
		
	}
	
	private void buildInitial(Spec toParse) {
		if(toParse instanceof VariableReference) {
			VariableReference varRef = (VariableReference) toParse;
			this.name = varRef.getReferenceName();
			this.LTLProp = varRef.getReferenceName().toUpperCase();
		} else if(toParse instanceof SpecExp) {
			SpecExp specification = (SpecExp) toParse;
			if(specification.getOperator().equals(Operator.EQUALS)) {
				VariableReference left = (VariableReference) specification.getChildren()[0]; 
				this.name = left.getReferenceName();
				MyConstraint right = new MyConstraint("initial", specification.getChildren()[1]);
				this.LTLProp = right.LTLProp;
			} else if(specification.getOperator().equals(Operator.NOT)) {
				MyConstraint child = new MyConstraint("initial", specification.getChildren()[0]);
				this.name = child.name;
				this.LTLProp = "!"+child.LTLProp;
			} else {
				throw new Error();
			}
			
		} else if (toParse instanceof PrimitiveValue) {
			PrimitiveValue val = (PrimitiveValue) toParse;
			this.name = val.getValue();
			this.LTLProp = val.getValue();
		} else {
			throw new Error("we need another type of Spec to parse");
		}
	}
	
	public String getLTLProp() {
		return LTLProp;
	}

	public String getName() {
		return name;
	}
}
