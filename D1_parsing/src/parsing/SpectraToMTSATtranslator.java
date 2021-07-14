package parsing;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.*;

import tau.smlab.syntech.gameinput.model.Constraint;
import tau.smlab.syntech.gameinput.model.GameInput;
import tau.smlab.syntech.gameinput.model.Player;
import tau.smlab.syntech.gameinput.model.Variable;
import tau.smlab.syntech.gameinputtrans.TranslationProvider;
import tau.smlab.syntech.spectragameinput.ErrorsInSpectraException;
import tau.smlab.syntech.spectragameinput.SpectraInputProviderNoIDE;
import tau.smlab.syntech.spectragameinput.SpectraTranslationException;

/**
 * Example of how to parse spectra specifications.
 */
public class SpectraToMTSATtranslator {

	private static List<String> playerNames = Arrays.asList("sys","aux","env");
	
	public static void main(String[] args) throws ErrorsInSpectraException, SpectraTranslationException {

		String name = "GyroLTL_390_GyroAspect";
		String specPath = name + ".spectra";

		// get the Xtext-based input parser
		SpectraInputProviderNoIDE sip = new SpectraInputProviderNoIDE();
		// parse (via Xtext) and translate to abstract syntax (Xtext independent)
		GameInput gi = sip.getGameInput(specPath);

		System.out.println("\nPrinting vars and constraints of system player:");
		Player sys = gi.getSys();
		printVars(sys);
		printConstraints(sys);
		
		System.out.println("Printing vars and constraints of environment player:");
		Player env = gi.getEnv();
		printVars(env);
		printConstraints(env);

		System.out.println("\nTranslating to Spectra Kernel.");
		// important step to reduce language features to the Spectra Kernel
		TranslationProvider.translate(gi);
		Player aux = gi.getAux();

		System.out.println("\nPrinting vars and constraints of system and aux players:");
		printVars(sys);
		printVars(aux);
		printConstraints(sys);
		printConstraints(aux);
		
		System.out.println("\nPrinting vars and constraints of environment player:");
		printVars(env);
		printConstraints(env);
		
		translateToFSP(name, gi);
	}

	private static void translateToFSP(String name, GameInput gi) {
		String filename = name + ".fsp";
		PrintWriter out;
		File f = new File(filename);
		if(!f.isFile()) { 
			try {
				f.createNewFile();
			} catch (IOException e) {
				e.printStackTrace();
			}
		}
		try {			
			Map<String, Set<MyVar>> playersMyVars = new HashMap<String, Set<MyVar>>(Map.of(
					"sys",new HashSet<MyVar>(),
					"aux",new HashSet<MyVar>(),
					"env",new HashSet<MyVar>()));			
			List<String> sysActions = getActions(gi.getSys().getVars(), playersMyVars.get("sys"));
			List<String> auxActions = getActions(gi.getAux().getVars(), playersMyVars.get("aux"));
			List<String> envActions = getActions(gi.getEnv().getVars(), playersMyVars.get("env"));
			sysActions.add("tick");
			envActions.add("tock");
			List<String> controllableActions = new ArrayList<String>(sysActions);
			controllableActions.addAll(auxActions);
			
			out = new PrintWriter(f);
			out.println("//" + name + " automatically_translated \n");
			printActions(out, controllableActions, "ControlledActions");
			printActions(out, envActions, "UncontrolledActions");
			out.println("set AllActions = {ControlledActions, UncontrolledActions}\n");
			
			printVars(out, playersMyVars);
			
			printClock(out);
			
			printInitialValues(out, gi);
			
			out.close();
		} catch (FileNotFoundException e) {
			e.printStackTrace();
		}
	}
	
	private static void printInitialValues(PrintWriter out, GameInput gi) {
		List<String> initialNames = new ArrayList<String>(); 
		for (String pName : playerNames) {
			Player p = gi.getPlayer(pName);
			String typeOfProp = "ltl_property";
			String clock = "tick";
			if (pName == "env") {
				typeOfProp = "constraint";
				clock = "tock";
			}
			for (Constraint cons : p.getConstraints()) {
				if (cons.isInitial()) {
					MyConstraint myCons = new MyConstraint(cons);
					out.println(typeOfProp+" Initial_" + myCons.getName() + " = "+ 
							initialToAsynchronous(myCons.getLTLProp(), clock));
					initialNames.add("Initial_"+myCons.getName());
				}
			}
		}
		String composition = initialNames.stream().collect(Collectors.joining(" || "));
		out.println("||Initial_Values = ("+composition+").\n\n");		
	}
	
	private static String initialToAsynchronous(String prop, String clock) {
		return "(!"+clock+" W ("+clock+" && "+prop+"))";
	}
	
	private static void printClock(PrintWriter out) {
		out.println("\n\n// move from synchronous play to asynchronous representation\n"
				+ "Clock = Env_turn,\n"
				+ "Env_turn = (tock -> Sys_turn | {UncontrolledActions}\\{tock} -> Env_turn),\n"
				+ "Sys_turn = (tick -> Env_turn | {ControlledActions}\\{tick} -> Sys_turn).\n"
				+ "\n"
				+ "Turns(N=1) = Controller[N],\n"
				+ "Controller[i:1..N] = ({ControlledActions}\\{tick} -> Controller[i-1] | tick -> Controller[N]),\n"
				+ "Controller[0] = (tick -> Controller[N]).\n"
				+ "\n"
				+ "||Full_Clock = (Clock || Turns(#ControlledActions)).//|| UTurns(#UncontrolledActions+2)).\n"
				+ "\n"
				+ "//fluent Tick = <tick, AllActions\\{tick}>\n"
				+ "\n"
				+ "//assumption, env eventually gives control to sys\n"
				+ "fluent Tock = <tock, tick>\n"
				+ "assert A_clock = (Tock)\n"
				+ "\n"
				+ "//==================LTL Properties=============================\n"
				+ "//=======Starting values=======\n");
	}
	
	private static void printVars(PrintWriter out, Map<String, Set<MyVar>> playersMyVars) {
		for(Set<MyVar> player : playersMyVars.values()) {
			for(MyVar v : player) {
				String varActions = v.getName()+"_Actions";
				out.println("\n"+"set "+varActions+" = {"+v.printActions()+"}");
				for(String fluent : v.getFluents()) {
					out.println("fluent "+fluent+" = <"+fluent.toLowerCase()+", "+varActions+"\\{"+fluent.toLowerCase()+"}>");
				}
			}
		}
	}
	
	//Also build Set of MyVar for the respective player
	private static List<String> getActions(List<Variable> vars, Set<MyVar> playersMyVars){
		List<String> answer = new ArrayList<String>();
		for (Variable var : vars) {
			List<String> current = getActions(var);
			answer.addAll(current);
			playersMyVars.add(new MyVar(var.getName(), current, var.getType()));
		}
		return answer;
	}
	
	private static List<String> getActions(Variable var){
		List<String> answer = new ArrayList<String>();
		String name = var.getName();
		if(var.getType().isBoolean()) {
			answer.add(name);
			answer.add("not_"+name);
		} else if(var.getType().isInteger()) {
			for (Integer i = var.getType().getLower(); i<=var.getType().getUpper(); i++) {
				answer.add(name+"."+Integer.toString(i));
			}
		} else {
			// We assume for now that the var is an enum if not bool or int.
			for (String action : var.getType().getValues()) {
				answer.add(name+"."+action.toLowerCase());
			}
		}
		return answer;
	}
	
	private static void printActions(PrintWriter out, List<String> actions, String name) {
		String ans = actions.stream().collect(Collectors.joining(", "));
		out.println("set "+name+" = {"+ans+"}");
	}

	
	private static void printVars(Player p) {
		for (Variable v : p.getVars()) {
			System.out.println(v.toString());
		}
	}

	private static void printConstraints(Player p) {
		for (Constraint c : p.getConstraints()) {
			switch (c.getKind()) {
			case INI:
				System.out.println("Initial constraint " + c.getSpec());
				break;
			case SAFETY:
				System.out.println("Safety constraint " + c.getSpec());
				break;
			case STATE_INV:
				System.out.println("State invariant " + c.getSpec());
				break;
			case JUSTICE:
				System.out.println("Justice constraint " + c.getSpec());
				break;
			case PATTERN:
				System.out.println("Pattern constraint " + c.getSpec());
				break;
			default:
				break;
			}
		}
	}

}
