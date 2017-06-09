package org.ggp.base.util.statemachine.implementation.propnet;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.ggp.base.util.gdl.grammar.Gdl;
import org.ggp.base.util.gdl.grammar.GdlConstant;
import org.ggp.base.util.gdl.grammar.GdlRelation;
import org.ggp.base.util.gdl.grammar.GdlSentence;
import org.ggp.base.util.propnet.architecture.Component;
import org.ggp.base.util.propnet.architecture.PropNet;
import org.ggp.base.util.propnet.architecture.components.And;
import org.ggp.base.util.propnet.architecture.components.Constant;
import org.ggp.base.util.propnet.architecture.components.Not;
import org.ggp.base.util.propnet.architecture.components.Or;
import org.ggp.base.util.propnet.architecture.components.Proposition;
import org.ggp.base.util.propnet.architecture.components.Transition;
import org.ggp.base.util.propnet.factory.OptimizingPropNetFactory;
import org.ggp.base.util.statemachine.MachineState;
import org.ggp.base.util.statemachine.Move;
import org.ggp.base.util.statemachine.Role;
import org.ggp.base.util.statemachine.StateMachine;
import org.ggp.base.util.statemachine.exceptions.GoalDefinitionException;
import org.ggp.base.util.statemachine.exceptions.MoveDefinitionException;
import org.ggp.base.util.statemachine.exceptions.TransitionDefinitionException;
import org.ggp.base.util.statemachine.implementation.prover.query.ProverQueryBuilder;


@SuppressWarnings("unused")
public class SamplePropNetStateMachine extends StateMachine {
    /** The underlying proposition network  */
    private PropNet propNet;
    /** The topological ordering of the propositions */
    private List<Proposition> ordering;
    /** The player roles */
    private List<Role> roles;

    /**
     * Initializes the PropNetStateMachine. You should compute the topological
     * ordering here. Additionally you may compute the initial state here, at
     * your discretion.
     */
    @Override
    public void initialize(List<Gdl> description) {
        try {
        	propNet = OptimizingPropNetFactory.create(description);
            roles = propNet.getRoles();
            ordering = getOrdering();
        } catch (InterruptedException e) {
            throw new RuntimeException(e);
        }
    }

    private boolean markbases(MachineState state) {
    	// Get the contents of the current state
    	Set<GdlSentence> contents = state.getContents();

    	for (Proposition p:propNet.getBasePropositions().values()) {
    		// Check if the base proposition is true/false in this state
    		if (contents.contains(p.getName())) p.setValue(true);
    		else p.setValue(false);
    	}
    	return true;
    }

    private boolean markactions(List<Move> moves) {
    	List<GdlSentence> move_sentences = toDoes(moves);
    	for (Proposition p:propNet.getInputPropositions().values()) {
    		if (move_sentences.contains(p.getName())) p.setValue(true);
    		else p.setValue(false);
    	}
    	return true;
    }

    private boolean clearPropnet() {
    	propNet.getInitProposition().setValue(false);
    	for (Proposition p:propNet.getBasePropositions().values()) {
    		p.setValue(false);
    	}
    	for (Proposition p:propNet.getBasePropositions().values()) {
    		p.setValue(false);
    	}
    	return true;
    }

    public boolean propmarkp(Component p) {
    	if (propNet.getBasePropositions().values().contains(p)) return p.getValue();
    	if (propNet.getInputPropositions().values().contains(p)) return p.getValue();
    	if (p instanceof Constant) return p.getValue();
    	if (p instanceof Transition) return p.getSingleInput().getValue();
    	if (p instanceof Not) return propmarkNegation(p);
    	if (p instanceof And) return propmarkConjunction(p);
    	if (p instanceof Or) return propmarkDisjunction(p);
    	if (p.getInputs().size() == 0) return p.getValue();
    	return propmarkp(p.getSingleInput());
    }

    public void forwardProp() {
    	for (Proposition p:ordering) {
    		p.setValue(p.getSingleInput().getValue());
    	}
    }

    private boolean propmarkNegation(Component p) {
    	return !propmarkp(p.getSingleInput());
    }

    private boolean propmarkConjunction(Component p) {
    	for (Component c:p.getInputs()) {
    		if (!propmarkp(c)) return false;
    	}
    	return true;
    }

    private boolean propmarkDisjunction(Component p) {
    	for (Component c:p.getInputs()) {
    		if (propmarkp(c)) return true;
    	}
    	return false;
    }

    /**
     * Computes if the state is terminal. Should return the value
     * of the terminal proposition for the state.
     */
    @Override
    public boolean isTerminal(MachineState state) {
        clearPropnet();
    	markbases(state);	// Mark the base propositions
    	forwardProp();
    	return propNet.getTerminalProposition().getValue();
//    	return propmarkp(propNet.getTerminalProposition());	// Propagate
    }

    /**
     * Computes the goal for a role in the current state.
     * Should return the value of the goal proposition that
     * is true for that role. If there is not exactly one goal
     * proposition true for that role, then you should throw a
     * GoalDefinitionException because the goal is ill-defined.
     */
    @Override
    public int getGoal(MachineState state, Role role)
            throws GoalDefinitionException {
        clearPropnet();
    	markbases(state);
    	forwardProp();
    	for (Proposition p:propNet.getGoalPropositions().get(role)) {
    		if (p.getValue()) return goalValue(p);
    	}
//        for (Proposition p:propNet.getGoalPropositions().get(role)) {
//        	if (propmarkp(p)) {
//        		return goalValue(p);
//        	}
//        }
        return 0;
    }

    private int goalValue(Proposition p) {
    	GdlRelation relation = (GdlRelation)p.getName();
    	GdlConstant constant = (GdlConstant)relation.get(1);
    	return Integer.parseInt(constant.toString());
    }

    /**
     * Returns the initial state. The initial state can be computed
     * by only setting the truth value of the INIT proposition to true,
     * and then computing the resulting state.
     */
    @Override
    public MachineState getInitialState() {
    	// Initialize a set of contents to be used for MachineState
        Set<GdlSentence> contents = new HashSet<GdlSentence>();
        propNet.getInitProposition().setValue(true);
        for (Proposition p:propNet.getBasePropositions().values()) {	// Loop over all base propositions
        	if (p.getSingleInput().getValue()) {	// Check to see if the Input for base proposition is true
        		contents.add(p.getName());	// B/c transition connective, true input leads to true base prop
        		p.setValue(true);
        	} else {
        		p.setValue(false);
        	}
        }
        return new MachineState(contents);
    }

    /**
     * Computes all possible actions for role.
     */
    @Override
    public List<Move> findActions(Role role)
            throws MoveDefinitionException {
    	Set<Proposition> actions = new HashSet<Proposition>();
    	forwardProp();
    	for (Proposition p:propNet.getLegalPropositions().get(role)) {
    		if (p.getValue()) actions.add(p);
    	}
//        for (Proposition p:propNet.getLegalPropositions().get(role)) {
//        	if (propmarkp(p)) actions.add(p);
//        }
        List<Move> allMoves = new ArrayList<Move>();
        for (Proposition p:actions) {
        	allMoves.add(getMoveFromProposition(p));
        }
        return allMoves;
    }

    /**
     * Computes the legal moves for role in state.
     */
    @Override
    public List<Move> getLegalMoves(MachineState state, Role role)
            throws MoveDefinitionException {
    	clearPropnet();
    	markbases(state);
    	forwardProp();
    	List<Proposition> action_props = new ArrayList<Proposition>();
    	for (Proposition p:propNet.getLegalPropositions().get(role)) {
    		if (p.getValue()) action_props.add(p);
    	}
//    	for (Proposition p:propNet.getLegalPropositions().get(role)) {
//    		if (propmarkp(p)) action_props.add(p);
//    	}

    	List<Move> actions = new ArrayList<Move>();
    	for (Proposition p:action_props) {
    		actions.add(getMoveFromProposition(p));
    	}
    	if (actions.size() == 0) throw new MoveDefinitionException(state, role);
    	return actions;
    }

    /**
     * Computes the next state given state and the list of moves.
     */
    @Override
    public MachineState getNextState(MachineState state, List<Move> moves)
            throws TransitionDefinitionException {
    	markbases(state);
    	markactions(moves);
    	forwardProp();
    	Collection<Proposition> bases = propNet.getBasePropositions().values();
    	Set<GdlSentence> contents = new HashSet<GdlSentence>();

    	for (Proposition p:bases) {
    		if (p.getSingleInput().getSingleInput().getValue()) contents.add(p.getName());
    	}
//    	for (Proposition p:bases) {
//    		if (propmarkp(p.getSingleInput().getSingleInput())) contents.add(p.getName());
//    	}
    	return new MachineState(contents);
    }

    /**
     * This should compute the topological ordering of propositions.
     * Each component is either a proposition, logical gate, or transition.
     * Logical gates and transitions only have propositions as inputs.
     *
     * The base propositions and input propositions should always be exempt
     * from this ordering.
     *
     * The base propositions values are set from the MachineState that
     * operations are performed on and the input propositions are set from
     * the Moves that operations are performed on as well (if any).
     *
     * @return The order in which the truth values of propositions need to be set.
     */
    public List<Proposition> getOrdering()
    {
    	// List to contain the topological ordering.
        List<Proposition> order = new LinkedList<Proposition>();

        // All of the components in the PropNet
        List<Component> components = new ArrayList<Component>(propNet.getComponents());

        // All of the propositions in the PropNet.
        List<Proposition> propositions = new ArrayList<Proposition>(propNet.getPropositions());

        // Get rid of base propositions, input propositions, and initproposition from components
        for (Proposition b:propNet.getBasePropositions().values()) {
        	components.remove(b);
        }
        for (Proposition i:propNet.getInputPropositions().values()) {
        	components.remove(i);
        }
        components.remove(propNet.getInitProposition());
        // Remove from the list when a component can be calculated
        while (!components.isEmpty()) {
        	List<Component> copy = new ArrayList<Component>(components);
        	for (Component component:components) {
        		boolean inputsDone = true; // Used to check and see if a component's inputs are all calculated
        		for (Component input:component.getInputs()) {
        			if (components.contains(input)) {
        				inputsDone = false;
        				break;
        			}
        		}
        		// Actions when component is deemed ready
        		if (inputsDone) {
        			copy.remove(component);
        			if (propositions.contains(component)) order.add((Proposition) component);
        		}
        	}
        	components = copy;	// Only bring remaining components back to the start of loop
        }

        return order;
    }

    /* Already implemented for you */
    @Override
    public List<Role> getRoles() {
        return roles;
    }

    /* Helper methods */

    /**
     * The Input propositions are indexed by (does ?player ?action).
     *
     * This translates a list of Moves (backed by a sentence that is simply ?action)
     * into GdlSentences that can be used to get Propositions from inputPropositions.
     * and accordingly set their values etc.  This is a naive implementation when coupled with
     * setting input values, feel free to change this for a more efficient implementation.
     *
     * @param moves
     * @return
     */
    private List<GdlSentence> toDoes(List<Move> moves)
    {
        List<GdlSentence> doeses = new ArrayList<GdlSentence>(moves.size());
        Map<Role, Integer> roleIndices = getRoleIndices();

        for (int i = 0; i < roles.size(); i++)
        {
            int index = roleIndices.get(roles.get(i));
            doeses.add(ProverQueryBuilder.toDoes(roles.get(i), moves.get(index)));
        }
        return doeses;
    }

    /**
     * Takes in a Legal Proposition and returns the appropriate corresponding Move
     * @param p
     * @return a PropNetMove
     */
    public static Move getMoveFromProposition(Proposition p)
    {
        return new Move(p.getName().get(1));
    }

    /**
     * Helper method for parsing the value of a goal proposition
     * @param goalProposition
     * @return the integer value of the goal proposition
     */
    private int getGoalValue(Proposition goalProposition)
    {
        GdlRelation relation = (GdlRelation) goalProposition.getName();
        GdlConstant constant = (GdlConstant) relation.get(1);
        return Integer.parseInt(constant.toString());
    }

    /**
     * A Naive implementation that computes a PropNetMachineState
     * from the true BasePropositions.  This is correct but slower than more advanced implementations
     * You need not use this method!
     * @return PropNetMachineState
     */
    public MachineState getStateFromBase()
    {
        Set<GdlSentence> contents = new HashSet<GdlSentence>();
        for (Proposition p : propNet.getBasePropositions().values())
        {
            p.setValue(p.getSingleInput().getValue());
            if (p.getValue())
            {
                contents.add(p.getName());
            }

        }
        return new MachineState(contents);
    }
}
