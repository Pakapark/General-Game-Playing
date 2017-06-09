import java.util.ArrayList;
import java.util.List;
import java.util.Random;

import org.ggp.base.apps.player.Player;
import org.ggp.base.player.gamer.exception.GamePreviewException;
import org.ggp.base.player.gamer.statemachine.StateMachineGamer;
import org.ggp.base.util.game.Game;
import org.ggp.base.util.statemachine.MachineState;
import org.ggp.base.util.statemachine.Move;
import org.ggp.base.util.statemachine.Role;
import org.ggp.base.util.statemachine.StateMachine;
import org.ggp.base.util.statemachine.cache.CachedStateMachine;
import org.ggp.base.util.statemachine.exceptions.GoalDefinitionException;
import org.ggp.base.util.statemachine.exceptions.MoveDefinitionException;
import org.ggp.base.util.statemachine.exceptions.TransitionDefinitionException;
import org.ggp.base.util.statemachine.implementation.prover.ProverStateMachine;
//import org.ggp.base.util.statemachine.implementation.propnet.SamplePropNetStateMachine;

public class The_Overachiever extends StateMachineGamer{

	Player p;
	private long TIME_LIMIT;
	private long PLAY_TIME;
	private long QUERY_TIME;
	private Role ROLE;
	private StateMachine MACHINE;
	private int NPLAYERS;
	//private int countDepthCharges;

	public The_Overachiever() {
		// TODO Auto-generated constructor stub
	}

	@Override
	public StateMachine getInitialStateMachine() {
		// TODO Auto-generated method stub
		return new CachedStateMachine(new ProverStateMachine());
//		return new SamplePropNetStateMachine();
	}

	@Override
	public void stateMachineMetaGame(long timeout)
			throws TransitionDefinitionException, MoveDefinitionException, GoalDefinitionException {
		// TODO Auto-generated method stub
		MachineState state = getCurrentState();
		PLAY_TIME = getMatch().getPlayClock();
		MACHINE = getStateMachine();
		ROLE = getRole();
		TIME_LIMIT = System.currentTimeMillis() + (getMatch().getStartClock() - 3)*1000;
		QUERY_TIME = getQueryTime();
		NPLAYERS = MACHINE.getRoles().size();
//		countDepthCharges = 0;
//		if (NPLAYERS > 1) MCSTExplore(state);
		MCSTExplore(state);
	}

	private long getQueryTime()
			throws TransitionDefinitionException, MoveDefinitionException, GoalDefinitionException {
		List<List<Move>> moves = MACHINE.getLegalJointMoves(getCurrentState());
		long initTime = System.currentTimeMillis();
		int counter = 0;
		for (int i = 0; i < moves.size(); i++){
			for (int j = 0; j < moves.get(i).size(); j++){
				counter++;
			}
		}
		return System.currentTimeMillis() - initTime;
	}

	@Override
	public Move stateMachineSelectMove(long timeout)
			throws TransitionDefinitionException, MoveDefinitionException, GoalDefinitionException {
		MachineState state = getCurrentState();
		TIME_LIMIT = System.currentTimeMillis() + (PLAY_TIME - 2*QUERY_TIME - (long)3.5)*1000;
		return MCST(state);
	}

	private float maxScore(MachineState state, float alpha, float beta, int level, int level_limit)
			throws TransitionDefinitionException, MoveDefinitionException, GoalDefinitionException {
		if (MACHINE.isTerminal(state)) return MACHINE.getGoal(state, ROLE);

//		if (level >= level_limit) return weighted_combination(role, machine, state);
		if (level >= level_limit) return montecarlo(state, 4);

		List <Move> actions = MACHINE.getLegalMoves(state, ROLE);
		for (int i = 0; i < actions.size(); i++) {
			float result = minScore(actions.get(i), state, alpha, beta, level, level_limit);
			if (result < 0 || System.currentTimeMillis() >= TIME_LIMIT) return -1;
			alpha = (alpha > result ? alpha : result);
			if (alpha >= beta) return beta;
		}

		return alpha;
	}


	private float minScore(Move action, MachineState state, float alpha, float beta, int level, int level_limit)
			throws TransitionDefinitionException, MoveDefinitionException, GoalDefinitionException {
		List <List <Move>> actions = MACHINE.getLegalJointMoves(state, ROLE, action);	// Gets list of list of legal moves from each opponent
		for (int i = 0; i < actions.size(); i++) {
			List <Move> move;
			move = actions.get(i);	// Gets a specific legal move set for all roles in the game
			MachineState newState = MACHINE.getNextState(state, move);
			float result = maxScore(newState, alpha, beta, level + 1, level_limit);
			if (result < 0 || System.currentTimeMillis() >= TIME_LIMIT) return -1;
			beta = (beta < result ? beta : result);
			if (beta <= alpha) return alpha;
		}
		return beta;
	}

	private Move MCST(MachineState state)
			throws TransitionDefinitionException, MoveDefinitionException, GoalDefinitionException {
		MCSTExplore(state);
		return pickBestMove(state);
	}

	private void MCSTExplore(MachineState state)
			throws TransitionDefinitionException, MoveDefinitionException, GoalDefinitionException {
		while (System.currentTimeMillis() < TIME_LIMIT){
			MachineState selectedState = select(state, true);
			if(System.currentTimeMillis() > TIME_LIMIT) return;
			if (MACHINE.isTerminal(selectedState)){
				backpropagate(selectedState, MACHINE.getGoal(selectedState, ROLE));
			} else {
				expand(selectedState);
				if(System.currentTimeMillis() > TIME_LIMIT) return;
				simulate(selectedState);
			}
		}
	}

	private Move pickBestMove(MachineState state)
			throws TransitionDefinitionException, MoveDefinitionException, GoalDefinitionException {
		float score = -1;
		Move bestMove = MACHINE.getRandomMove(state, ROLE);
		for (int i = 0; i < state.children.size(); i++){
			float curScore = state.children.get(i).utility/state.children.get(i).visits;
			if (curScore > score){
				score = curScore;
				bestMove = state.moves.get(i);
			}
		}
//		System.out.println(countDepthCharges);
//		countDepthCharges = 0;
		return bestMove;
	}

	private MachineState select(MachineState state, Boolean trigger)
			throws TransitionDefinitionException, MoveDefinitionException, GoalDefinitionException {
		if (state.visits == 0) return state;
		for (int i = 0; i < state.children.size(); i++) {
			if (state.children.get(i).visits == 0) return state.children.get(i);
		}
		float score = -1;
		MachineState result = state;
		for (int i = 0; i < state.children.size(); i++) {
			float newScore = selectfn(state.children.get(i), trigger);
			if (newScore > score){
				score = newScore;
				result = state.children.get(i);
			}
		}
		if (result.equals(state)) return state;
		return select(result, !trigger);
	}


	private float selectfn(MachineState state, Boolean trigger)
			throws TransitionDefinitionException, MoveDefinitionException, GoalDefinitionException {
		if (trigger || NPLAYERS == 1)
			return (float)(state.utility/state.visits + Math.sqrt(2*(float)Math.log(state.parent.visits)/state.visits));
		return (float)(-state.utility/state.visits + Math.sqrt(2*(float)Math.log(state.parent.visits)/state.visits));
	}


	private void expand(MachineState state)
			throws TransitionDefinitionException, MoveDefinitionException, GoalDefinitionException {
		List<Move> actions = MACHINE.getLegalMoves(state, ROLE);
		for (int i = 0; i < actions.size(); i++) {
			if (System.currentTimeMillis() > TIME_LIMIT) return;
			List<List<Move>> allActions = MACHINE.getLegalJointMoves(state, ROLE, actions.get(i));
			for (int j = 0; j < allActions.size(); j++) {
				MachineState newState = MACHINE.getNextState(state, allActions.get(j));
				newState.parent = state;
				state.children.add(newState);
				state.moves.add(actions.get(i));
			}
		}
	}

	private void simulate(MachineState state)
			throws TransitionDefinitionException, MoveDefinitionException, GoalDefinitionException {
		for (int i = 0; i < state.children.size(); i++) {
			float score = montecarlo(state.children.get(i), 5);
			if (score < 0) return;
			if(System.currentTimeMillis() > TIME_LIMIT) return;
			backpropagate(state.children.get(i), score);
		}
	}

	private void backpropagate(MachineState state, float score)
			throws TransitionDefinitionException, MoveDefinitionException, GoalDefinitionException {
		state.visits += 1;
		state.utility += score;
		if (state.parent != null) backpropagate(state.parent, score);
	}

	private float montecarlo(MachineState state, int count)
			throws TransitionDefinitionException, MoveDefinitionException, GoalDefinitionException {
		float total = 0;
		float score = 0;
		for (int i = 0; i < count; i++){
			score = depthcharge(state);
			if (score < 0) return -1;
			total += score;
		}
		return total/count;
	}

	private float depthcharge(MachineState state)
			throws TransitionDefinitionException, MoveDefinitionException, GoalDefinitionException {
		//countDepthCharges++;
		if (MACHINE.isTerminal(state)) return (float)MACHINE.getGoal(state, ROLE);
		List<Role> roles = MACHINE.getRoles();
		List<Move> moves = new ArrayList<Move>();
		if(System.currentTimeMillis() > TIME_LIMIT) return -1;
		for (int i = 0; i < roles.size(); i++){
			List<Move> options = MACHINE.getLegalMoves(state, roles.get(i));
			Random randomizer = new Random();
			moves.add(options.get(randomizer.nextInt(options.size())));
		}

		MachineState newState = MACHINE.getNextState(state, moves);
		return depthcharge(newState);
	}

//******************* Some Functions pertinent for different versions of a player **************************

//	private Move bestmove(MachineState state, int level, int level_limit)
//			throws TransitionDefinitionException, MoveDefinitionException, GoalDefinitionException {
//		List <Move> actions = MACHINE.getLegalMoves(state, ROLE);
//		Move action = actions.get(0);
//		float score = 0;
//		for (int i = 0; i < actions.size(); i++) {
//			float result = minScore(actions.get(i), state, 0, 100, level, level_limit);
//			if (result == 100) return actions.get(i);
//			if (result == -1) return null;
//			if (result > score) {
//				score = result;
//				action = actions.get(i);
//			}
//		}
//		return action;
//	}

//	private float weighted_combination(MachineState state)
//			throws TransitionDefinitionException, MoveDefinitionException, GoalDefinitionException {
//		float w1 = (float)1/5;
//		float w2 = (float)4/5;
//		return w1 * mobility(state) + w2 * goal_proximity(state);
//	}

//	private int goal_proximity(MachineState state)
//			throws TransitionDefinitionException, MoveDefinitionException, GoalDefinitionException {
//		return MACHINE.getGoal(state, ROLE);
//	}

//	private float mobility (MachineState state)
//			throws TransitionDefinitionException, MoveDefinitionException, GoalDefinitionException {
//		List <Move> actions = MACHINE.getLegalMoves(state, ROLE);
//		List <Move> feasibles = MACHINE.findActions(ROLE);
////		System.out.println(((float)actions.size()/feasibles.size()) * 100);
//		return ((float)actions.size()/feasibles.size()) * 100;
//	}

//	private float opponent_focus (Role role, List <Role> roles, StateMachine machine, MachineState state)
//			throws TransitionDefinitionException, MoveDefinitionException, GoalDefinitionException {
//		List <List <Move>> actions = machine.getLegalJointMoves(state);
//		int total_combinations = 1;
//		if (roles.size() == 1) return (100 - ((float)actions.size()/machine.findActions(role).size()) * 100);
//		for (int i = 0; i < roles.size(); i++) {
//			if (!(roles.get(i).equals(role))) {
//				List <Move> opponent_moves = machine.findActions(roles.get(i));
//				total_combinations *= opponent_moves.size();
//			}
//		}
//		return (100 - ((float)actions.size()/total_combinations) * 100);
//	}

	@Override
	public void stateMachineStop() {
		// TODO Auto-generated method stub

	}

	@Override
	public void stateMachineAbort() {
		// TODO Auto-generated method stub

	}

	@Override
	public void preview(Game g, long timeout) throws GamePreviewException {
		// TODO Auto-generated method stub

	}

	@Override
	public String getName() {
		// TODO Auto-generated method stub
		return "The_Overachiever";
	}

}

