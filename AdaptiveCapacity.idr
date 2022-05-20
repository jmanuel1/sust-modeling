module AdaptiveCapacity

import Data.SortedSet

%default total

public export
record LinkedActorEnv (0 nondet : Type -> Type) where
  constructor MkLinkedActorEnv
  EnvironmentState, ActorState, Action, Harm : Nat -> Type
  ||| The non-strict partial order on Harm t, for arbitrary t.
  |||
  ||| NOTE: This is not defined through Control.Order.PartialOrder because
  ||| Harm t and Harm u are different types.
  leq : forall t, u. Harm t -> Harm u -> Bool
  ||| The actor state transition function that describes the evolution of
  ||| the actor over time and the actions it performs.
  actor : forall t.
          Monad nondet =>
          EnvironmentState t ->
          ActorState t ->
          -- the action currently being done
          Action t ->
          nondet (ActorState (S t),
                  -- what will be done in the next time step
                  Action (S t))
  ||| The environment state transition function that describes the
  ||| evolution of the environment over time.
  environment : forall t.
                Monad nondet =>
                -- state of the environment at time t
                EnvironmentState t ->
                -- state of the system at time t (so folding observers
                -- into the environment makes sense)
                ActorState t ->
                -- action performed by system at time t
                Action t ->
                -- state of the environment at time (t + 1)
                nondet (EnvironmentState (S t))
  ||| Determines the harmfulness of the present action and states to the
  ||| system.
  measureHarm : forall t.
                EnvironmentState t ->
                ActorState t ->
                Action t ->
                Harm t
  ||| Determines the set of actions the system can perform in the next
  ||| time step, given the current environment state and system state.
  |||
  ||| Adaptive capacity is based on the set of actions that the actor can
  ||| perform in a given state. The available actions can depend on wider
  ||| institutional structures, so availableActions should be explicitly
  ||| be a function of the environment state.
  availableActions : forall t.
                     EnvironmentState t ->
                     ActorState t ->
                     SortedSet (Action (S t))
  ||| Combines all of the harms in a list of uncertain harms into a single
  ||| harm value. It could be some sort of average, for example.
  aggregateHarms : forall t.
                   Monad nondet =>
                   List (nondet (Harm t)) ->
                   Harm t

||| Nondeterministically find what the harm to the system might be in the
||| next time step, given an action to perform in the next step.
(.measureHarmInPresenceOfAction) : forall t.
                                   (lae : LinkedActorEnv nondet) ->
                                   Monad nondet =>
                                   lae.EnvironmentState t ->
                                   lae.ActorState t ->
                                   lae.Action t ->
                                   lae.Action (S t) ->
                                   nondet (lae.Harm (S t))
(.measureHarmInPresenceOfAction) lae envState actorState action nextAction =
  do
    (nextActorState, _) <- lae.actor envState actorState action
    nextEnvState <- lae.environment envState actorState action
    pure $ lae.measureHarm nextEnvState nextActorState nextAction

||| Nondeterministically computes the possible harm in the next time step
||| for each available action.
(.potentialHarms) : (lae : LinkedActorEnv nondet) ->
                    Monad nondet =>
                    lae.EnvironmentState t ->
                    lae.ActorState t ->
                    lae.Action t ->
                    List (nondet $ lae.Harm (S t))
(.potentialHarms) lae input state currentAction =
  map (lae.measureHarmInPresenceOfAction input state currentAction)
    (SortedSet.toList $ lae.availableActions input state)

||| Determine if the system has adaptive capacity, given the current
||| environment state, system state, and action. This depends on the
||| ability of the system to adapt in the next time step, where ability
||| is every possible action the system could take in the next step.
(.hasAdaptiveCapacity) : (lae : LinkedActorEnv nondet) ->
                         Monad nondet =>
                         lae.EnvironmentState t ->
                         lae.ActorState t ->
                         lae.Action t ->
                         Bool
(.hasAdaptiveCapacity) lae envState actorState currentAction =
  lae.leq futureHarm currentHarm where
    futureHarm : lae.Harm (S t)
    futureHarm = lae.aggregateHarms
      (lae.potentialHarms envState actorState currentAction)
    currentHarm : lae.Harm t
    currentHarm = lae.measureHarm envState actorState currentAction

data (.Evolution) : LinkedActorEnv _ ->
                    Nat ->
                    (0 nextTime : Nat) ->
                    Type where
  Lin : lae.Evolution 0 t
  (:<) : lae.Evolution n t ->
         (lae.ActorState t, lae.EnvironmentState t, lae.Action t) ->
         lae.Evolution (S n) (S t)

||| Compute the evolution of the system and environment starting with the
||| present and then n steps into the future. This function demonstrates
||| that the functions, data structures, and types above can be composed.
||| It might be useful for exploring the future of the actor and
||| environment, too.
evolve : (n : Nat) ->
         (lae : LinkedActorEnv nondet) ->
         Monad nondet =>
         lae.ActorState t ->
         lae.EnvironmentState t ->
         lae.Action t ->
         nondet (lae.Evolution (S n) (S (n + t)))
evolve 0 lae initActState initEnvState initAction =
  pure [<(initActState, initEnvState, initAction)]
evolve (S n) lae initActState initEnvState initAction = do
  prev@(_ :< (prevActState, prevEnvState, prevAction)) <-
    evolve n lae initActState initEnvState initAction
  (newActState, newAction) <-
    lae.actor prevEnvState prevActState prevAction
  newEnvState <- lae.environment prevEnvState prevActState prevAction
  pure (prev :< (newActState, newEnvState, newAction))
