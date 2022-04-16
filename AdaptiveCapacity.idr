module AdaptiveCapacity

import Data.SortedSet

%default total

public export
record LinkedActorEnv (0 nondet : Type -> Type) where
  constructor MkLinkedActorEnv
  EnvironmentState, ActorState, Action, Harm : Nat -> Type
  -- The non-strict partial order on Harm t, for arbitrary t.
  -- NOTE: This is not defined through Control.Order.PartialOrder because Harm t and Harm u are different types.
  leq : forall t, u. Harm t -> Harm u -> Bool
  actor : forall t.
          Monad nondet =>
          EnvironmentState t ->
          ActorState t ->
          Action t ->                             -- the action currently being done
          nondet (ActorState (S t),
                  Action (S t))                   -- what will be done in the next time step
  environment : forall t.
                Monad nondet =>
                EnvironmentState t ->                -- state of the environment at time t
                ActorState t ->                      -- state of the system at time t (so folding observers into the environment makes sense)
                Action t ->                          -- action performed by system at time t
                nondet (EnvironmentState (S t))      -- state of the environment at time (t + 1)
  measureHarm : forall t. EnvironmentState t -> ActorState t -> Action t -> Harm t
  -- Adaptive capacity is based on the set of actions that the actor can perform
  -- in a given state. The available actions can depend on wider institutional
  -- structures, so availableActions should be explicitly be a function of the
  -- environment state.
  availableActions : forall t. EnvironmentState t -> ActorState t -> SortedSet (Action (S t))
  -- There is a function
  aggregateHarms : forall t. Monad nondet => List (nondet (Harm t)) -> Harm t
  -- that combines all of the harms in a list of harms into a single harm value.
  -- It could be some sort of average, for example.

data (.Evolution) : LinkedActorEnv _ -> Nat -> (0 nextTime : Nat) -> Type where
  Lin : lae.Evolution 0 t
  (:<) : lae.Evolution n t -> (lae.ActorState t, lae.EnvironmentState t, lae.Action t) -> lae.Evolution (S n) (S t)

evolve : (n : Nat) -> (lae : LinkedActorEnv nondet) -> Monad nondet => lae.ActorState t -> lae.EnvironmentState t -> lae.Action t -> nondet (lae.Evolution (S n) (S (n + t)))
evolve 0 lae initActState initEnvState initAction = pure [<(initActState, initEnvState, initAction)]
evolve (S n) lae initActState initEnvState initAction = do
  prev@(_ :< (prevActState, prevEnvState, prevAction)) <- (evolve n lae initActState initEnvState initAction)
  (newActState, newAction) <- lae.actor prevEnvState prevActState prevAction
  newEnvState <- lae.environment prevEnvState prevActState prevAction
  pure (prev :< (newActState, newEnvState, newAction))

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

-- Adaptive capacity over a local time horizon:
-- Adaptive capacity based on all possible actions

-- The harm in the presence of each available action is
(.potentialHarms) : (lae : LinkedActorEnv nondet) ->
                    Monad nondet =>
                    lae.EnvironmentState t ->
                    lae.ActorState t ->
                    lae.Action t ->
                    List (nondet $ lae.Harm (S t))
-- NOTE: My original definition used a "map" from sets to sets, which is wrong
-- because there should be a resultant measureHarmInPresenceOfAction value for
-- each available action, and some of those values might be equal. The fact
-- that there is no Data.SortedSet.map defined led me to catch this error.
(.potentialHarms) lae input state currentAction =
  map (lae.measureHarmInPresenceOfAction input state currentAction)
    (SortedSet.toList $ lae.availableActions input state)

-- NOTE: originally, I accidentally got the direction of the inequality wrong
(.hasAdaptiveCapacity) : (lae : LinkedActorEnv nondet) ->
                         Monad nondet =>
                         lae.EnvironmentState t ->
                         lae.ActorState t ->
                         lae.Action t ->
                         Bool
(.hasAdaptiveCapacity) lae envState actorState currentAction = lae.leq futureHarm currentHarm where
  futureHarm : lae.Harm (S t)
  futureHarm = lae.aggregateHarms (lae.potentialHarms envState actorState currentAction)
  currentHarm : lae.Harm t
  currentHarm = lae.measureHarm envState actorState currentAction
