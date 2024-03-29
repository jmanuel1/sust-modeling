module OBrienEtAl

import AdaptiveCapacity
import Data.SortedSet

%default total

data UntimestampedAction =
  UseVarietiesWithHigherYield
  | Irrigate
  | UsePesticides
  | Fertilize
  | AdjustToOpenEconomy
  | PerformNonAgriculturalActivity

data Action : Nat -> Type where
  Act : UntimestampedAction -> Action _

record Climate where
  constructor MkClimate
  temperature : Double
  precipitation : Double
  {- ... other relevant climatic variables -}

record EnvState t where
  constructor MkEnvState
  climate : Climate
  {- Things like "economic globalization" are rather abstract, so we just
  use floats for those, where a larger number means "more of that thing."
  -}
  economicGlobalization : Double
  economicLiberalization : Double
  agriculturalImportCompetition : Double
  {- For "economic reforms" (policies) and "agricultural policy", let's
  just use sets of strings. -}
  economicPolicies : SortedSet String
  agriculturalPolicies : SortedSet String

record ActorState t where
  constructor MkActorState
  agriculturalProduction : Double
  soilCoverDepth, soilDegradation : Double
  availableGroundwaterThisYear : Double
  adultLiteracyRate : Double
  genderEquity : Double
  workersInAgriculturePercent, landlessAgriculturalWorkersPercent : Double
  irrigationRate : Double
  infrastructureQuality : Double

{- O'Brien et al. are not clear about what type harm values should have.
Since real numbers are used for many of their adaptive capacity
indicators, it will be assumed that Harm t is Double for any t. -}
record Harm t where
  constructor MkHarm
  value : Double

||| The non-strict order on the harm values of O'Brien et al.
harmLessThanOrEqual : Harm _ -> Harm _ -> Bool
harmLessThanOrEqual a b = a.value <= b.value

||| Calculates the harm to the system at a given time. In particular, the
||| harm depends on the climatic conditions at that time.
calculateHarm : EnvState t -> ActorState t -> Action t -> Harm t
calculateHarm envState actorState (Act action) =
  let climate = envState.climate in
    {- O'Brien et al. do not define a harm index or calculation, so this
    is left as a hole. -}
    ?calcHarm

||| Determines what the Indian agricultural sector in each district is
||| able to do in the next time step, depending on socioeconomic and
||| infrastructural factors of the actor state.
available : EnvState t -> ActorState t -> SortedSet (Action (S t))
available envState actState =
  let economicActions = ?availableEconomicActions
        actState.soilCoverDepth actState.soilDegradation
      socioeconomicActions = ?availableSocioeconomicActions
        actState.workersInAgriculturePercent
      infrastructuralFactors = (actState.infrastructureQuality,
                               actState.irrigationRate) in
    ?availableHole

{- It's unclear from the study what notion of uncertainty they are using
in their adaptive capacity index. Even in their sensitivity index, they
use only a control scenario and a single increased carbon dioxide scenario
from one climate model. As they note, a range of scenarios is needed to
demonstrate uncertainty.

It is assumed that their nondeterminism monad is the list monad because it
is simple, and their two climate change scenarios can be thought of as a
list of two possibilities. -}

||| Computes possible states and actions of the system of the next time
||| step, given present conditions.
system : EnvState t ->
         ActorState t ->
         Action t ->
         List (ActorState (S t), Action (S t))
system envState actorState (Act action) = ?systemTransitionFunctionHole

||| Computes possible states of the environment of the next time
||| step, given present conditions.
env : EnvState t -> ActorState t -> Action t -> List (EnvState (S t))
env envState actorState (Act action) = ?environmentTransitionFunctionHole

||| Aggregates a list of uncertain harms by taking the average of every
||| given potential harm value.
aggregate : List (List (Harm t)) -> Harm t
aggregate harms = MkHarm (harmSum / count) where
  flattenedHarms : List (Harm t)
  flattenedHarms = concat harms
  harmSum : Double
  harmSum = sum (map (.value) flattenedHarms)
  count : Double
  count = cast (length flattenedHarms)

modelInstance : LinkedActorEnv List
modelInstance = MkLinkedActorEnv
  EnvState
  ActorState
  Action
  Harm
  harmLessThanOrEqual
  system
  env
  calculateHarm
  available
  aggregate
