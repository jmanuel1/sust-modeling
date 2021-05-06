module Main

import Probability.Core
import Probability.Monad
import Probability.Display

plusAssoc : (l, c, r : Nat) -> l `plus` (c `plus` r) = (l `plus` c) `plus` r
plusAssoc Z c r = Refl
plusAssoc (S l) c r = rewrite plusAssoc l c r in Refl

mortalityRate : Double
mortalityRate = 0.03

binomial : (trials: Nat) -> Double -> Prob (successes: Nat ** LTE successes trials)
binomial Z _ = pure (0 ** LTEZero)
binomial (S trials') successProbability = do
  success <- shape [False, True] [1.0 - successProbability, successProbability]
  (otherSuccesses ** lte) <- binomial trials' successProbability
  if success
    then pure (S otherSuccesses ** LTESucc lte)
    else pure (otherSuccesses ** lteSuccRight lte)

kill : (population: Nat) -> Double -> Prob (population': Nat ** LTE population' population)
kill n rate = binomial n rate

replace : Nat -> Nat -> Prob (Nat, Nat)
replace n1 n2 = do
  (n1' ** _) <- binomial (n1 + n2) ((cast n1) / (cast (n1 + n2)))
  pure (n1', n1 + n2 - n1')

step : Nat -> Nat -> Prob (Nat, Nat)
step n1 n2 = do
  (dead1 ** _) <- kill n1 mortalityRate
  (dead2 ** _) <- kill n2 mortalityRate
  (new1, new2) <- replace dead1 dead2
  pure (n1 - dead1 + new1, n2 - dead2 + new2)

simulate : Nat -> Nat -> Nat -> Prob (Nat, Nat)
simulate species1Initial species2Initial Z = pure (species1Initial, species2Initial)
simulate species1Initial species2Initial (S k) = do
  (n1, n2) <- step species1Initial species2Initial
  simulate n1 n2 k

main : IO ()
main = do
  putStrLn "Hello there!"
  putStrLn $ (show (runProb (gather $ simulate 5 5 1)))
