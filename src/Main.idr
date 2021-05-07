module Main

import Data.Fin

import Probability.Core
import Probability.Monad

-- %default total

mortalityRate : Double
mortalityRate = 0.03

choose : Nat -> Nat -> Nat
choose _ Z = 1
choose Z (S _) = 0
choose n k = divNat (product [((n `minus` k) + 1)..n]) (product [1..k])

-- chooseZero : (n: Nat) -> choose n 0 = 1
-- chooseZero n = ?cz
--
-- chooseOne : (n: Nat) -> choose (S n) 1 = S n
-- chooseOne n = ?co

safeNatToFin : (n: Nat) -> Fin (S n)
safeNatToFin Z = FZ
safeNatToFin (S n) = FS $ safeNatToFin n

binomial : Nat -> Double -> Prob Nat
binomial trials successProbability = shape possibilities (binomialProbability <$> possibilities) where
  binomialProbability k = cast (trials `choose` k) * (successProbability `pow` k) * ((1.0 - successProbability) `pow` (trials `minus` k))
  possibilities : List Nat
  possibilities = [0..trials]

kill : (population: Nat) -> Double -> Prob Nat
kill = binomial

replace : Nat -> Nat -> Prob (Nat, Nat)
replace n1 n2 = gather $ replace' <$> binomial (n1 + n2) ((cast n1) / (cast (n1 + n2))) where
  replace' n1' = (n1', (n1 + n2) `minus` n1')

step : Nat -> Nat -> Prob (Nat, Nat)
step n1 n2 = gather $ do
  dead1 <- kill n1 mortalityRate
  dead2 <- kill n2 mortalityRate
  gather $ (\(new1,new2) => ((n1 `minus` dead1) + new1, (n2 `minus` dead2) + new2)) <$> replace dead1 dead2

simulate : Nat -> Nat -> Nat -> Prob (Nat, Nat)
simulate species1Initial species2Initial Z = pure (species1Initial, species2Initial)
simulate species1Initial species2Initial (S k) = gather $ do
  (n1, n2) <- step species1Initial species2Initial
  gather $ simulate n1 n2 k

main : IO ()
main = do
  dist <- pure (simulate 1 1 10)
  putStrLn "dist"
  printLn (runProb dist)
