module Main

import Data.Fin

-- import Probability.Core
-- import Probability.Monad

%default total

data Prob : Type -> Type where
  Binomial : Nat -> Double -> Prob Nat
  Certainly : a -> Prob a
  Bind : (Prob a) -> (a -> Prob b) -> Prob b
  CustomDist : List (a, Double) -> Prob a

Show a => Show (Prob a) where
  show (Binomial n p) = "Binomial " ++ (show n) ++ " " ++ (show p)
  show (Certainly a) = "Certainly " ++ (show a)
  show (Bind (Binomial n p) _) = "Bind (" ++ (show $ Binomial n p) ++ ") <function>"
  show (Bind a _) = "Bind <dist> <function>"
  show (CustomDist d) = "CustomDist " ++ (show d)

zeroSum : {a: Nat} -> {b: Nat} -> (a + b = 0) -> Either (a = 0) (b = 0)
zeroSum {a = Z} _ = Left Refl
zeroSum {b = Z} _ = Right Refl
zeroSum _ = assert_unreachable

zeroProduct : {a: Nat} -> {b: Nat} -> (a * b = 0) -> Either (a = 0) (b = 0)
zeroProduct {a = Z} _ = Left Refl
zeroProduct {b = Z} _ = Right Refl
zeroProduct _ = assert_unreachable

factNZ : (k: Nat) -> Not (fact k = Z)
factNZ Z p = SIsNotZ p
factNZ (S k) p = case zeroSum p of
  Left q => factNZ k q
  Right q => case zeroProduct q of
    Left r => SIsNotZ $ replace {P = \k => plus (fact k) (mult k (fact k)) = 0} r p
    Right r => factNZ k r

total
choose : Nat -> Nat -> Nat
choose _ Z = 1
choose Z (S _) = 0
choose n (S k') = divNatNZ (product [((n `minus` k'))..n]) (fact (S k')) (factNZ (S k'))

total
binomialPMF : Nat -> Double -> Nat -> Double
binomialPMF n p k = cast (n `choose` k) * (p `pow` k) * ((1.0 - p) `pow` (n `minus` k))

splitBy : (a -> Bool) -> List a -> (List a, List a)
splitBy _ [] = ([], [])
splitBy pred (x::xs) = let (s, t) = splitBy pred xs in
  if pred x then (x::s, t) else (s, x::t)

gatherer : (Eq a, Eq p, Num p) => List (a,p) -> List (a,p) -- copied from https://github.com/lambdacasserole/probability/blob/master/src/Probability/Core.idr
gatherer [] = []
gatherer ((x,p) :: xs) = assert_total $  -- why is assert_total needed?
   let lyln = splitBy (\(z,_) => z == x) xs
       newp = (+) p . sum $ map snd (fst lyln)
   in  (x,newp) :: gatherer (snd lyln)

total
runProb : Prob a -> List (a, Double)
runProb (Binomial n p) = (\k => (k, binomialPMF n p k)) <$> [0..n]
runProb (Certainly a) = [(a, 1.0)]
runProb (Bind a f) = [ (y, q*w) | (x,w) <- runProb a, (y,q) <- runProb (f x) ]
runProb (CustomDist d) = d

Functor Prob where
  map f (Certainly a) = Certainly $ f a
  map f (Bind a g) = Bind a (\x => f <$> g x)
  map f (CustomDist d) = CustomDist $ (\(x, p) => (f x, p)) <$> d
  map f p = CustomDist $ (\(x, p) => (f x, p)) <$> runProb p

Applicative Prob where
  pure = Certainly
  (Certainly f) <*> p = f <$> p
  (Bind pa f) <*> p = Bind pa (\a => (f a) <*> p)
  (CustomDist d) <*> p = CustomDist [ (f x, q*w) | (f,w) <- d, (x,q) <- runProb p ] -- copied from https://github.com/lambdacasserole/probability/blob/master/src/Probability/Core.idr

Monad Prob where
  (Certainly a) >>= f = f a
  (Bind fa f) >>= g = fa >>= (\a => (f a) >>= g)
  fa >>= f = Bind fa f

gather : (Eq a) => Prob a -> Prob a
gather (CustomDist d) = CustomDist (gatherer d)
gather (Bind pa f) = pa >>= (\a => gather $ f a) -- FIXME: Might not gather completely because pa not gathered
gather p = p

mortalityRate : Double
mortalityRate = 0.03



-- chooseZero : (n: Nat) -> choose n 0 = 1
-- chooseZero n = ?cz
--
-- chooseOne : (n: Nat) -> choose (S n) 1 = S n
-- chooseOne n = ?co

safeNatToFin : (n: Nat) -> Fin (S n)
safeNatToFin Z = FZ
safeNatToFin (S n) = FS $ safeNatToFin n

binomial : Nat -> Double -> Prob Nat
binomial = Binomial

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
  dist <- pure (simulate 1 1 3)
  putStrLn "dist"
  printLn dist
  printLn (gatherer $ runProb dist)
