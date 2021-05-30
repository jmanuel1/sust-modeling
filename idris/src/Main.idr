module Main

import Effect.Random
import Effect.StdIO
import Effects
import Data.Vect

-- import Probability.Core
-- import Probability.Monad

%default total

{- Probabilistic programming -}

data Prob : Type -> Type where
  Binomial : Nat -> Double -> Prob Nat
  Certainly : a -> Prob a
  Bind : (Prob a) -> (a -> Prob b) -> Prob b
  CustomDist : Vect (S n) (a, Double) -> Prob a

Show a => Show (Prob a) where
  show (Binomial n p) = "Binomial " ++ (show n) ++ " " ++ (show p)
  show (Certainly a) = "Certainly " ++ (show a)
  show (Bind (Binomial n p) _) = "Bind (" ++ (show $ Binomial n p) ++ ") <function>"
  show (Bind a _) = "Bind <dist> <function>"
  show (CustomDist d) = "CustomDist " ++ (show d)

-- NOTE: It seems Idris won't accept this as total unless I handle the
-- 'impossible' case (that's also why choose wasn't reducing at compile time).
zeroSum : {a: Nat} -> {b: Nat} -> (a + b = 0) -> Either Void ((a = 0), (b = 0))
zeroSum {a = Z} Refl = Right (Refl, Refl)
zeroSum {a} {b = Z} prf = Right (replace {P = \x => x = 0} (plusZeroRightNeutral a) prf, Refl)
zeroSum {a = S a} {b = S b} prf = Left $ SIsNotZ prf

factNZ : {k: Nat} -> Not (fact k = Z)
factNZ {k = Z} p = SIsNotZ p
factNZ {k = (S k)} p = case zeroSum p of
  Left v => v
  Right (q1, _) => factNZ q1

-- factBetween : Nat -> Nat -> Nat
-- factBetween n m = if n == m then n else if n > m then 0 else  (factBetween n (pred m)) * (m)

total
choose : Nat -> Nat -> Nat
choose _ Z = 1
choose (S n) (S Z) = S n
choose Z (S _) = 0
-- if n < k then n `choose` k = 0
choose n k = divNatNZ (divNatNZ (fact n) (fact (n `minus` k)) factNZ) (fact k) factNZ

chooseZero : {n: Nat} -> choose n Z = 1
chooseZero = Refl

chooseOne : {n: Nat} -> choose (S n) 1 = S n
chooseOne = Refl

-- chooseNLessK : choose n (n + m + 1) = 0
-- chooseNLessK = ?csdvsd

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

-- vectNatEnumFromTo : (a, b: Nat) -> {auto prf: LTE a b} -> Vect (b - a + 1) Nat
-- vectNatEnumFromTo a b = vectNatEnumFromTo' a (b - a) where
--   vectNatEnumFromTo' a Z = [a]
--   vectNatEnumFromTo' a (S n) = a :: vectNatEnumFromTo' (a + 1) n

-- cartesianProduct : Vect n a -> (a -> Vect m b) -> Vect (n * m) (a, b)
-- cartesianProduct [] _ = []
-- cartesianProduct {n} {m = Z} _ _ = rewrite multZeroRightZero n in []
-- cartesianProduct (x::xs) fys = ((\y => (x, y)) <$> fys x) ++ cartesianProduct xs fys
--
-- cartesianProduct' : Vect n a -> (a -> (m: Nat ** Vect m b)) -> Vect (n * m) (a, b)
-- cartesianProduct' xs fys = cartesianProduct xs (DPair.snd . fys)

concatNonempty' : Vect n (m: Nat ** Vect (S m) a) -> (k: Nat ** Vect k a)
concatNonempty' [] = (_ ** [])
concatNonempty' (x1::xs) = (_ ** (snd x1) ++ (snd (concatNonempty' xs)))

concatNonempty : Vect (S n) (m: Nat ** Vect (S m) a) -> (k: Nat ** Vect (S k) a)
concatNonempty [x] = x
-- concatNonempty [x1, x2] = (_ ** (snd x1) ++ (snd x2))
concatNonempty (x1::xs) = (_ ** (snd x1) ++ (snd (concatNonempty' xs)))

total
runProb : Prob a -> (k: Nat ** Vect (S k) (a, Double))
runProb (Binomial n p) = (_ ** (\k => (k, binomialPMF n p k)) <$> 0 :: fromList [1..n])
runProb (Certainly a) = (_ ** [(a, 1.0)])
-- runProb {a} (Bind probA f) = (_ ** (\((_,w),(y,q)) => (y, q*w)) <$> cartesianProduct {m = m} (DPair.snd {x = runProb probA}) f'') where
--   f' : (a: Type) -> (b, Double) -> (l: Nat ** Vect (S l) (a, Double))
--   f' a (y,_) = runProb {a = a} ?dxdv --(f x)
--   f'' y' = DPair.snd {x = (f' a y')}
--   m = S $ DPair.fst (f' (head (DPair.snd (runProb probA))))
runProb {a} (Bind probA f) =
  concatNonempty (snd joinedPartly) -- unjoined = (\(pA,p) => (runProb pA, p)) <$> probfAs in
  where
    probfAs : (k: Nat ** Vect (S k) ((l: Nat ** Vect (S l) (a, Double)), Double))
    probfAs = assert_total (_ ** (\(x,p) => (runProb (f x), p)) <$> snd (runProb (assert_smaller (Bind probA f) probA)))
    joinedPartly : (k: Nat ** Vect (S k) (l: Nat ** Vect (S l) (a, Double)))
    joinedPartly = (_ ** (\((_**dist),p) => (_ ** (\(x,q) => (x, p*q)) <$> dist)) <$> snd probfAs)
    -- joinedPartly = (_ ** ?cbfdbdb <$> probfAs)
runProb (CustomDist d) = (_ ** d)

Functor Prob where
  map f (Certainly a) = Certainly $ f a
  map f (Bind a g) = Bind a (\x => f <$> g x)
  map f (CustomDist d) = CustomDist $ (\(x, p) => (f x, p)) <$> d
  map f p = CustomDist $ (\(x, p) => (f x, p)) <$> (snd $ runProb p)

Applicative Prob where
  pure = Certainly
  (Certainly f) <*> p = f <$> p
  (Bind pa f) <*> p = Bind pa (\a => (f a) <*> p)
  -- (CustomDist d) <*> p = CustomDist [ (f x, q*w) | (f,w) <- d, (x,q) <- runProb p ] -- copied from https://github.com/lambdacasserole/probability/blob/master/src/Probability/Core.idr
  (CustomDist d) <*> p = Bind (CustomDist d) (\f => Bind p (pure . f))

Monad Prob where
  (Certainly a) >>= f = f a
  (Bind fa f) >>= g = fa >>= (\a => (f a) >>= g)
  fa >>= f = Bind fa f

gather : (Eq a) => Prob a -> Prob a
-- FIXME: Adapt this function for vects
-- gather (CustomDist d) = CustomDist (gatherer d)
-- gather (Bind pa f) = pa >>= (\a => gather $ f a) -- FIXME: Might not gather completely because pa not gathered
gather p = p

mortalityRate : Double
mortalityRate = 0.03

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

{- Error propagation -}

data Uncertain value = MkUncertain value value

interface SquareRootable a where
  sqrt : a -> a

SquareRootable Double where
  sqrt = Doubles.sqrt

square : Num a => a -> a
square a = a * a

norm : (Num a, SquareRootable a) => List a -> a
norm values = sqrt $ sum (square <$> values)

(Fractional value, SquareRootable value) => Num (Uncertain value) where
  -- FIXME: Account for correlation
  (+) (MkUncertain a aUncertainty) (MkUncertain b bUncertainty) = MkUncertain (a + b) (norm [aUncertainty, bUncertainty])
  (*) (MkUncertain a aUncertainty) (MkUncertain b bUncertainty) = (MkUncertain (a * b) (a * b * norm [aUncertainty/a, bUncertainty/b]))
  fromInteger i = MkUncertain (fromInteger i) 0

(SquareRootable value, Fractional value) => Fractional (Uncertain value) where
  (MkUncertain a aUncertainty) / (MkUncertain b bUncertainty) = MkUncertain (a / b) (a / b * norm [aUncertainty/a, bUncertainty/b])

Show value => Show (Uncertain value) where
  show (MkUncertain a aUncertainty) = show a ++ " +- " ++ show aUncertainty

interface Scalable a where
  (*) : a -> Double -> a

Scalable Double where
  (*) = Interfaces.(*)

mean : (Scalable a, Num a) => (prob: Prob a) -> a
mean (Binomial n p) = (Main.(*) n p) -- probably not what you want
mean (Certainly a) = a
mean (CustomDist d) = sum [x * p | (x, p) <- d]
mean (Bind pa f) = sum [x * p | (x, p) <- snd $ runProb (pa >>= f)]

-- population standardDeviation (QUESTION: should it be sample instead?)
standardDeviation : (SquareRootable a, Scalable a, Neg a) => (prob: Prob a) -> a
standardDeviation (Binomial n p) = sqrt (Main.(*) (Main.(*) n p) (1.0 - p)) -- probably not what you want
standardDeviation (Certainly _) = 0
standardDeviation (CustomDist d) = let mu = mean (CustomDist d) in
  sqrt $ sum [square (mu - x) * p | (x, p) <- d]
standardDeviation (Bind pa f) = let mu = mean (Bind pa f) in
  sqrt $ sum [square (mu - x) * p | (x, p) <- snd $ runProb (pa >>= f)]

probToUncertain : (SquareRootable a, Scalable a, Neg a, Fractional a) => (prob: Prob a) -> Uncertain a
probToUncertain dist = MkUncertain (mean dist) (Main.(*) (standardDeviation dist) 0.5)

{- Estimate distributions by sampling (Monte Carlo) -}

select : Double -> Vect (S n) (a, Double) -> Double -> a
select _ [(x, p)] _ = x
select target ((x, p)::xps) current =
  if target >= current + p
    then x
    else case xps of
      [] => x
      (xp::xps') => select target (xp::xps') (current + p)

-- Copied from https://bl.ocks.org/justinmanley/f2e169feb32e06e06c2f
||| Naively generate a (pseudo)-random float between 0 and 1.
rndDouble : Integer -> Eff Double [RND]
rndDouble max = do
	rnd <- assert_total $ rndInt 0 max
	pure (fromInteger rnd / fromInteger max)

sample : Prob a -> Eff a [RND, STDIO]
sample (Bind prob f) = do
  observedFromProb <- sample prob
  putStrLn "Bind: sampled prob"
  result <- sample (f observedFromProb)
  putStrLn "Bind: sampled f _"
  pure result
sample prob = do
  putStrLn "Sampling from an arbitrary distribution"
  probability <- rndDouble (2 `pow` 20)
  (_ ** dist) <- pure (runProb prob)
  pure $ select probability dist 0.0

Applicative (Pair Int) where
  pure a = (0, a)

  f <*> fa = (fst fa, (snd f) (snd fa))

main : IO ()
main = do
  dist <- pure (simulate 1 1 3)
  putStrLn "dist"
  printLn dist
  printLn (gatherer $ toList (snd (runProb dist)))
  printLn $ (MkUncertain 0.172807 0.000008) / ((MkUncertain 13.7 0.3) * (MkUncertain 1.0 0.1)) -- 0.013 ± 0.001 (https://chem.libretexts.org/Bookshelves/Analytical_Chemistry/Supplemental_Modules_(Analytical_Chemistry)/Quantifying_Nature/Significant_Digits/Propagation_of_Error)
  printLn $ probToUncertain (cast {to=Double} <$> binomial 5 0.5) -- 2.5 +- 0.559
  -- printLn (run $ sample (simulate 1 1 3))
