{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Main where
import Data.Type.Equality
import Data.Void

main :: IO ()
main = do
  let dist = simulate 1 1 3
  putStrLn "dist"
  print dist
  putStrLn ""
  print (gatherer $ toList (case runProb dist of NonEmptyVect xs -> xs))
  putStrLn ""

simulate :: Nat -> Nat -> Nat -> Prob (Nat, Nat)
simulate species1Initial species2Initial Z = pure (species1Initial, species2Initial)
simulate species1Initial species2Initial (S k) = gather $ do
  (n1, n2) <- step species1Initial species2Initial
  gather $ simulate n1 n2 k

step :: Nat -> Nat -> Prob (Nat, Nat)
step n1 n2 = gather $ do
  dead1 <- kill n1 mortalityRate
  dead2 <- kill n2 mortalityRate
  gather $ (\(new1,new2) -> ((n1 `minus` dead1) + new1, (n2 `minus` dead2) + new2)) <$> replace dead1 dead2

kill :: Nat -> Double -> Prob Nat
kill = binomial

replace :: Nat -> Nat -> Prob (Nat, Nat)
replace n1 n2 = gather $ replace' <$> binomial (n1 + n2) ((natToDouble n1) / (natToDouble (n1 + n2))) where
  replace' n1' = (n1', (n1 + n2) `minus` n1')

binomial :: Nat -> Double -> Prob Nat
binomial = Binomial

mortalityRate :: Double
mortalityRate = 0.03

data Nat = Z | S Nat deriving (Eq, Ord)

instance Show Nat where
  show n = show (natToInteger n)

instance Num Nat where
  (+) a b = fromInteger (natToInteger a + natToInteger b)
  (*) a b = fromInteger (natToInteger a * natToInteger b)
  abs = id
  signum Z = Z
  signum _ = S Z
  fromInteger 0 = Z
  fromInteger n = S (fromInteger (n - 1))
  negate n = undefined -- FIXME

instance Enum Nat where
  toEnum 0 = Z
  toEnum n = S (toEnum (n - 1))
  fromEnum n = natToInteger n

instance Real Nat where
  toRational n = toRational (natToInteger n)

instance Integral Nat where
  quotRem a b = ((fromInteger ((natToInteger a) `div` (natToInteger b))), (fromInteger ((natToInteger a) `rem` (natToInteger b))))
  toInteger = natToInteger

natToInteger Z = 0
natToInteger (S n) = 1 + natToInteger n

natToDouble n = 1.0 * natToInteger n

minus a Z = a
minus (S a) (S b) = minus a b
minus Z b = Z

type family Mult (a :: Nat) b :: Nat where
  Mult _ Z = Z
  Mult a (S b) = Plus a (Mult a b)

type family Plus (a :: Nat) b :: Nat where
  Plus a Z = Z
  Plus Z a = a
  Plus a (S b) = S (Plus a b)

data Prob :: * -> * where
  Binomial :: Nat -> Double -> Prob Nat
  Certainly :: a -> Prob a
  Bind :: (Prob a) -> (a -> Prob b) -> Prob b
  CustomDist :: Vect (S n) (a, Double) -> Prob a

instance Show a => Show (Prob a) where
  show (Binomial n p) = "Binomial " ++ (show n) ++ " " ++ (show p)
  show (Certainly a) = "Certainly " ++ (show a)
  show (Bind (Binomial n p) _) = "Bind (" ++ (show $ Binomial n p) ++ ") <function>"
  show (Bind a _) = "Bind <dist> <function>"
  show (CustomDist d) = "CustomDist " ++ (show d)

instance Functor Prob where
  fmap f (Certainly a) = Certainly $ f a
  fmap f (Bind a g) = Bind a (\x -> f <$> g x)
  fmap f (CustomDist d) = CustomDist $ (\(x, p) -> (f x, p)) <$> d
  -- fmap f p = CustomDist $ (\(x, p) -> (f x, p)) <$> case (runProb p) of NonEmptyVect xs -> xs
  fmap f p = Bind p (\x -> Certainly (f x))

instance Applicative Prob where
  pure = Certainly
  (Certainly f) <*> p = f <$> p
  (Bind pa f) <*> p = Bind pa (\a -> (f a) <*> p)
  -- (CustomDist d) <*> p = CustomDist [ (f x, q*w) | (f,w) <- d, (x,q) <- runProb p ] -- copied from https://github.com/lambdacasserole/probability/blob/master/src/Probability/Core.idr
  (CustomDist d) <*> p = Bind (CustomDist d) (\f -> Bind p (pure . f))

instance Monad Prob where
  (Certainly a) >>= f = f a
  (Bind fa f) >>= g = fa >>= (\a -> (f a) >>= g)
  fa >>= f = Bind fa f

-- total
runProb :: Prob a -> (NonEmptyVect (a, Double))
runProb (Binomial n p) = case fromList [1..n] of
  VectWithUnknownLength support -> NonEmptyVect ((\k -> (k, binomialPMF n p k)) <$> 0 :> support)
runProb (Certainly a) = NonEmptyVect ((a, 1.0) :> Nil)
-- runProb {a} (Bind probA f) = (_ ** (\((_,w),(y,q)) => (y, q*w)) <$> cartesianProduct {m = m} (DPair.snd {x = runProb probA}) f'') where
--   f' : (a: Type) -> (b, Double) -> (l: Nat ** Vect (S l) (a, Double))
--   f' a (y,_) = runProb {a = a} ?dxdv --(f x)
--   f'' y' = DPair.snd {x = (f' a y')}
--   m = S $ DPair.fst (f' (head (DPair.snd (runProb probA))))
runProb (Bind probA f) =
  concatNonempty (case joinedPartly of NonEmptyVect xs -> xs) -- unjoined = (\(pA,p) => (runProb pA, p)) <$> probfAs in
  where

    joinedPartly :: NonEmptyVect (NonEmptyVect (a, Double))
    joinedPartly = (\((dist),p) -> (_ ** (\(x,q) -> (x, p*q)) <$> dist)) <$> probfAs
    -- joinedPartly = (_ ** ?cbfdbdb <$> probfAs)
runProb (CustomDist d) = d

probfAs :: Prob b -> (b -> Prob a) -> NonEmptyVect (NonEmptyVect (a, Double), Double)
probfAs probA f = NonEmptyVect ((\(x,p) -> (runProb (f x), p)) <$> case runProb (probA) of NonEmptyVect xs -> xs)

binomialPMF :: Nat -> Double -> Nat -> Double
binomialPMF n p k = natToDouble (n `choose` k) * (p ^^ k) * ((1.0 - p) ^^ (n `minus` k))

choose :: Nat -> Nat -> Nat
choose _ Z = 1
choose (S n) (S Z) = S n
choose Z (S _) = 0
-- if n < k then n `choose` k = 0
choose n k = divNatNZ (divNatNZ (fact n) (fact (n `minus` k))) (fact k)

fact Z = S Z
fact (S n) = (S n) * fact n

type family Fact n :: Nat where
  Fact Z = S Z
  Fact (S n) = Mult (S n) (Fact n)

divNatNZ :: Nat -> Nat -> Nat
divNatNZ a b = (fromInteger ((natToInteger a) `div` (natToInteger b)))

concatNonempty' :: Vect n (VectWithUnknownLength a) -> (VectWithUnknownLength a)
concatNonempty' Nil = VectWithUnknownLength Nil
concatNonempty' (x1:>xs) = (x1) ++ ((concatNonempty' xs))

concatNonempty :: Vect (S n) (NonEmptyVect a) -> (NonEmptyVect a)
concatNonempty (x :> Nil) = x
-- concatNonempty [x1, x2] = (_ ** (snd x1) ++ (snd x2))
concatNonempty (x1:>xs) = (x1) ++ ((concatNonempty' xs))

type Not a = (->) a Void

data NonEmptyVect :: * -> * where
  NonEmptyVect :: Vect (S n) a -> NonEmptyVect a

data VectWithUnknownLength :: * -> * where
  VectWithUnknownLength :: Vect n a -> VectWithUnknownLength a

data Vect :: Nat -> * -> * where
  Nil :: Vect Z a
  (:>) :: a -> Vect n a -> Vect (S n) a

append :: Vect n a -> Vect m a -> Vect (Plus n m) a
append Nil ys = ys
append (x :> xs) (ys) = x :> (append xs ys)

fromList :: [a] -> VectWithUnknownLength a
fromList [] = VectWithUnknownLength Nil
fromList (x:xs) = case fromList xs of
  VectWithUnknownLength vectxs -> VectWithUnknownLength (x :> vectxs)

instance Show a => Show (Vect n a) where
  show Nil = "Nil"
  show (x :> xs) = show x ++ " :> " ++ show xs

instance Functor (Vect n) where
  fmap _ Nil = Nil
  fmap f (x :> xs) = (f x) :> (fmap f xs)

gather :: (Eq a) => Prob a -> Prob a
-- FIXME: Adapt this function for vects
-- gather (CustomDist d) = CustomDist (gatherer d)
-- gather (Bind pa f) = pa >>= (\a => gather $ f a) -- FIXME: Might not gather completely because pa not gathered
gather p = p

gatherer :: (Eq a, Eq p, Num p) => [(a,p)] -> [(a,p)] -- copied from https://github.com/lambdacasserole/probability/blob/master/src/Probability/Core.idr
gatherer [] = []
gatherer ((x,p) : xs) =
   let lyln = splitBy (\(z,_) -> z == x) xs
       newp = (+) p . sum $ map snd (fst lyln)
   in  (x,newp) : gatherer (snd lyln)

splitBy :: (a -> Bool) -> [a] -> ([a], [a])
splitBy _ [] = ([], [])
splitBy pred (x:xs) = let (s, t) = splitBy pred xs in
  if pred x then (x:s, t) else (s, x:t)
