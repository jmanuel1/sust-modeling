Language extensions.

> {-# LANGUAGE DataKinds #-}
> {-# LANGUAGE GADTs #-}
> {-# LANGUAGE TypeFamilies #-}
> {-# LANGUAGE UndecidableInstances #-}
> {-# LANGUAGE ScopedTypeVariables #-}

Imports.

> module Main where
> import Data.Type.Equality
> import Data.Void
> import Data.Bifunctor
> import Control.Monad
> import System.Random
> import Numeric.Natural
> import qualified Data.Type.Nat as TNat
> import Math.Combinatorics.Exact.Binomial
> import qualified Data.Map as Map
> import Control.Monad.State.Lazy

> main :: IO ()
> main = do
>   let

Form a probability distribution over the possible results of a population
simulation running for five steps, and name it dist. The initial parameters are:

Population of first species: 1
Population of second species: 1

I chose these parameters so that runProb dist can finish in a somewhat
reasonable amount of time on my machine.

>     dist :: Prob (Nat, Nat)
>     dist = simulate 1 1 5
>     distMoreSteps = simulate 25 25 250
>   putStrLn "dist"
>   print dist
>   putStrLn ""
>   print (gatherer (case runProb dist of NonEmptyVect xs -> toList xs))
>   putStrLn ""
>   gen <- getStdGen
>   let sampleDist = case runRandomProcess (runSampledProb distMoreSteps 100) gen of (VectWithUnknownLength xs, _) -> toList xs
>   print sampleDist
>   print (sum (snd <$> sampleDist))
>   putStrLn ""

The simulate function is the translation of the model described under the
section "Forward Simulations" at
https://esajournals.onlinelibrary.wiley.com/doi/10.1890/0012-9623-93.4.373.

> simulate :: Nat -> Nat -> Nat -> Prob (Nat, Nat)
> simulate species1Initial species2Initial 0 = pure (species1Initial, species2Initial)
> simulate species1Initial species2Initial k = gather $ do
>   (n1, n2) <- step species1Initial species2Initial
>   gather $ simulate n1 n2 (k - 1)

The step function corresponds to the "For each year" part of the pseudo-code in
the article. It uses some smaller functions to implement the instructions in the
pseudo-code. These functions are based on the probability monad defined below.

> step :: Nat -> Nat -> Prob (Nat, Nat)
> step n1 n2 = gather $ do
>   dead1 <- kill n1 mortalityRate
>   dead2 <- kill n2 mortalityRate
>   gather $ (\(new1,new2) -> ((n1 - dead1) + new1, (n2 - dead2) + new2)) <$> replace dead1 dead2

> kill :: Nat -> Double -> Prob Nat
> kill = binomial

> replace :: Nat -> Nat -> Prob (Nat, Nat)
> replace n1 n2 = gather $ replace' <$> binomial (n1 + n2) (fromIntegral n1 / fromIntegral (n1 + n2)) where
>   replace' n1' = (n1', (n1 + n2) - n1')
>
> binomial :: Nat -> Double -> Prob Nat
> binomial = Binomial
>
> mortalityRate :: Double
> mortalityRate = 0.03

I originally wrote this program in Idris, where I made use of its Nat type.
That's why I alias Natural as Nat.

> type Nat = Natural

> type family Plus (a :: TNat.Nat) b :: TNat.Nat where
>   Plus TNat.Z a = a
>   Plus (TNat.S a) b = TNat.S (Plus a b)

My probability monad. Notice that no interpreter is used in these definitions;
it's up to runProb and runSampledProb to interpret a probability distrubution
and compute a result.

> data Prob :: * -> * where
>   Binomial :: Nat -> Double -> Prob Nat
>   Certainly :: a -> Prob a
>   Bind :: Prob a -> (a -> Prob b) -> Prob b
>   CustomDist :: Vect (TNat.S n) (a, Double) -> Prob a

> instance Show a => Show (Prob a) where
>   show (Binomial n p) = "Binomial " ++ show n ++ " " ++ show p
>   show (Certainly a) = "Certainly " ++ show a
>   show (Bind (Binomial n p) _) = "Bind (" ++ show (Binomial n p) ++ ") <function>"
>   show (Bind a _) = "Bind <dist> <function>"
>   show (CustomDist d) = "CustomDist " ++ show d

> instance Functor Prob where
>   fmap f (Certainly a) = Certainly $ f a
>   fmap f (Bind a g) = Bind a (fmap f . g)
>   fmap f (CustomDist d) = CustomDist $ first f <$> d
>   fmap f p = Bind p (Certainly . f)

> instance Applicative Prob where
>   pure = Certainly
>   (Certainly f) <*> p = f <$> p
>   (Bind pa f) <*> p = Bind pa (\a -> f a <*> p)
>   (CustomDist d) <*> p = Bind (CustomDist d) (\f -> Bind p (pure . f))

> instance Monad Prob where
>   (Certainly a) >>= f = f a
>   (Bind fa f) >>= g = fa >>= (f >=> g)
>   fa >>= f = Bind fa f

This interpreter computes a distribution by computing the probability of every
single possible outcome. Since the number of operations that have to be
performed grows exponentially with the number of binds, runProb is too slow for
all but the smallest distributions.

> runProb :: Prob a -> NonEmptyVect (a, Double)
> runProb (Binomial n p) = case fromList [1..n] of
>   VectWithUnknownLength support -> NonEmptyVect ((\k -> (k, binomialPMF n p k)) <$> 0 :> support)
> runProb (Certainly a) = NonEmptyVect ((a, 1.0) :> Nil)
> runProb (Bind probA f) =
>   case joinedPartly probA f of NonEmptyVect xs -> concatNonempty xs
> runProb (CustomDist d) = NonEmptyVect d

> joinedPartly :: Prob a -> (a -> Prob b) -> NonEmptyVect (NonEmptyVect (b, Double))
> joinedPartly probA f = case probfAs probA f of
>   NonEmptyVect pfAs -> NonEmptyVect ((\(NonEmptyVect dist,p) -> NonEmptyVect (second (p *) <$> dist)) <$> pfAs)

> probfAs :: Prob b -> (b -> Prob a) -> NonEmptyVect (NonEmptyVect (a, Double), Double)
> probfAs probA f = case runProb probA of NonEmptyVect xs -> NonEmptyVect ((\(x,p) -> (runProb (f x), p)) <$> xs)

binomialPMF n p is the probability mass function of the binomial distribution
B(n, p), where n is the number of trials and p is the probability of success for
each trial. binomialPMF n p k is the probability that there are k successes out
of n trials.

> binomialPMF :: Nat -> Double -> Nat -> Double
> binomialPMF n p k = fromIntegral (n `choose` k) * (p ^^ k) * ((1.0 - p) ^^ (n - k))

> concatNonempty' :: Vect n (VectWithUnknownLength a) -> VectWithUnknownLength a
> concatNonempty' Nil = VectWithUnknownLength Nil
> concatNonempty' ((VectWithUnknownLength x1):>xs) = case concatNonempty' xs of
>   VectWithUnknownLength xs' -> VectWithUnknownLength (x1 `append` xs')

> concatNonempty :: Vect (TNat.S n) (NonEmptyVect a) -> NonEmptyVect a
> concatNonempty (x :> Nil) = x
> -- concatNonempty [x1, x2] = (_ ** (snd x1) ++ (snd x2))
> concatNonempty ((NonEmptyVect x1):>xs) = case concatNonempty' ((\(NonEmptyVect ys) -> VectWithUnknownLength ys) <$> xs) of
>   VectWithUnknownLength xs' -> NonEmptyVect (x1 `append` xs')
>
> data NonEmptyVect :: * -> * where
>   NonEmptyVect :: Vect (TNat.S n) a -> NonEmptyVect a
>
> data VectWithUnknownLength :: * -> * where
>   VectWithUnknownLength :: Vect n a -> VectWithUnknownLength a

A vector type that keeps its size in its type.

> data Vect :: TNat.Nat -> * -> * where
>   Nil :: Vect TNat.Z a
>   (:>) :: a -> Vect n a -> Vect (TNat.S n) a

> append :: Vect n a -> Vect m a -> Vect (Plus n m) a
> append Nil ys = ys
> append (x :> xs) ys = x :> append xs ys

> fromList :: [a] -> VectWithUnknownLength a
> fromList [] = VectWithUnknownLength Nil
> fromList (x:xs) = case fromList xs of
>   VectWithUnknownLength vectxs -> VectWithUnknownLength (x :> vectxs)

> toList :: Vect n a -> [a]
> toList Nil = []
> toList (x :> xs) = x : toList xs
>
> instance Show a => Show (Vect n a) where
>   show Nil = "Nil"
>   show (x :> xs) = show x ++ " :> " ++ show xs
>
> instance Functor (Vect n) where
>   fmap _ Nil = Nil
>   fmap f (x :> xs) = f x :> fmap f xs

> instance Foldable (Vect n) where
>   foldMap f Nil = mempty
>   foldMap f (x :> xs) = f x <> foldMap f xs

> gather :: (Eq a) => Prob a -> Prob a
> -- FIXME: Adapt this function for vects
> -- gather (CustomDist d) = CustomDist (gatherer d)
> -- gather (Bind pa f) = pa >>= (\a => gather $ f a) -- FIXME: Might not gather completely because pa not gathered
> gather p = p
>
> gatherer :: (Eq a, Eq p, Num p) => [(a,p)] -> [(a,p)] -- copied from https://github.com/lambdacasserole/probability/blob/master/src/> Probability/Core.idr
> gatherer [] = []
> gatherer ((x,p) : xs) =
>    let lyln = splitBy (\(z,_) -> z == x) xs
>        newp = (+) p . sum $ map snd (fst lyln)
>    in  (x,newp) : gatherer (snd lyln)

> splitBy :: (a -> Bool) -> [a] -> ([a], [a])
> splitBy _ [] = ([], [])
> splitBy pred (x:xs) = let (s, t) = splitBy pred xs in
>   if pred x then (x:s, t) else (s, x:t)

Monte Carlo Prob interpreter: we can approximate distrubutions through repeated
sampling.

> runSampledProb :: (Ord a, RandomGen g) => Prob a -> Nat -> RandomProcess g (VectWithUnknownLength (a, Double))
> runSampledProb prob size = do
>   samples <- runSampled prob size
>   let counts' = case samples of VectWithUnknownLength s -> count s
>   let dist = case counts' of VectWithUnknownLength counts -> VectWithUnknownLength (normalize counts)
>   pure dist

> select :: Double -> Vect (TNat.S n) (a, Double) -> Double -> a
> select _ ((x, p) :> Nil) _ = x
> select target ((x, p):>xps) current =
>   if target <= current + p
>     then x
>     else case xps of
>       Nil -> x
>       (xp:>xps') -> select target (xp:>xps') (current + p)

Generates a (pseudo)-random float between 0 and 1.

> rndDouble :: RandomGen g => RandomProcess g Double
> rndDouble = do
>   gen <- get
>   let (a, gen') = random gen
>   put gen'
>   pure a

> sample :: RandomGen g => Prob a -> RandomProcess g a
> sample (Bind prob f) = do
>   observedFromProb <- sample prob
>   sample (f observedFromProb)
> sample prob = do
>   probability <- rndDouble
>   let dist = runProb prob
>   case dist of NonEmptyVect dist -> pure (select probability dist 0.0)

> normalize :: Vect n (a, Nat) -> Vect n (a, Double)
> normalize counts = second (\c -> fromIntegral c / fromIntegral totalCount) <$> counts where
>   totalCount = foldr (\(_, c) t -> c + t) 0 counts

> count :: Ord a => Vect n a -> VectWithUnknownLength (a, Nat)
> count as = fromList (Map.toAscList (count' as Map.empty))

> count' :: Ord a => Vect n a -> Map.Map a Nat -> Map.Map a Nat
> count' Nil map = map
> count' (a :> as) map = Map.insertWith (+) a 1 (count' as map)

A sort of more fundamental interpreter which computes a list of observations
from a probability distribution.

> runSampled :: RandomGen g => Prob a -> Nat -> RandomProcess g (VectWithUnknownLength a)
> runSampled prob 0 = pure (VectWithUnknownLength Nil)
> runSampled prob size = do
>   observeds <- runSampled prob (size - 1)
>   observed <- sample prob
>   case observeds of VectWithUnknownLength observeds -> pure (VectWithUnknownLength (observed :> observeds))

RandomProcess is just an alias for the State monad that I use so that I don't
have to pass around the random number generator state myself.

> type RandomProcess g a = State g a

> runRandomProcess = runState
