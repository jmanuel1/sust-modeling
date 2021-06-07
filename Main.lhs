Language extensions.

> {-# LANGUAGE DataKinds #-}
> {-# LANGUAGE GADTs #-}
> {-# LANGUAGE TypeFamilies #-}
> {-# LANGUAGE UndecidableInstances #-}
> {-# LANGUAGE ScopedTypeVariables #-}
> {-# LANGUAGE RankNTypes #-}

Imports.

> module Main where
> import Control.Monad
> import System.Random
> import Numeric.Natural
> import qualified Data.Type.Nat as TNat
> import Math.Combinatorics.Exact.Binomial
> import qualified Data.Map as Map
> import Control.Monad.State.Lazy
> import qualified Data.List.NonEmpty as NE
> import Data.List.NonEmpty (NonEmpty(..))
> import Control.Monad.Free
> import Data.Functor.Classes
> import Data.Bifunctor (first, second)
> import Data.List

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
>   -- print dist -- WARNING: Spams terminal
>   print (gatherer (NE.toList (runProb dist)))
>   putStrLn ""
>   gen <- getStdGen
>   let sampleDist = fst $ runRandomProcess (runSampledProb distMoreSteps 100) gen
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
> replace 0 0 = pure (0, 0) -- avoid division by zero
> replace n1 n2 = gather $ replace' <$> binomial (n1 + n2) (fromIntegral n1 / fromIntegral (n1 + n2)) where
>   replace' n1' = (n1', (n1 + n2) - n1')

> mortalityRate :: Double
> mortalityRate = 0.03

I originally wrote this program in Idris, where I made use of its Nat type.
That's why I alias Natural as Nat.

> type Nat = Natural

> type family Plus (a :: TNat.Nat) b :: TNat.Nat where
>   Plus TNat.Z a = a
>   Plus (TNat.S a) b = TNat.S (Plus a b)

My probability monad, as a free monad. Notice that no interpreter is used in
these definitions; it's up to runProb and runSampledProb to interpret a
probability distrubution and compute a result.

> type Prob a = Free Distribution a

> data Distribution :: * -> * where
>   BinomialShape :: Nat -> Double -> (Nat -> a) -> Distribution a
>   CustomDist :: Vect (TNat.S n) (a, Double) -> Distribution a

> instance Functor Distribution where
>   fmap f (BinomialShape n p g) = BinomialShape n p (f . g)
>   fmap f (CustomDist d) = CustomDist (first f <$> d)

> binomial :: Nat -> Double -> Prob Nat
> binomial n p = Free (BinomialShape n p Pure)

> instance Show1 Distribution where
>   liftShowsPrec argShowsPrec _ _ (BinomialShape n p f) = (++) ("(BinomialShape " ++ show n ++ " " ++ show p ++ " <support: " ++ intercalate ", " ((showArg . f) <$> [0..n]) ++ ">)") where
>     showArg a = argShowsPrec 0 a ""
>   liftShowsPrec argShowsPrec _ _ (CustomDist d) = (++) ("(CustomDist " ++ showVect (argShowsPrec 0) d ++ ")") where
>     showVect :: (a -> String -> String) -> Vect n (a, Double) -> String
>     showVect _ Nil = "Nil"
>     showVect showEl ((x, p) :> xs) = "((" ++ showEl x ", " ++ show p ++ ") :> " ++ showVect showEl xs ++ ")"

This interpreter computes a distribution by computing the probability of every
single possible outcome. Since the number of operations that have to be
performed grows exponentially with the number of binds, runProb is too slow for
all but the smallest distributions.

> runProb :: Prob a -> NE.NonEmpty (a, Double)
> runProb (Free dist) = flatten (first runProb <$> shape dist)
> runProb (Pure value) = (value, 1.0) :| []

> shape :: Distribution a -> NE.NonEmpty (a, Double)
> shape (BinomialShape n p f) = let support = 0 :| [1..n] in
>   ((\k -> (f k, binomialPMF n p k)) <$> support)
> shape (CustomDist (d :> ds)) = d :| toList ds

> flatten :: NE.NonEmpty (NE.NonEmpty (a, Double), Double) -> NE.NonEmpty (a, Double)
> flatten shapeOfShapes = do
>   (shape, p) <- shapeOfShapes
>   (value, q) <- shape
>   pure (value, p*q)

binomialPMF n p is the probability mass function of the binomial distribution
B(n, p), where n is the number of trials and p is the probability of success for
each trial. binomialPMF n p k is the probability that there are k successes out
of n trials.

> binomialPMF :: Nat -> Double -> Nat -> Double
> binomialPMF n p k = fromIntegral (n `choose` k) * (p ^^ k) * ((1.0 - p) ^^ (n - k))

A vector type that keeps its size in its type.

> data Vect :: TNat.Nat -> * -> * where
>   Nil :: Vect TNat.Z a
>   (:>) :: a -> Vect n a -> Vect (TNat.S n) a

> append :: Vect n a -> Vect m a -> Vect (Plus n m) a
> append Nil ys = ys
> append (x :> xs) ys = x :> append xs ys

> toList :: Vect n a -> [a]
> toList Nil = []
> toList (x :> xs) = x : toList xs

> vectFromList :: [a] -> (forall n. Vect n a -> r) -> r
> vectFromList [] k = k Nil
> vectFromList (x:xs) k = vectFromList xs (\xs' -> k (x :> xs'))

> withNonEmptyVect :: NE.NonEmpty a -> (forall n. Vect (TNat.S n) a -> r) -> r
> withNonEmptyVect (x :| xs) k = vectFromList xs (\xs' -> k (x :> xs'))

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

> runSampledProb :: (Ord a, RandomGen g) => Prob a -> Nat -> RandomProcess g [(a, Double)]
> runSampledProb prob size = do
>   samples <- runSampled prob size
>   let counts = vectFromList samples count
>   let dist = vectFromList counts (toList . normalize)
>   pure dist

Computes an inverse cumulative mass function from the shape of a discrete
distribution. The first argument is the target cumulative probability, and the
third argument is an accumulator that should be set to 0.0 by other functions.

> inverseCMF :: Double -> Vect (TNat.S n) (a, Double) -> Double -> a
> inverseCMF target ((x, p):>xps) current =
>   if target <= current + p
>     then x
>     else case xps of
>       Nil -> x
>       (xp:>xps') -> inverseCMF target (xp:>xps') (current + p)

Generates a (pseudo)-random float between 0 and 1.

> rndDouble :: RandomGen g => RandomProcess g Double
> rndDouble = do
>   gen <- get
>   let (a, gen') = random gen
>   put gen'
>   pure a

> sample :: RandomGen g => Prob a -> RandomProcess g a
> sample (Free dist) = do
>   prob <- sampleDist dist
>   sample prob
> sample (Pure value) = pure value

> sampleDist :: RandomGen g => Distribution a -> RandomProcess g a
> sampleDist prob = do
>   probability <- rndDouble
>   let dist = shape prob
>   pure (withNonEmptyVect dist (\dist -> inverseCMF probability dist 0.0))

> normalize :: Vect n (a, Nat) -> Vect n (a, Double)
> normalize counts = second (\c -> fromIntegral c / fromIntegral totalCount) <$> counts where
>   totalCount = foldr (\(_, c) t -> c + t) 0 counts

> count :: Ord a => Vect n a -> [(a, Nat)]
> count as = Map.toAscList (count' as Map.empty)

> count' :: Ord a => Vect n a -> Map.Map a Nat -> Map.Map a Nat
> count' Nil map = map
> count' (a :> as) map = Map.insertWith (+) a 1 (count' as map)

A sort of more fundamental interpreter which computes a list of observations
from a probability distribution.

> runSampled :: RandomGen g => Prob a -> Nat -> RandomProcess g [a]
> runSampled prob 0 = pure []
> runSampled prob size = do
>   observeds <- runSampled prob (size - 1)
>   observed <- sample prob
>   pure (observed : observeds)

RandomProcess is just an alias for the State monad that I use so that I don't
have to pass around the random number generator state myself.

> type RandomProcess g a = State g a

> runRandomProcess = runState
