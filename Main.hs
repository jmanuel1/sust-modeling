{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}

module Main where

main :: IO ()
main = do
  dist <- pure (simulate 1 1 3)
  putStrLn "dist"
  print dist
  putStrLn ""
  print (gatherer $ toList (snd (runProb dist)))
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

data Nat = S Nat | Z deriving (Eq)

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

natToInteger Z = 0
natToInteger (S n) = 1 + natToInteger n

natToDouble n = 1.0 * natToInteger n

minus a Z = a
minus (S a) (S b) = minus a b
minus Z b = Z

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
  fmap f p = CustomDist $ (\(x, p) -> (f x, p)) <$> (snd $ runProb p)

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
runProb :: Prob a -> (k: Nat ** Vect (S k) (a, Double))
runProb (Binomial n p) = (_ ** (\k -> (k, binomialPMF n p k)) <$> 0 :: fromList [1...n])
runProb (Certainly a) = (_ ** [(a, 1.0)])
-- runProb {a} (Bind probA f) = (_ ** (\((_,w),(y,q)) => (y, q*w)) <$> cartesianProduct {m = m} (DPair.snd {x = runProb probA}) f'') where
--   f' : (a: Type) -> (b, Double) -> (l: Nat ** Vect (S l) (a, Double))
--   f' a (y,_) = runProb {a = a} ?dxdv --(f x)
--   f'' y' = DPair.snd {x = (f' a y')}
--   m = S $ DPair.fst (f' (head (DPair.snd (runProb probA))))
runProb {a} (Bind probA f) =
  concatNonempty (snd joinedPartly) -- unjoined = (\(pA,p) => (runProb pA, p)) <$> probfAs in
  where
    probfAs :: (k: Nat ** Vect (S k) ((l: Nat ** Vect (S l) (a, Double)), Double))
    probfAs = (_ ** (\(x,p) -> (runProb (f x), p)) <$> snd (runProb (assert_smaller (Bind probA f) probA)))
    joinedPartly :: (k: Nat ** Vect (S k) (l: Nat ** Vect (S l) (a, Double)))
    joinedPartly = (_ ** (\((_**dist),p) => (_ ** (\(x,q) => (x, p*q)) <$> dist)) <$> snd probfAs)
    -- joinedPartly = (_ ** ?cbfdbdb <$> probfAs)
runProb (CustomDist d) = (_ ** d)

data Vect :: Nat -> * -> * where
  Nil :: Vect Z a
  (:>) :: a -> Vect n a -> Vect (S n) a

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
   in  (x,newp) :: gatherer (snd lyln)
