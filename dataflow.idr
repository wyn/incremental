module Dataflow
-- from paper 
-- The Essence of Dataflow Programming. 
-- Tarmo Uustalu and Varmo Vene. 2006
import Control.Comonad (Comonad(..))


newtype Id a = Id a
             deriving (Show)

instance Functor Id where
  fmap f (Id a) = Id $ f a
  
instance Applicative Id where
  pure = Id
  Id f <*> Id a = Id $ f a
  
instance Monad Id where
  return a = Id a
  Id a >>= k = k a


-- Streams and Comonads stuff
data Stream a = a :< Stream a

instance Show a => Show (Stream a) where
  show (a0 :< (a1 :< (a2 :< _))) = show a0 ++ ", " ++ show a1 ++ ", " ++ show a2 ++ ",...."

                       
mapS :: (a -> b) -> Stream a -> Stream b
mapS f (a:<sa) = f a :< mapS f sa

zipS :: Stream a -> Stream b -> Stream (a, b)
zipS (a:<sa) (b:<sb) = (a,b) :< zipS sa sb

unzipS :: Stream (a, b) -> (Stream a, Stream b)
unzipS pairs = (mapS fst pairs, mapS snd pairs)

newtype SF a b = SF (Stream a -> Stream b)

instance Comonad Id where
  extract (Id a) = a
  extend f a = Id $ f a

data Prod e a = a :& e

instance Functor (Prod e) where
  fmap f (a :& e) = f a :& e
  
instance Comonad (Prod e) where
  extract (a :& _) = a
  extend f pa@(_ :& e) = f pa :& e

askP :: Prod e a -> e
askP (_ :& e) = e

localP :: (e -> e) -> Prod e a -> Prod e a
localP f (a :& e) = a :& f e

instance Functor Stream where
  fmap f (a :< s) = f a :< fmap f s
  
instance Comonad Stream where
  extract (a :< _) = a
  extend f sa@(a :< s) = f sa :< extend f s

nextS :: Stream a ->Stream a
nextS (_ :< s) = s

newtype CoKleisli d a b = CoKleisli (d a -> b)

pair :: (a -> b) -> (a -> b') -> a -> (b, b')
pair f g x = (f x, g x)

-- instance (Comonad d) => Arrow (CoKleisli d) where

str2fun :: Stream a -> Int -> a
str2fun (a :< _) 0 = a
str2fun (_ :< as) i = str2fun as (i-1)

fun2str :: (Int -> a) -> Stream a
fun2str f = fun2str' f 0
  where
    fun2str' f' i = f' i :< fun2str' f' (i+1)

data FunArg s a = (s -> a) :# s

instance Functor (FunArg s) where
  fmap f (sf :# s) = (f . sf) :# s
  
instance Comonad (FunArg s) where
  extract (sf :# s) = sf s
  extend f (sf :# s) = (\s' -> f (sf :# s')) :# s
  
-- TODO dont really understand this one
runFA :: (FunArg Int a -> b) -> Stream a -> Stream b
runFA k as = runFA' k (str2fun as :# 0)
  where
    runFA' k' d@(f :# i) = k' d :< runFA' k' (f :# (i + 1))

-- List the other way around
data List a = Nil | List a :> a
            deriving (Show)
-- a non empty list type
data LV a = List a := a
          deriving (Show)
-- past := value :| future
data LVS a = LV a :| Stream a

instance Show a => Show (LVS a) where
  show (az := a :| as) = show az ++ ", " ++ show a ++ ", " ++ show as
  
instance Functor List where
  fmap f Nil = Nil
  fmap f (as :> a) = fmap f as :> f a

instance Functor LV where
  fmap f (as := a) = fmap f as := f a
  
instance Functor LVS where
  fmap f (az :| as) = fmap f az :| fmap f as
  
instance Comonad LVS where
  extract ((_ := a) :| _) = a
  --            List       value    Stream
  extend k d = cobindL d := k d :| cobindS d
    where
      cobindL (Nil        := _  :|  _      ) = Nil
      cobindL ((az :> a') := a  :|  as     ) = cobindL d' :> k d'
        where -- see how the a' a have been moved to the right
          d' =  az        := a' :| (a :< as)
      cobindS (az      := a  :| (a' :< as')) = k d' :< cobindS d'
        where -- see how the a a' have been moved to the left
          d' = az :> a := a' :| as'

runLVS :: (LVS a -> b) -> Stream a -> Stream b
runLVS k (a' :< as') = runLVS' k (Nil := a' :| as')
  where
    runLVS' k' d@(az := a :| (a'' :< as'')) =
      k' d :< runLVS' k' (az :> a := a'' :| as'')

fbyFA :: a -> (FunArg Int a -> a)
fbyFA a0 (f :# 0) = a0
fbyFA _ (f :# i) = f (i-1)

fbyLVS :: a -> (LVS a -> a)
fbyLVS a0 (Nil := _ :| _) = a0
fbyLVS _ ((_ :> a') := _ :| _) = a'

nextFA :: FunArg Int a -> a
nextFA (f :# i) = f (i+1)

nextLVS :: LVS a -> a
nextLVS (_ := _ :| (a :< _)) = a


instance Comonad LV where
  extract (_ := a) = a
  extend k d@(az := _) = cobindL k az := k d
    where
      cobindL _ Nil = Nil
      cobindL k' (az' :> a) = cobindL k' az' :> k' (az' := a)

fbyLV :: a -> (LV a -> a)
fbyLV a0 (Nil := _) = a0
fbyLV _ ((_ :> a) := _) = a


type Var = String

data Tm = V Var | L Var Tm | Tm :@ Tm -- variables, lambdas, application
        | N Integer | Tm :+ Tm | Tm :- Tm | Tm :* Tm       -- numbers and addition and stuff
        | Tm :== Tm | Tm :<= Tm | TT | FF | Not Tm | If Tm Tm Tm -- equality and bool stuff
        | Rec Tm -- recursion
        | Tm `Fby` Tm
        | Next Tm
        deriving (Show)
                 
-- value types will be numbers, bools and functions
data Val d = I Integer | B Bool | F (d (Val d) -> Val d)

type Env d = [(Var, Val d)]

empty :: [(a, b)]
empty = []


zipL :: List a -> List b -> List (a, b)
zipL Nil _ = Nil
zipL _ Nil = Nil
zipL (az :> a) (bz :> b) = (zipL az bz) :> (a, b)

class Comonad d => ComonadZip d where
  czip :: d a -> d b -> d (a, b)

instance ComonadZip Id where
  czip (Id a) (Id b) = Id (a, b)

instance ComonadZip LVS where
  czip (az := a :| as) (bz := b :| bs) =
    zipL az bz := (a, b) :| zipS as bs

instance ComonadZip LV where
  czip (az := a) (bz := b) = 
    zipL az bz := (a, b)

class ComonadZip d => ComonadEv d where
  ev :: Tm -> d (Env d) -> Val d
  
instance ComonadEv Id where
  ev e denv = _ev e denv

instance ComonadEv LVS where
  ev (Fby e0 e1) denv = ev e0 denv `fbyLVS` extend (ev e1) denv  
  ev (Next e) denv = nextLVS (extend (ev e) denv)
  ev e denv = _ev e denv

instance ComonadEv LV where
  ev (Fby e0 e1) denv = ev e0 denv `fbyLV` extend (ev e1) denv  
  ev e denv = _ev e denv

evClosedI :: Tm -> Val Id
evClosedI e = ev e (Id empty)

emptyL :: Int -> List [(a, b)]
emptyL 0 = Nil
emptyL i = emptyL (i-1) :> empty

emptyS :: Stream [(a, b)]
emptyS = empty :< emptyS

evClosedLVS :: Tm -> Int -> Val LVS
evClosedLVS e i = ev e (emptyL i := empty :| emptyS)

evClosedLV :: Tm -> Int -> Val LV
evClosedLV e i = ev e (emptyL i := empty)

update :: a -> b -> [(a, b)] -> [(a, b)]
update x y xys = (x, y) : xys

unsafeLookup :: Eq a => a -> [(a, b)] -> b
unsafeLookup a0 ((a, b):abs) = if a0 == a then b else unsafeLookup a0 abs

_ev :: ComonadEv d => Tm -> d (Env d) -> Val d
_ev (V x) denv = unsafeLookup x $ extract denv
_ev (e :@ e') denv = case ev e denv of
  F f -> f (extend (ev e') denv)
_ev (Rec e) denv = case ev e denv of
  F f -> f (extend (_ev (Rec e)) denv)
_ev (N n) _ = I n
_ev (e0 :+ e1) denv = case ev e0 denv of
  I n0 -> case ev e1 denv of
    I n1 -> I (n0 + n1)
_ev (e0 :- e1) denv = case ev e0 denv of
  I n0 -> case ev e1 denv of
    I n1 -> I (n0 - n1)
_ev (e0 :* e1) denv = case ev e0 denv of
  I n0 -> case ev e1 denv of
    I n1 -> I (n0 * n1)
_ev TT _ = B True
_ev FF _ = B False
_ev (Not e) denv = case ev e denv of
  B b -> B (not b)
_ev (e0 :== e1) denv = case ev e0 denv of
  B b0 -> case ev e1 denv of
    B b1 -> B (b0 == b1)
_ev (e0 :<= e1) denv = case ev e0 denv of
  B b0 -> case ev e1 denv of
    B b1 -> B (b0 <= b1)
_ev (If e e0 e1) denv = case ev e denv of
  B b -> if b then ev e0 denv else ev e1 denv
_ev (L x e) denv = F (\d -> ev e (fmap repair (czip d denv)))
  where
    repair (a, env) = update x a env
  
-- testing
pos :: Tm
pos = Rec (L "pos" (N 0 `Fby` (V "pos" :+ N 1)))

posVal :: Stream (Val LVS)
posVal = runLVS (ev pos) emptyS
