module Stuff

import Data.Vect 

StringOrInt : Bool -> Type
StringOrInt False = String
StringOrInt True = Int


data Thing = T1 | T2 | T3

t2nott1 : T2 = T1 -> Void
t2nott1 Refl impossible

t3nott1 : T3 = T1 -> Void
t3nott1 Refl impossible

isThing1 : (t : Thing) -> Dec (t = T1)
isThing1 T1 = Yes Refl
isThing1 T2 = No t2nott1
isThing1 T3 = No t3nott1

is_not_thing1 : (t : Thing) -> Type
is_not_thing1 t with (isThing1 t)
  | Yes _ = Void
  | No  _ = Type
  
data Atest : (ts : Vect (S n) Thing) -> Type where
  Make : (is_not_thing1 (head ts)) -> (Atest (tail ts)) -> Atest ts

make_atest : (ts : Vect (S n) Thing) -> Atest ts
make_atest ts with (isThing1 (head ts))
  | (Yes prf) = absurd prf
  | (No cont) = Make x xs


print_things : (Atest vs) -> String
print_things (Make x xs) = "did it: "


 
