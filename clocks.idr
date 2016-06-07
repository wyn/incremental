module Clocks

-- An Idris implementation of 'A Clocked Denotational Semantics for
-- LUCID-SYNCHRONE in COQ' by S. Boulme & G. Hamon 2001
  
funPower : (f : (a -> a)) -> (repeats : Nat) -> (start : a) -> a
funPower f Z x = x
funPower f (S k) x = funPower f k (f x)

funPower_commutes : (f : (a -> a)) -> (n : Nat) -> (x : a) -> (f (funPower f n x)) = (funPower f (S n) x)
funPower_commutes f Z x = Refl
funPower_commutes f (S k) x = let ff = funPower_commutes f k (f x) in
                                  rewrite ff in Refl


data CStream : Type -> Type where
  Cons : a -> CStream a -> CStream a


hd : CStream a -> a
hd (Cons x xs) = x

tl : CStream a -> CStream a
tl (Cons x xs) = xs

cconst : a -> CStream a 
cconst x = Cons x (cconst x)


head_bad : (cont : (x = y) -> Void) -> (Cons x xs = Cons y ys) -> Void
head_bad cont Refl = cont Refl

tail_bad : (cont : (xs = ys) -> Void) -> (Cons x xs = Cons x ys) -> Void
tail_bad cont Refl = cont Refl

(DecEq a) => DecEq (CStream a) where
    decEq (Cons x xs) (Cons y ys) with (decEq x y) 
      decEq (Cons x xs) (Cons y ys)   | No cont             = No (head_bad cont)
      decEq (Cons x xs) (Cons x ys)   | Yes Refl with (decEq xs ys) 
        decEq (Cons x xs) (Cons x xs) | Yes Refl | Yes Refl = Yes Refl
        decEq (Cons x xs) (Cons x ys) | Yes Refl | No cont  = No (tail_bad cont)


stream_unfold : (x : CStream a) -> (x = (Cons (hd x) (tl x)))
stream_unfold (Cons x xs) = Refl


data SamplElt : (a : Type) -> Bool -> Type where
  CNone : SamplElt a False
  CAny  : a -> SamplElt a True
  CFail : SamplElt a True


bad_any_prf : (cont : (x = y) -> Void) -> (CAny x = CAny y) -> Void
bad_any_prf cont Refl = cont Refl

(DecEq a) => DecEq (SamplElt a bl) where
    decEq CNone CNone = Yes Refl
    decEq CFail CFail = Yes Refl
    decEq (CAny x) (CAny y) = case (decEq x y) of
                Yes prf => Yes (cong prf)
                No cont => No (bad_any_prf cont)
    decEq x y = No (believe_me x y)
    
Clock : Type
Clock = CStream Bool

data SamplStr : (a : Type) -> (c : Clock) -> Type where
  SPCons : (SamplElt a (hd c)) -> (SamplStr a (tl c)) -> SamplStr a c


sp_hd : SamplStr a c -> SamplElt a (hd c)
sp_hd (SPCons x _) = x

sp_tl : SamplStr a c -> SamplStr a (tl c)
sp_tl (SPCons _ xs) = xs


unfold_samplStr : (c : Clock) -> (s : SamplStr a c) -> (s = (SPCons (sp_hd s) (sp_tl s)))
unfold_samplStr c (SPCons x xs) = Refl

bad_head_stream : (cont : (x = y) -> Void) -> 
                  (SPCons x xs = SPCons y ys) -> Void
bad_head_stream cont Refl = cont Refl

bad_tail_stream : (cont : (xs = ys) -> Void) -> 
                  (SPCons x xs = SPCons x ys) -> Void
bad_tail_stream cont Refl = cont Refl


(DecEq a) => DecEq (SamplStr a c) where
     decEq (SPCons x xs) (SPCons y ys) with (decEq x y) 
      decEq (SPCons x xs) (SPCons y ys) | No cont = No (bad_head_stream cont)
      decEq (SPCons x xs) (SPCons x ys) | Yes Refl with (decEq xs ys) 
        decEq (SPCons x xs) (SPCons x xs) | Yes Refl | Yes Refl = Yes Refl
        decEq (SPCons x xs) (SPCons x ys) | Yes Refl | No cont  = No (bad_tail_stream cont)


prf_samplElt : (a : Type ) -> (c1 : Clock) -> (c2 : Clock) -> (head_prf : hd c1 = hd c2) -> 
               (SamplElt a (hd c1) = SamplElt a (hd c2))
prf_samplElt a c1 c2 head_prf = rewrite head_prf in Refl


head_coerce : (head_prf : hd c1 = hd c2) -> (x : SamplElt a (hd c1)) -> SamplElt a (hd c2)
head_coerce {a} {c1} {c2} head_prf x = let prf = prf_samplElt a c1 c2 head_prf in 
                                       rewrite sym $ prf in x

clock_coerce : (prf : c1 = c2) -> SamplStr a c1 -> SamplStr a c2
clock_coerce Refl x = x

sp_eq_clock_coerce : (prf : (c1 = c2)) -> (s : SamplStr a c1) -> (s = (clock_coerce prf s))
sp_eq_clock_coerce Refl s = Refl

data WellFormed : (s : SamplStr a c) -> Type where
  HeadIsAny : ((sp_hd s) = (CAny a)) -> WellFormed (sp_tl s) -> WellFormed s
  HeadIsNone : ((sp_hd s) = CNone) -> WellFormed (sp_tl s) -> WellFormed s
  
 
