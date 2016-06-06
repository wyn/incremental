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


-- data EqSt : (s1 : CStream a) -> (s2 : CStream a) -> Type where
--   EqStream : (head_prf : hd s1 = hd s2) -> (tail_prf : (EqSt (tl s1) (tl s2))) -> EqSt s1 s2
head_bad : (cont : (x = y) -> Void) -> (Cons x xs = Cons y ys) -> Void
head_bad cont Refl = cont Refl

tail_bad : (cont : (xs = ys) -> Void) -> (Cons x xs = Cons x ys) -> Void
tail_bad cont Refl = cont Refl

(DecEq a) => DecEq (CStream a) where
    decEq (Cons x xs) (Cons y ys) with (decEq x y) 
      decEq (Cons x xs) (Cons x ys)   | Yes Refl with (decEq xs ys) 
        decEq (Cons x xs) (Cons x xs) | Yes Refl | Yes Refl = Yes Refl
        decEq (Cons x xs) (Cons x ys) | Yes Refl | No cont = No (tail_bad cont)

      decEq (Cons x xs) (Cons y ys)   | No cont = No (head_bad cont)



        
    
stream_unfold : (x : CStream a) -> (x = (Cons (hd x) (tl x)))
stream_unfold (Cons x y) = Refl


-- data SamplElt : (a : Type) -> Bool -> Type where
--   CNone : SamplElt a False
--   CAny  : a -> SamplElt a True
--   CFail : SamplElt a True
  
-- Clock : Type
-- Clock = CStream Bool

-- data SamplStr : (a : Type) -> (c : Clock) -> Type where
--   SPCons : (SamplElt a (hd c)) -> (SamplStr a (tl c)) -> SamplStr a c


-- sp_hd : SamplStr a c -> SamplElt a (hd c)
-- sp_hd (SPCons x _) = x

-- sp_tl : SamplStr a c -> SamplStr a (tl c)
-- sp_tl (SPCons _ y) = y


-- unfold_samplStr : (c : Clock) -> (s : SamplStr a c) -> (s = (SPCons (sp_hd s) (sp_tl s)))
-- unfold_samplStr c (SPCons x y) = Refl



-- data SpEq : (s1 : SamplStr a c1) -> (s2 : SamplStr a c2) -> Type where
--   SpEqProof : (sp_hd s1 = sp_hd s2) -> (SpEq (sp_tl s1) (sp_tl s2)) -> SpEq s1 s2

-- prf_samplElt : (a : Type ) -> (c1 : Clock) -> (c2 : Clock) -> (head_prf : hd c1 = hd c2) -> 
--                (SamplElt a (hd c1) = SamplElt a (hd c2))
-- prf_samplElt a c1 c2 head_prf = rewrite head_prf in Refl


-- head_coerce : (head_prf : hd c1 = hd c2) -> (x : SamplElt a (hd c1)) -> SamplElt a (hd c2)
-- head_coerce {a} {c1} {c2} head_prf x = let prf = prf_samplElt a c1 c2 head_prf in 
--                                        rewrite sym $ prf in x

-- clock_coerce : (EqSt c1 c2) -> SamplStr a c1 -> SamplStr a c2
-- clock_coerce (EqStream head_prf tail_prf) (SPCons x xs) = SPCons (head_coerce head_prf x) (clock_coerce tail_prf xs)

-- sp_eq_clock_coerce : (prf : (EqSt c1 c2)) -> (s : SamplStr a c1) -> (SpEq s (clock_coerce prf s))
-- sp_eq_clock_coerce {a} {c1} {c2} (EqStream head_prf tail_prf) (SPCons x xs) = believe_me (EqStream head_prf tail_prf) (SPCons x xs)
--   -- let prf_elt = prf_samplElt a c1 c2 head_prf in 
--   --   case (sp_eq_clock_coerce tail_prf xs) of
--   --     SpEqProof inner_head_prf inner_tail_prf => 
--   --       SpEqProof ?stuff_head ?
  

-- -- is_fail : (s : SamplElt a b) -> Dec (s = the (SamplElt a True) CFail)
-- -- is_fail CFail = Yes Refl
-- -- is_fail _ = No ?rest1

-- -- data SpWf : (SamplStr a c) -> Type where
-- --   SpWfProof : (s : SamplStr a c) -> 
-- --               (is_no_fail (sp_hd s)) ->
-- --               (sp_wf (sp_tl s)) -> sp_wf s
  
 
