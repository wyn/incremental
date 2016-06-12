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


codata CStream : Type -> Type where
  Cons : a -> CStream a -> CStream a

hd : CStream a -> a
hd (Cons x xs) = x

tl : CStream a -> CStream a
tl (Cons x xs) = xs

cconst : a -> CStream a 
cconst x = Cons x (Delay (cconst x))


head_bad : (cont : (x = y) -> Void) -> 
           (Cons x (Delay xs) = Cons y (Delay ys)) -> Void
head_bad cont Refl = cont Refl

tail_bad : (cont : ((Delay xs) = (Delay ys)) -> Void) -> 
           (Cons x (Delay xs) = Cons x (Delay ys)) -> Void
tail_bad cont Refl = cont Refl

(DecEq a, DecEq (Lazy (CStream a))) => DecEq (CStream a) where
    decEq (Cons x (Delay xs)) (Cons y (Delay ys)) with (decEq x y) 
      decEq (Cons x (Delay xs)) (Cons y (Delay ys))   | No cont             = No (head_bad cont)
      decEq (Cons x (Delay xs)) (Cons x (Delay ys))   | Yes Refl with (decEq (Delay xs) (Delay ys)) 
        decEq (Cons x (Delay xs)) (Cons x (Delay xs)) | Yes Refl | Yes Refl = Yes Refl
        decEq (Cons x (Delay xs)) (Cons x (Delay ys)) | Yes Refl | No cont  = No (tail_bad cont)

-- Cons x xs = Cons x (Delay xs)
-- Cons x xs = Cons x (Lazy' t a)
-- Delay : (val : a) -> Lazy' t a
--  Force : Lazy' t a -> a

force_delay_prf : (xs : CStream a) -> Force (Delay xs) = xs
force_delay_prf xs = Refl

-- force_delay_prf2 : Cons x (Delay xs) = Cons x (Delay (Force (Delay xs)))
-- force_delay_prf2 {x} {xs} = let prf = force_delay_prf xs in rewrite prf in ?stuff_prf

-- force_delay_prf2 : (x : a) -> (xs : CStream a) -> 
--                    Cons x (Delay (Force (the (Lazy' LazyCodata (CStream a)) (Delay xs)))) = Cons x (the (Lazy' LazyCodata (CStream a)) (Delay xs))
force_delay_prf2 : (x : a) -> (xs : CStream a) -> Cons x (Delay xs) = Cons x (Delay (Force (Delay xs)))
-- force_delay_prf2 x (Cons y ys) = let prf = force_delay_prf (Cons y ys) in 
--                                  let prf2 = force_delay_prf2 y ys in 
--                                  ?force_delay_prf2_rhs
-- force_delay_prf2 {x} {xs} = let prf = force_delay_prf xs in rewrite prf in ?stuff_prf


-- delay_force_prf : (Cons x xs) = Delay (Force (Cons x xs))
-- delay_force_prf = ?delay_force_prf_rhs1


-- stream_unfold_rhs_1 : (prf : Force xs = Cons (hd (Force xs)) (Delay (tl (Force xs)))) -> 
--                       Cons x xs = Cons x (Delay (tl (Cons x xs)))

stream_unfold : (s : CStream a) -> (s = (Cons (hd s) (tl s)))
stream_unfold (Cons x xs) = let prf = stream_unfold xs in 
                            ?stream_unfold_rhs_1 prf


data SamplElt : (a : Type) -> Bool -> Type where
  CNone : SamplElt a False
  CAny  : a -> SamplElt a True
  CFail : SamplElt a True


bad_any_fail_prf : (clk : Bool) -> (CAny x = CFail) -> Void
bad_any_fail_prf _ Refl impossible

bad_fail_any_prf : (clk : Bool) -> (CFail = CAny x) -> Void
bad_fail_any_prf _ Refl impossible

bad_any_prf : (cont : (x = y) -> Void) -> (CAny x = CAny y) -> Void
bad_any_prf cont Refl = cont Refl

(DecEq a) => DecEq (SamplElt a clk) where
    decEq CNone CNone = Yes Refl
    decEq CFail CFail = Yes Refl
    decEq (CAny x) (CAny y) = case (decEq x y) of
                Yes prf => Yes (cong prf)
                No cont => No (bad_any_prf cont)
    decEq {clk=True} (CAny x) CFail = No (bad_any_fail_prf True)
    decEq {clk=True} CFail (CAny y) = No (bad_fail_any_prf True)
    
    decEq CNone CFail    impossible
    decEq CFail CNone    impossible
    decEq CNone (CAny y) impossible
    decEq (CAny x) CNone impossible
    
    
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


prf_samplElt : (a : Type ) -> (c1 : Clock) -> (c2 : Clock) -> 
               (head_prf : hd c1 = hd c2) -> 
               (SamplElt a (hd c1) = SamplElt a (hd c2))
prf_samplElt a c1 c2 head_prf = rewrite head_prf in Refl


head_coerce : (head_prf : hd c1 = hd c2) -> (x : SamplElt a (hd c1)) -> SamplElt a (hd c2)
head_coerce {a} {c1} {c2} head_prf x = let prf = prf_samplElt a c1 c2 head_prf in 
                                       rewrite sym $ prf in x

clock_coerce : (prf : c1 = c2) -> SamplStr a c1 -> SamplStr a c2
clock_coerce Refl x = x

sp_eq_clock_coerce : (prf : (c1 = c2)) -> (s : SamplStr a c1) -> (s = (clock_coerce prf s))
sp_eq_clock_coerce Refl s = Refl

-- doesnt work becasue Bool is different but only one clk
-- notFails : a -> Vect 2 (SamplElt a clk)
-- notFails x = [CNone, CAny x]

  
is_not_fail : (e : SamplElt a clk) -> Bool
is_not_fail CNone = True
is_not_fail (CAny x) = True
is_not_fail CFail = False


data WellFormed : (s : SamplStr a c) -> Type where
  IsNotFail : (prf : True = is_not_fail (sp_hd s)) -> WellFormed (sp_tl s) -> WellFormed s


-- data WellFormed : (s : SamplStr a c) -> Type where
--   HeadIsAny : ((sp_hd s) = (CAny a)) -> WellFormed (sp_tl s) -> WellFormed s
--   HeadIsNone : ((sp_hd s) = CNone) -> WellFormed (sp_tl s) -> WellFormed s
  

elt_const : a -> (b : Bool) -> SamplElt a b
elt_const x clk_val = case clk_val of 
  True  => CAny x
  False => CNone


sp_const : a -> (clk : Clock) -> SamplStr a clk
sp_const x (Cons c cs) = SPCons (elt_const x c) (sp_const x cs)


sp_const_wellformed : (x : a) -> (clk : Clock) -> WellFormed (sp_const a clk)
sp_const_wellformed x (Cons c cs) = let rest = (sp_const_wellformed x cs) in 
                                    case elt_const x c of
                                    CAny x' => ?head_any_prf rest
                                    CNone  =>  ?head_non_prf
                                    CFail => ?head_fail_prf

elt_extend : (SamplElt (a -> b) clk_value) -> (SamplElt a clk_value) -> (SamplElt b clk_value)
elt_extend CNone    _        = CNone
elt_extend (CAny f) (CAny x) = CAny (f x)
elt_extend _        CFail    = CFail 
elt_extend CFail    _        = CFail

sp_extend : (SamplStr (a -> b) clk) -> (SamplStr a clk) -> (SamplStr b clk)
sp_extend (SPCons f fs) (SPCons x xs) = SPCons (elt_extend f x) (sp_extend fs xs)


sp_extend_wellformed : (fs : SamplStr (a->b) clk) -> 
                       (s : SamplStr a clk) -> 
                       (WellFormed fs) -> 
                       (WellFormed s) -> 
                       (WellFormed (sp_extend fs s)) 
sp_extend_wellformed fs s wf_fs wf_xs = ?sp_extend_wellformed_rhs


sp_extend_const_prf : (f : a -> b) -> (x : a) -> (sp_extend (sp_const f clk) (sp_const x clk)) = sp_const (f x) clk 
sp_extend_id_prf : (x : SamplStr a clk) -> (sp_extend (sp_const id clk) x) = x
sp_extend_comp_prf : (f : a -> b) -> (g : b -> c) -> (x : SamplStr a clk) ->
                     (sp_extend (sp_const g clk) (sp_extend (sp_const f clk) x)) = (sp_extend (sp_const (g . f) clk) x)


flip_bool : Bool -> Bool
flip_bool False = True
flip_bool True = False

sp_not :(SamplStr Bool clk) -> (SamplStr Bool clk)
sp_not {clk} = sp_extend (sp_const flip_bool clk)

sp_not2_id_prf : (lc : SamplStr Bool clk) -> (sp_not (sp_not lc)) = lc

if_then_else : Bool -> a -> a -> a
if_then_else cond x y = if cond then x else y

sp_if : SamplStr Bool clk -> SamplStr a clk -> SamplStr a clk -> SamplStr a clk
sp_if {clk} lc x y = sp_extend (sp_extend (sp_extend (sp_const if_then_else clk) lc) x) y

elt_on : SamplElt Bool b -> Bool
elt_on CNone = False
elt_on (CAny x) = x
elt_on CFail = True

sp_on : SamplStr Bool clk -> Clock
sp_on (SPCons x xs) = Cons (elt_on x) (sp_on xs)

elt_when : (o : SamplElt Bool clk_value) -> SamplElt a clk_value -> SamplElt a (elt_on o)                               
elt_when CNone        e = CNone
elt_when (CAny False) e = CNone
elt_when (CAny True)  e = e
elt_when CFail        e = CFail

sp_when : (lc : SamplStr Bool clk) -> SamplStr a clk -> SamplStr a (sp_on lc)
sp_when (SPCons c cs) (SPCons x xs) = SPCons (elt_when c x) (sp_when cs xs) 


elt_merge : (o : SamplElt Bool clk_value) -> 
            (SamplElt a (elt_on o)) -> 
            (SamplElt a (elt_on (elt_extend (elt_const flip_bool clk_value) o))) ->
            SamplElt a clk_value            
elt_merge CNone        x y = CNone
elt_merge (CAny False) x y = ?elt_merge_rhs_1
elt_merge (CAny True)  x y = x
elt_merge CFail        x y = CFail

sp_merge : (lc : SamplStr Bool clk) -> 
           SamplStr a (sp_on lc) -> 
           SamplStr a (sp_on (sp_not lc)) -> 
           SamplStr a clk
sp_merge (SPCons c cs) (SPCons x xs) (SPCons y ys) = ?sp_merge_rhs  --SPCons (elt_merge c x y) (sp_merge cs xs ys) 


sp_if_equiv_prf : (lc : SamplStr Bool clk) -> (x : SamplStr a clk) -> (y : SamplStr a clk) ->
                  (WellFormed x) ->
                  (WellFormed y) ->
                  (sp_if lc x y) = (sp_merge lc (sp_when lc x) (sp_when (sp_not lc) y)) 
