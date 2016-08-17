module Clocks

%default total

-- An Idris implementation of 'A Clocked Denotational Semantics for
-- LUCID-SYNCHRONE in COQ' by S. Boulme & G. Hamon 2001
  
funPower : (f : (a -> a)) -> (repeats : Nat) -> (start : a) -> a
funPower f Z x = x
funPower f (S k) x = funPower f k (f x)

funPower_commutes : (f : (a -> a)) -> (n : Nat) -> (x : a) -> (f (funPower f n x)) = (funPower f (S n) x)
funPower_commutes f Z x = Refl
funPower_commutes f (S k) x = let ff = funPower_commutes f k (f x) in
                                  rewrite ff in Refl


-- nicked from bmckenna
-- dont think we can have DecEq for streams??
-- use equivalence instead
-- infixl 9 =~=
-- data Equiv : Stream a -> Stream a -> Type where
--   Cons :  (head_prf : a = b) -> Inf (Equiv as bs) -> Equiv (a :: as) (b :: bs)  
  

-- stream_unfold : (DecEq a) => (s : Stream a) -> Equiv s (( head s ) :: ( tail s ))
-- stream_unfold (x :: xs) with (decEq x (head (x :: xs)))
--   stream_unfold (x :: xs) | (Yes prf) = ?stream_unfold_rhs_1_rhs_3
--   stream_unfold (x :: xs) | (No contra) = ?stream_unfold_rhs_1_rhs_4

data Clk = Tick | Tock
    
data SamplElt : (a : Type) -> Clk -> Type where
  CNone : SamplElt a Tock
  CAny  : a -> SamplElt a Tick
  CFail : SamplElt a Tick


bad_any_fail_prf : (clk : Clk) -> (CAny x = CFail) -> Void
bad_any_fail_prf _ Refl impossible

bad_fail_any_prf : (clk : Clk) -> (CFail = CAny x) -> Void
bad_fail_any_prf _ Refl impossible

bad_any_prf : (cont : (x = y) -> Void) -> (CAny x = CAny y) -> Void
bad_any_prf cont Refl = cont Refl

(DecEq a) => DecEq (SamplElt a clk) where
    decEq CNone CNone = Yes Refl
    decEq CFail CFail = Yes Refl
    decEq (CAny x) (CAny y) = case (decEq x y) of
                Yes prf => Yes (cong prf)
                No cont => No (bad_any_prf cont)
    decEq {clk=Tick} (CAny x) CFail = No (bad_any_fail_prf Tick)
    decEq {clk=Tick} CFail (CAny y) = No (bad_fail_any_prf Tick)
    
    decEq CNone CFail    impossible
    decEq CFail CNone    impossible
    decEq CNone (CAny y) impossible
    decEq (CAny x) CNone impossible
    
    
Clock : Type
Clock = Stream Clk

data SamplStr : (a : Type) -> (c : Clock) -> Type where
  (::) : (SamplElt a (head c)) -> Inf (SamplStr a (tail c)) -> SamplStr a c

-- infixl 9 =~~=
-- data (=~~=) : SamplStr a c -> SamplStr a c -> Type where
--   (:::) : a = b -> Inf (as =~~= bs) -> (SPCons a as =~~= SPCons b bs)

sp_hd : SamplStr a c -> SamplElt a (head c)
sp_hd (x :: _) = x

sp_tl : SamplStr a c -> SamplStr a (tail c)
sp_tl (_ :: xs) = xs


using (c1 : Clock, c2 : Clock)
  prf_samplElt : (a : Type ) -> (c1 : Clock) -> (c2 : Clock) -> 
                 (head_prf : head c1 = head c2) -> 
                 (SamplElt a (head c1) = SamplElt a (head c2))
  prf_samplElt a c1 c2 head_prf = rewrite head_prf in Refl

  head_coerce : (head_prf : head c1 = head c2) -> 
                (x : SamplElt a (head c1)) -> SamplElt a (head c2)
  head_coerce {a} {c1} {c2} head_prf x = let prf = prf_samplElt a c1 c2 head_prf in 
                                         rewrite sym $ prf in x

  clock_coerce : (prf : c1 = c2) -> SamplStr a c1 -> SamplStr a c2
  clock_coerce Refl x = x

  sp_eq_clock_coerce : (prf : (c1 = c2)) -> (s : SamplStr a c1) -> (s = (clock_coerce prf s))
  sp_eq_clock_coerce Refl s = Refl

-- -- doesnt work becasue Bool is different but only one clk
-- -- notFails : a -> Vect 2 (SamplElt a clk)
-- -- notFails x = [CNone, CAny x]

  
-- -- is_not_fail : (e : SamplElt a clk) -> Bool
-- -- is_not_fail CNone = True
-- -- is_not_fail (CAny x) = True
-- -- is_not_fail CFail = False


-- -- data WellFormed : (s : SamplStr a c) -> Type where
-- --   IsNotFail : (prf : True = is_not_fail (sp_hd s)) -> WellFormed (sp_tl s) -> WellFormed s


data WellFormed : (s : SamplStr a c) -> Type where
  HeadIsAny : ((sp_hd s) = (CAny a)) -> WellFormed (sp_tl s) -> WellFormed s
  HeadIsNone : ((sp_hd s) = CNone) -> WellFormed (sp_tl s) -> WellFormed s
  

elt_const : a -> (clk_value : Clk) -> SamplElt a clk_value
elt_const x clk_value = case clk_value of 
  Tick   => CAny x
  Tock => CNone


sp_const : a -> (clk : Clock) -> SamplStr a clk
sp_const x (c :: cs) = (elt_const x c) :: (sp_const x cs)


-- sp_const_wellformed : (x : a) -> (clk : Clock) -> WellFormed (sp_const a clk)
-- sp_const_wellformed x (Cons c cs) = let rest = (sp_const_wellformed x cs) in 
--                                     case elt_const x c of
--                                     CAny x' => ?head_any_prf rest
--                                     CNone  =>  ?head_non_prf
--                                     CFail => ?head_fail_prf

elt_extend : (SamplElt (a -> b) clk_value) -> (SamplElt a clk_value) -> (SamplElt b clk_value)
elt_extend CNone    _        = CNone
elt_extend (CAny f) (CAny x) = CAny (f x)
elt_extend _        CFail    = CFail 
elt_extend CFail    _        = CFail

sp_extend : (SamplStr (a -> b) clk) -> (SamplStr a clk) -> (SamplStr b clk)
sp_extend (f :: fs) (x :: xs) = (elt_extend f x) :: (sp_extend fs xs)


-- sp_extend_wellformed : (fs : SamplStr (a->b) clk) -> 
--                        (s : SamplStr a clk) -> 
--                        (WellFormed fs) -> 
--                        (WellFormed s) -> 
--                        (WellFormed (sp_extend fs s)) 
-- sp_extend_wellformed fs s wf_fs wf_xs = ?sp_extend_wellformed_rhs


-- sp_extend_const_prf : (f : a -> b) -> (x : a) -> (sp_extend (sp_const f clk) (sp_const x clk)) = sp_const (f x) clk 
-- sp_extend_const_prf f x = ?sp_extend_const_prf_rhs

-- sp_extend_id_prf : (x : SamplStr a clk) -> (sp_extend (sp_const id clk) x) = x
-- sp_extend_id_prf x = ?sp_extend_id_prf_rhs

-- sp_extend_comp_prf : (f : a -> b) -> (g : b -> c) -> (x : SamplStr a clk) ->
--                      (sp_extend (sp_const g clk) (sp_extend (sp_const f clk) x)) = (sp_extend (sp_const (g . f) clk) x)
-- sp_extend_comp_prf f g (SPCons x xs) = ?sp_extend_comp_prf_rhs_1


flip_bool : Bool -> Bool
flip_bool False = True
flip_bool True = False

bool_to_clk : Bool -> Clk
bool_to_clk True = Tick
bool_to_clk False = Tock

clk_to_bool : Clk -> Bool
clk_to_bool Tick = True
clk_to_bool Tock = False

sp_not :(SamplStr Bool clk) -> (SamplStr Bool clk)
sp_not {clk} = sp_extend (sp_const flip_bool clk)

if_then_else : Bool -> a -> a -> a
if_then_else cond x y = if cond then x else y

sp_if : SamplStr Bool clk -> SamplStr a clk -> SamplStr a clk -> SamplStr a clk
sp_if {clk} lc x y = sp_extend (sp_extend (sp_extend (sp_const if_then_else clk) lc) x) y

elt_on : SamplElt Bool clk_value -> Clk
elt_on CNone = Tock
elt_on (CAny x) = bool_to_clk x
elt_on CFail = Tick

sp_on : SamplStr Bool clk -> Clock
sp_on (x :: xs) = (elt_on x) :: (sp_on xs)

elt_when : (o : SamplElt Bool clk_value) -> 
           SamplElt a clk_value -> 
           SamplElt a (elt_on o)                               
elt_when CNone        e = CNone
elt_when (CAny False) e = CNone
elt_when (CAny True)  e = e
elt_when CFail        e = CFail

sp_when : (lc : SamplStr Bool clk) -> SamplStr a clk -> SamplStr a (sp_on lc)
sp_when (c :: cs) (x :: xs) = (elt_when c x) :: (sp_when cs xs) 

-- flip_bool_prf : (elt_on (elt_extend (elt_const flip_bool Tick) (CAny False))) = Tick


elt_merge : (o : SamplElt Bool clk_value) -> 
            (SamplElt a (elt_on o)) -> 
            (SamplElt a (elt_on (elt_extend (elt_const Clocks.flip_bool clk_value) o))) ->
            SamplElt a clk_value            
elt_merge CNone        x y = CNone
elt_merge (CAny False) x y = y
elt_merge (CAny True)  x y = x -- elt_on (CAny True)
elt_merge CFail        x y = CFail

sp_merge : (lc : SamplStr Bool clk) -> 
           SamplStr a (sp_on lc) -> 
           SamplStr a (sp_on (sp_not lc)) -> 
           SamplStr a clk
sp_merge (c :: cs) (x :: xs) (y :: ys) = (elt_merge c x ?ything) :: (sp_merge cs xs ?ysthings)

 
--   (c :: cs) (x :: xs) (y :: ys) = (elt_merge c x y) :: (sp_merge cs xs ys) 


-- sp_if_equiv_prf : (lc : SamplStr Bool clk) -> (x : SamplStr a clk) -> (y : SamplStr a clk) ->
--                   (WellFormed x) ->
--                   (WellFormed y) ->
--                   (sp_if lc x y) = (sp_merge lc (sp_when lc x) (sp_when (sp_not lc) y)) 

-- chooses xs until clock ticks, then chooses ys
sp_arrow : SamplStr a clk -> SamplStr a clk -> SamplStr a clk
sp_arrow {clk = (c :: cs)} (x :: xs) (y :: ys) 
  = x :: (if (clk_to_bool c) then ys else (sp_arrow xs ys))

-- delay by one Clk element - if the clock ticks then initialised with init
-- else initialise with none and recurse with rest of x :: xs
sp_delay : (SamplStr a clk) -> (SamplElt a Tick) -> SamplStr a clk
sp_delay {clk = (Tick :: cs)} (x :: xs) init = init  :: (sp_delay xs x)
sp_delay {clk = (Tock :: cs)} (x :: xs) init = CNone :: (sp_delay xs init)

sp_pre : SamplStr a clk -> SamplStr a clk
sp_pre s = sp_delay s CFail 

sp_fby : SamplStr a clk -> SamplStr a clk -> SamplStr a clk
sp_fby x y = sp_arrow x (sp_pre y)

-- arrow_equiv_prf : (x : SamplStr a clk) -> (y : SamplStr a clk) -> 
--                   WellFormed x -> WellFormed y ->
--                   (sp_arrow x y) = (sp_if (sp_fby (sp_const True clk) (sp_const False clk)) x y)
