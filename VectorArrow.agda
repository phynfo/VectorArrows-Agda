module MyVec where

data Bool : Set where
  true : Bool
  false : Bool

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

{-# BUILTIN NATURAL Nat    #-}
{-# BUILTIN ZERO    zero #-}
{-# BUILTIN SUC     suc  #-}

_+_ : Nat -> Nat -> Nat
zero + j  = j
suc i + j = suc (i + j)

infixl 6 _+_

{-# BUILTIN NATPLUS _+_ #-}

data _*_ (A B : Set) : Set where 
  _,_  : A -> B -> A * B

data Vec (A : Set) : Nat -> Set where 
  []   : Vec A zero
  _::_ : {n : Nat} -> A -> (Vec A n) -> (Vec A (suc n))

infixr 5 _::_

_++_ : {A : Set}{n m : Nat} -> Vec A n -> Vec A m -> Vec A (n + m)
[] ++ ys        = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

split : {A : Set}{m n : Nat} -> Vec A (n + m) -> (Vec A n) * (Vec A m) 
split {_} {_} {zero}  xs        = ( [] , xs )
split {_} {_} {suc _} (x :: xs) with split xs 
... | ( ys , zs ) = ( (x :: ys) , zs )

-- All Elements but the last
heads : {A : Set}{n : Nat} -> Vec A (1 + n) -> Vec  A n
heads (x :: []) = []
heads (x :: y :: xs) = x :: (heads (y :: xs))

last : {A : Set}{n : Nat} -> Vec A (1 + n) -> A
last (x :: []) = x
last (x :: y :: xs) = last (y :: xs)

take : {A : Set} {m : Nat} -> (n : Nat) -> Vec A (n + m) -> Vec A n
take zero    xs        = []
take (suc i) (x :: xs) = x :: (take i xs)

drop : {A : Set} {m : Nat} -> (n : Nat) -> Vec A (n + m) -> Vec A m
drop zero    xs        = xs
drop (suc i) (x :: xs) = drop i xs

swap : {A : Set} {m n : Nat} -> Vec A (n + m) -> Vec A (m + n)
swap {_} {_} {n} xs = drop n xs ++ take n xs

-- yields same result as split BUT calculates it from the back
-- splitM : {A : Set}{m n : Nat} -> Vec A (n + m) -> (Vec A m) * (Vec A n) 
-- splitM {_} {zero} {_}  xs       = ( [] , xs )
-- splitM {_} {suc _} {_} xs with splitM (heads xs) 
-- ... | ( ys , zs ) = ( last xs :: ys , zs )

_o_ : {A C : Set}{B : A -> Set}{C : (x : A) -> (B x) -> Set} -> (f : {x : A}(y : B x) -> C x y) -> (g : (x : A) -> B x) -> (x : A) -> C x (g x) 
_o_ f g x = f (g x)

_o1_ : {A C : Set}{B : A -> Set} -> ({x : A} -> B x -> C) -> ( (x : A) -> B x) -> (A -> C)
_o1_ f g x = f (g x)

seconds : {A : Set}{n m : Nat} -> (k : Nat) -> (Vec A n -> Vec A m) -> Vec A (k + n) -> Vec A (k + m)
seconds {_} {_} {_} k f xs with split {_} {_} {k} xs
... | ( ys , zs ) = ys ++ (f zs)

firsts : {A : Set}{n m k : Nat} -> (Vec A n -> Vec A m) -> Vec A (n + k) -> Vec A (m + k)
firsts f xs with split xs
... | ( ys , zs ) = f ys ++ zs


change2 : {A : Set} -> Vec A 2 -> Vec A 2
change2 ( x :: y :: [] ) = (y :: x :: [] )

change3 : {A : Set} -> Vec A 3 -> Vec A 3
change3 ( x :: y :: z :: [] ) = (y :: x :: z :: [] )

changeN : {A : Set}{n : Nat} -> Vec A (2 + n) -> Vec A (2 + n)
changeN = firsts change2

change3' : {A : Set} -> Vec A 3 -> Vec A 3
change3' = changeN {_} {1}

-- shifts value at pos i exactly j positions to the right
shift : {A : Set}{n : Nat} -> (i : Nat) -> (j : Nat) -> Vec A (1 + i + j + n) -> Vec A (1 + i + j + n)
shift zero zero xs = xs
shift zero (suc j) (x :: y :: xs) =  y :: shift zero j (x :: xs)
shift (suc i) j (x :: y :: xs) = x :: shift i j (y :: xs)



_***_ : {A : Set}{n m k j : Nat} -> (Vec A n -> Vec A m) -> (Vec A k -> Vec A j) -> Vec A (n + k) -> Vec A (m + j)
_***_ f g xs with split xs
...            | ( ys , zs) = f ys ++ g zs

_&&&_ : {A : Set}{n m k : Nat} -> (Vec A n -> Vec A m) -> (Vec A n -> Vec A k) -> Vec A n -> Vec A (m + k)
_&&&_ f g xs = f xs ++ g xs

--_>>>_ : {A C : Set}{B : A -> Set}{C : (x : A) -> (B x) -> Set} -> (g : (x : A) -> B x) -> (f : {x : A}(y : B x) -> C x y) -> (x : A) -> C x (g x) 
--_>>>_ g f x = f ( g x )

_>>>_ : {A B C : Set} -> (A -> B) -> (B -> C) -> (A -> C)
_>>>_ g f x = f (g x)


infixr 6 _>>>_ 

_xor_ : Bool -> Bool -> Bool
_xor_ true false = true
_xor_ false true = true
_xor_ _     _    = false

xorV : Vec Bool 2 -> Vec Bool 1
xorV (x :: y :: []) = (x xor y) :: []

-- Duplicate wire number i
dup : {A : Set}{n : Nat} -> (i : Nat) -> Vec A (1 + i + n) -> Vec A (2 + i + n)
dup zero (x :: xs) = x :: x :: xs
dup (suc i) (x :: xs) = x :: (dup i xs)

test : Vec Bool 5 -> Vec Bool 4
test = firsts xorV >>> swap {_} {_} {2}


crc_poly_ccit : Vec Bool 5 -> Vec Bool 4
crc_poly_ccit = shift 0 2 >>> 
                dup 2     >>> 
                shift 3 1 >>> 
                seconds 2 (xorV *** 
                           xorV
                          )

crc_poly_ccit1 : Vec Bool 5 -> Vec Bool 4
crc_poly_ccit1 = shift 0 2 >>> 
                dup 2     >>> 
                shift 3 1 >>> 
                firsts (xorV *** 
                        xorV
                       )


--crc_polynom_ccit : Vec Bool 5 -> Vec Bool 4 
--crc_polynom_ccit 
--    =   mvRight >:> mvRight >:>
--        (   aAssoc 
--        >>> (aXor *** aXor)
--        )
-- crc_polynom_ccit 
--  = proc (x4, (x3, (x2, (x1, x0)))) -> do
--      o1 <- aXor -< (x4, x0)
--      o2 <- aXor -< (x4, x1)
--      o3 <- aId  -< (x2)
--      o4 <- aId  -< (x3)
--      returnA    -< (o4, (o3, (o2, o1)))


