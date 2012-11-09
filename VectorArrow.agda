module VectorArrow where

open import Data.List using (List; _∷_; map; zipWith)
open import Data.Nat using (ℕ; zero; suc;  _+_; _*_)

data Bool : Set where
  true : Bool
  false : Bool

--_+_ : ℕ → ℕ → ℕ
--zero + j  = j
--suc i + j = suc (i + j)

--_*_ : ℕ → ℕ → ℕ
--zero * j = zero
--suc i * j = j + (i * j)

data _×_ (A B : Set) : Set where 
  _,_  : A → B → A × B

fst : ∀ {A B} → A × B → A
fst (x , y) = x

snd : ∀ {A B} → A × B → B
snd (x , y) = y

data Vec (A : Set) : ℕ → Set where 
  []   : Vec A zero
  _∷_ : {n : ℕ} → A → (Vec A n) → (Vec A (suc n))
 
infixr 5 _∷_

_++_ : {A : Set}{n m : ℕ} → Vec A n → Vec A m → Vec A (n + m)
[] ++ ys        = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

split : ∀ {A m n} → Vec A (n + m) → (Vec A n) × (Vec A m) 
split {_} {_} {zero}  xs        = ( [] , xs )
split {_} {_} {suc _} (x ∷ xs) with split xs 
... | ( ys , zs ) = ( (x ∷ ys) , zs )

-- All Elements but the last
heads : ∀ {A n} → Vec A (1 + n) → Vec  A n
heads (x ∷ []) = []
heads (x ∷ y ∷ xs) = x ∷ (heads (y ∷ xs))

last : ∀ {A n} → Vec A (1 + n) → A
last (x ∷ []) = x
last (x ∷ y ∷ xs) = last (y ∷ xs)

take : ∀ {A m} (n : ℕ) → Vec A (n + m) → Vec A n
take zero    xs        = []
take (suc i) (x ∷ xs) = x ∷ (take i xs)

drop : ∀ {A m} (n : ℕ) → Vec A (n + m) → Vec A m
drop zero    xs        = xs
drop (suc i) (x ∷ xs) = drop i xs

concat : ∀ {A n m} → Vec (Vec A n) m → Vec A (m * n)
concat [] = []
concat (xs ∷ xss) = xs ++ (concat xss)

swap : ∀ {A m n} → Vec A (n + m) → Vec A (m + n)
swap {_} {_} {n} xs = drop n xs ++ take n xs

-- yields same result as split BUT calculates it from the back
-- splitM : {A : Set}{m n : ℕ} → Vec A (n + m) → (Vec A m) x (Vec A n) 
-- splitM {_} {zero} {_}  xs       = ( [] , xs )
-- splitM {_} {suc _} {_} xs with splitM (heads xs) 
-- ... | ( ys , zs ) = ( last xs ∷ ys , zs )

--_o_ : {A C : Set}{B : A → Set}{C : (x : A) → (B x) → Set} → (f : {x : A}(y : B x) → C x y) → (g : (x : A) → B x) → (x : A) → C x (g x) 
--_o_ f g x = f (g x)

_◦_ : {A C : Set}{B : A → Set} → ({x : A} → B x → C) → ( (x : A) → B x) → (A → C)
_◦_ f g x = f (g x)

_=>_ : Set → Set → Set
A => B = A → B

_⇒S⇒_ : Set → Set → Set
A ⇒S⇒ B = List A → List B

seconds : ∀ {A n m} (k : ℕ) → (Vec A n => Vec A m) → Vec A (k + n) => Vec A (k + m)
seconds k f xs with split {_} {_} {k} xs
... | ( ys , zs ) = ys ++ (f zs)

firsts : ∀ {A n m k} → (Vec A n => Vec A m) → Vec A (n + k) => Vec A (m + k)
firsts f xs with split xs
... | ( ys , zs ) = f ys ++ zs

change2 : {A : Set} → Vec A 2 → Vec A 2
change2 ( x ∷ y ∷ [] ) = (y ∷ x ∷ [] )

change3 : {A : Set} → Vec A 3 → Vec A 3
change3 ( x ∷ y ∷ z ∷ [] ) = (y ∷ x ∷ z ∷ [] )

changeN : {A : Set}{n : ℕ} → Vec A (2 + n) → Vec A (2 + n)
changeN = firsts change2

change3' : {A : Set} → Vec A 3 → Vec A 3
change3' = changeN {_} {1}

-- shifts value at pos i exactly j positions to the right
shift : ∀ {A n}(i : ℕ) → (j : ℕ) → Vec A (1 + i + j + n) → Vec A (1 + i + j + n)
shift zero zero xs = xs
shift zero (suc j) (x ∷ y ∷ xs) = y ∷ shift zero j (x ∷ xs)
shift (suc i) j (x ∷ y ∷ xs)    = x ∷ shift i    j (y ∷ xs)

_***_ : ∀ {A n m k j} → (Vec A n → Vec A m) → (Vec A k → Vec A j) → Vec A (n + k) → Vec A (m + j)
_***_ f g xs with split xs
...            | ( ys , zs) = f ys ++ g zs

_&&&_ : {A : Set}{n m k : ℕ} → (Vec A n → Vec A m) → (Vec A n → Vec A k) → Vec A n → Vec A (m + k)
_&&&_ f g xs = f xs ++ g xs

_>>>_ : {A B C : Set} → (A → B) → (B → C) → (A → C)
_>>>_ g f x = f (g x)

infixr 6 _>>>_ 

_xor_ : Bool → Bool → Bool
_xor_ true false = true
_xor_ false true = true
_xor_ _     _    = false

xorV : Vec Bool 2 → Vec Bool 1
xorV (x ∷ y ∷ []) = (x xor y) ∷ []

-- Duplicate wire number i
dup : ∀ {A n} (i : ℕ) → Vec A (1 + i + n) → Vec A (2 + i + n)
dup zero (x ∷ xs) = x ∷ x ∷ xs
dup (suc i) (x ∷ xs) = x ∷ (dup i xs)

crc_poly_ccit : Vec Bool 5 → Vec Bool 4
crc_poly_ccit = shift 0 2 >>> 
                dup 2     >>> 
                shift 3 1 >>> 
                seconds 2 (xorV *** 
                           xorV
                          )

crc_poly_ccit1 : Vec Bool 5 → Vec Bool 4
crc_poly_ccit1 = shift 0 2 >>> 
                dup 2     >>> 
                shift 3 1 >>> 
                firsts (xorV *** 
                        xorV
                       )

--crc_polynom_ccit : Vec Bool 5 → Vec Bool 4 
--crc_polynom_ccit 
--    =   mvRight >:> mvRight >:>
--        (   aAssoc 
--        >>> (aXor *** aXor)
--        )
-- crc_polynom_ccit 
--  = proc (x4, (x3, (x2, (x1, x0)))) → do
--      o1 <- aXor -< (x4, x0)
--      o2 <- aXor -< (x4, x1)
--      o3 <- aId  -< (x2)
--      o4 <- aId  -< (x3)
--      returnA    -< (o4, (o3, (o2, o1)))

----------------- A Universe for Arrows!? --------------------

record VArrow (_~~>_ : Set → Set → Set) : Set₁ where 
  field
    arr : ∀ {B n m}         → (Vec B n → Vec B m) → (Vec B n) ~~> (Vec B m)
    fsts : ∀ {B n m k}      → Vec B n ~~> Vec B m → Vec B (n + k) ~~> Vec B (m + k)    
    snds : ∀ {B n m}(k : ℕ) → Vec B n ~~> Vec B m → Vec B (k + n) ~~> Vec B (k + m) 
    _⋙_ : ∀ {B n m k}      → Vec B n ~~> Vec B m → Vec B m ~~> Vec B k → Vec B n ~~> Vec B k
    _*₃_ : ∀ {B n m k j}    → Vec B n ~~> Vec B m → Vec B k ~~> Vec B j → Vec B (n + k) ~~> Vec B (m + j)
    _&₃_ : ∀ {B n m k}      → Vec B n ~~> Vec B m → Vec B n ~~> Vec B k → Vec B n ~~> Vec B (m + k) 
  infixr 2 _⋙_


-- The Stream-Arrow Combinators
arrL : ∀ {B n m} → (Vec B n → Vec B m) → Vec B n ⇒S⇒ Vec B m
arrL f = map f

fstsL : ∀ {B n m k} → Vec B n ⇒S⇒ Vec B m → Vec B (n + k) ⇒S⇒ Vec B (m + k)
fstsL f xs = zipWith _++_ (f (map fst xsSplit)) (map snd xsSplit)
   where xsSplit = map split xs

sndsL : ∀ {B n m}(k : ℕ) → Vec B n ⇒S⇒ Vec B m → Vec B (k + n) ⇒S⇒ Vec B (k + m)
sndsL k f xs = zipWith _++_  (map fst xsSplit) (f (map snd xsSplit))
   where xsSplit = map ( split {_} {_} {k} ) xs 

_>>>L_ : ∀ {B n m k} → Vec B n ⇒S⇒ Vec B m → Vec B m ⇒S⇒ Vec B k → Vec B n ⇒S⇒ Vec B k
_>>>L_ f g xs = g (f xs)

_***L_ : ∀ {B n m k j} → Vec B n ⇒S⇒ Vec B m → Vec B k ⇒S⇒ Vec B j → Vec B (n + k) ⇒S⇒ Vec B (m + j)
_***L_ f g xs = zipWith _++_ (f (map fst xsSplit)) (g (map snd xsSplit))
   where xsSplit = map split xs

_&&&L_ : ∀ {B n m k} → Vec B n ⇒S⇒ Vec B m → Vec B n ⇒S⇒ Vec B k → Vec B n ⇒S⇒ Vec B (m + k)
_&&&L_ f g xs = zipWith _++_ (f xs) (g xs)

fnArrow : VArrow _=>_
fnArrow = record 
  { arr = λ f → f
  ; fsts = firsts
  ; snds = seconds
  ; _⋙_ = _>>>_
  ; _*₃_ = _***_
  ; _&₃_ = _&&&_ 
  }

strArrow : VArrow _⇒S⇒_
strArrow = record
  { arr = arrL
  ; fsts = fstsL
  ; snds = sndsL
  ; _⋙_ = _>>>L_
  ; _*₃_ = _***L_
  ; _&₃_ = _&&&L_
  } 

data Type : Set where
  fun    : Type
  stream : Type

El : Type → Set → Set → Set
El fun    = _=>_
El stream = _⇒S⇒_

xorVA : ∀ { _~~>_ } -> (VArrow _~~>_) → (Vec Bool 2) ~~> (Vec Bool 1)
xorVA arrow = arr xorV
  where open VArrow arrow

-- But: Its not really polymorph, is it?
crc_poly_ccit₁ : ∀ {_~~>_} -> (VArrow _~~>_) → Vec Bool 5 ~~> Vec Bool 4
crc_poly_ccit₁ arrow =  arr (shift 0 2) 
                     ⋙ arr (dup 2) 
                     ⋙ arr (shift 3 1) 
                     ⋙ snds 2 (arr xorV *₃ arr xorV)
   where open VArrow arrow
