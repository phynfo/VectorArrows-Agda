# VectorArrows-Agda

Experiments in defining an Arrow-Like interface for fixed-size-Vectors in Agda

## The Interface

### Combinators: 


```haskell
record VArrow (_~~>_ : Set → Set → Set) : Set₁ where 
  field
    arr : ∀ {B n m}         → (Vec B n → Vec B m) → (Vec B n) ~~> (Vec B m)
    fsts : ∀ {B n m k}      → Vec B n ~~> Vec B m → Vec B (n + k) ~~> Vec B (m + k)    
    snds : ∀ {B n m}(k : ℕ) → Vec B n ~~> Vec B m → Vec B (k + n) ~~> Vec B (k + m) 
    _⋙_ : ∀ {B n m k}      → Vec B n ~~> Vec B m → Vec B m ~~> Vec B k → Vec B n ~~> Vec B k
    _*₃_ : ∀ {B n m k j}    → Vec B n ~~> Vec B m → Vec B k ~~> Vec B j → Vec B (n + k) ~~> Vec B (m + j)
    _&₃_ : ∀ {B n m k}      → Vec B n ~~> Vec B m → Vec B n ~~> Vec B k → Vec B n ~~> Vec B (m + k) 
  infixr 2 _⋙_
```



### Helpful functions: 

`shift i j` shifts wire number `i` for `j` positions to the right.
```haskell
shift : {A : Set}{n : Nat} -> (i : Nat) -> (j : Nat) -> Vec A (1 + i + j + n) -> Vec A (1 + i + j + n)
```

`dup i` duplicates wire number `i`. 
```haskell
dup : {A : Set}{n : Nat} -> (i : Nat) -> Vec A (1 + i + n) -> Vec A (2 + i + n)
```

## Examples

A part of the CRC-Algorithm programmed with this interface: 

```haskell
crc_poly_ccit₁ : ∀ {_~~>_} -> (VArrow _~~>_) → Vec Bool 5 ~~> Vec Bool 4
crc_poly_ccit₁ arrow =  arr (shift 0 2) 
                     ⋙ arr (dup 2) 
                     ⋙ arr (shift 3 1) 
                     ⋙ snds 2 (arr xorV *₃ arr xorV)
   where open VArrow arrow
```

(sinve the `(VArrow _~~>_)` is explicit, I feel its still not really polymorph in the Arrow...

(for comparison: Matthias' implementation with Haskell-Arrows works as follows: 
```
crc_polynom_ccit 
    =   mvRight >:> mvRight >:>
        (   aAssoc 
        >>> (aXor *** aXor)
        )
```
... and the same expressed via the proc-notation: 
```haskell
crc_polynom_ccit 
   = proc (x4, (x3, (x2, (x1, x0)))) -> do
        o1 <- aXor -< (x4, x0)
        o2 <- aXor -< (x4, x1)
        o3 <- aId  -< (x2)
        o4 <- aId  -< (x3)
        returnA    -< (o4, (o3, (o2, o1)))
```


