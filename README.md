# VectorArrows-Agda

Experiments in defining an Arrow-Like interface for fixed-size-Vectors in Agda

## The Interface

### Combinators: 

```haskell
_***_ : {A : Set}{n m k j : Nat} -> (Vec A n -> Vec A m) -> (Vec A k -> Vec A j) -> Vec A (n + k) -> Vec A (m + j)
_&&&_ : {A : Set}{n m k : Nat} -> (Vec A n -> Vec A m) -> (Vec A n -> Vec A k) -> Vec A n -> Vec A (m + k)
_>>>_ : {A B C : Set} -> (A -> B) -> (B -> C) -> (A -> C)
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
crc_poly_ccit : Vec Bool 5 -> Vec Bool 4
crc_poly_ccit = shift 0 2 >>> 
                dup 2     >>> 
                shift 3 1 >>> 
                seconds 2 (xorV *** 
                           xorV
                          )
```

(for comparison: Matthias' implementation with Haskell-Arrows works as follows: 
```
crc_polynom_ccit : Vec Bool 5 -> Vec Bool 4 
crc_polynom_ccit 
    =   mvRight >:> mvRight >:>
        (   aAssoc 
        >>> (aXor *** aXor)
        )
``
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


