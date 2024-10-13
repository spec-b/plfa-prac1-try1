---
title     : "Naturals: Natural numbers"
permalink : /Naturals/
---

```agda
module plfa.part1.Naturals where
```

    --------
    zero : ℕ

    m : ℕ
    ---------
    suc m : ℕ

And here is the definition in Agda:
```agda
data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ
```

#### Exercise `seven` (practice) {#seven}

Write out `7` in longhand.

```agda
-- Your code goes here
seven : ℕ 
seven = suc (suc (suc (suc (suc ( suc ( suc (zero)))))))
```
_ : seven ≡ 7 
_ = refl (couldn't make this work because of not in scope error)

You will need to give both a type signature and definition for the
variable `seven`. Type `C-c C-l` in Emacs to instruct Agda to re-load.



In Agda, any text following `--` or enclosed between `{-`
and `-}` is considered a _comment_.  Comments have no effect on the
code, with the exception of one special kind of comment, called a
_pragma_, which is enclosed between `{-#` and `#-}`.

Including the line
```agda
{-# BUILTIN NATURAL ℕ #-}
```



```agda
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; step-≡-∣; _∎)
```


Here is the definition of addition in Agda:
```agda
_+_ : ℕ → ℕ → ℕ
zero + n = n
(suc m) + n = suc (m + n)
```


For example, let's add two and three:
```agda
_ : 2 + 3 ≡ 5
_ =
  begin
    2 + 3
  ≡⟨⟩    -- is shorthand for
    (suc (suc zero)) + (suc (suc (suc zero)))
  ≡⟨⟩    -- inductive case
    suc ((suc zero) + (suc (suc (suc zero))))
  ≡⟨⟩    -- inductive case
    suc (suc (zero + (suc (suc (suc zero)))))
  ≡⟨⟩    -- base case
    suc (suc (suc (suc (suc zero))))
  ≡⟨⟩    -- is longhand for
    5
  ∎
```
We can write the same derivation more compactly by only
expanding shorthand as needed:
```agda
_ : 2 + 3 ≡ 5
_ =
  begin
    2 + 3
  ≡⟨⟩
    suc (1 + 3)
  ≡⟨⟩
    suc (suc (0 + 3))
  ≡⟨⟩
    suc (suc 3)
  ≡⟨⟩
    5
  ∎
```


#### Exercise `+-example` (practice) {#plus-example}

Compute `3 + 4`, writing out your reasoning as a chain of equations, using the equations for `+`.

```agda
-- Your code goes here
_ : 3 + 4 ≡ 7 
_ = refl 
```


## Multiplication

Once we have defined addition, we can define multiplication
as repeated addition:
```agda
_*_ : ℕ → ℕ → ℕ

zero    * n  =  zero
(suc m) * n  =  n + (m * n)
```
Computing `m * n` returns the sum of `m` copies of `n`.


For example, let's multiply two and three:
```agda
_ =
  begin
    2 * 3
  ≡⟨⟩    -- inductive case
    3 + (1 * 3)
  ≡⟨⟩    -- inductive case
    3 + (3 + (0 * 3))
  ≡⟨⟩    -- base case
    3 + (3 + 0)
  ≡⟨⟩    -- simplify
    6
  ∎
```


#### Exercise `*-example` (practice) {#times-example}

Compute `3 * 4`, writing out your reasoning as a chain of equations, using the equations for `*`.
(You do not need to step through the evaluation of `+`.)

```agda
-- Your code goes here
_ =
  begin
    3 * 4
  ≡⟨⟩    -- inductive case
    4 + 4 + (1 * 4)
  ≡⟨⟩    -- inductive case
    4 + 4 + (1 * 4 + (0 * 4))
  ≡⟨⟩    -- base case
    4 + 4 + 4 + 0
  ≡⟨⟩    -- simplify
    12
  ∎
```


#### Exercise `_^_` (recommended) {#power}

Define exponentiation, which is given by the following equations:

    m ^ 0        =  1
    m ^ (1 + n)  =  m * (m ^ n)

Check that `3 ^ 4` is `81`.

```agda
-- Your code goes here
_^_ : ℕ → ℕ → ℕ 

m ^ zero = 1 
m ^ (suc n) = m * (m ^ n)
```
```
_ = 
  begin 
  3 ^ 4 
  ≡⟨⟩
  3 ^ (suc 3) 
  ≡⟨⟩
  3 * (3 ^ 3)
  ≡⟨⟩
  3 * (3 ^ (suc 2))
  ≡⟨⟩
  3 * (3 * (3 ^ 2))
  ≡⟨⟩
  3 * (3 * (3 ^ (suc 1)))
  ≡⟨⟩ 
  3 * (3 * (3 * (3 ^ 1)))
  ≡⟨⟩
  3 * (3 * (3 * (3 ^ (suc 0))))
  ≡⟨⟩ 
  3 * (3 * (3 * (3 * (3 ^ 0))))
  ≡⟨⟩
  3 * (3 * (3 * (3 * 1)))
  ≡⟨⟩
  3 * (3 * (3 * 3))
  ≡⟨⟩
  3 * (3 * 9)
  ≡⟨⟩
  3 * 27
  ≡⟨⟩
  81 
  ∎
```

## Monus

```agda
_∸_ : ℕ → ℕ → ℕ
m     ∸ zero   =  m
zero  ∸ suc n  =  zero
suc m ∸ suc n  =  m ∸ n
```


For example, let's subtract two from three:
```agda
_ =
  begin
    3 ∸ 2
  ≡⟨⟩
    2 ∸ 1
  ≡⟨⟩
    1 ∸ 0
  ≡⟨⟩
    1
  ∎
```
We did not use the second equation at all, but it will be required
if we try to subtract a larger number from a smaller one:
```agda
_ =
  begin
    2 ∸ 3
  ≡⟨⟩
    1 ∸ 2
  ≡⟨⟩
    0 ∸ 1
  ≡⟨⟩
    0
  ∎
```



#### Exercise `∸-example₁` and `∸-example₂` (recommended) {#monus-examples}

Compute `5 ∸ 3` and `3 ∸ 5`, writing out your reasoning as a chain of equations.

```agda
-- Your code goes here
_ = 
  begin 
  5 ∸ 3 
  ≡⟨⟩
  4 ∸ 2
  ≡⟨⟩
  3 ∸ 1
  ≡⟨⟩
  2 ∸ 0
  ≡⟨⟩
  2 
  ∎

_ = 
  begin 
  3 ∸ 5 
  ≡⟨⟩
  2 ∸ 4
  ≡⟨⟩ 
  1 ∸ 3
  ≡⟨⟩
  0 ∸ 2
  ≡⟨⟩ 
  0 
  ∎
```


## Precedence

```agda
infixl 6  _+_  _∸_
infixl 7  _*_
```




#### Exercise `Bin` (stretch) {#Bin}

A more efficient representation of natural numbers uses a binary
rather than a unary system.  We represent a number as a bitstring:
```agda
data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin
```
For instance, the bitstring

    1011

standing for the number eleven is encoded as

    ⟨⟩ I O I I

Representations are not unique due to leading zeros.
Hence, eleven is also represented by `001011`, encoded as:

    ⟨⟩ O O I O I I

Define a function

    inc : Bin → Bin

that converts a bitstring to the bitstring for the next higher
number.  For example, since `1100` encodes twelve, we should have:

    inc (⟨⟩ I O I I) ≡ ⟨⟩ I I O O

Confirm that this gives the correct answer for the bitstrings
encoding zero through four.

Using the above, define a pair of functions to convert
between the two representations.

    to   : ℕ → Bin
    from : Bin → ℕ

For the former, choose the bitstring to have no leading zeros if it
represents a positive natural, and represent zero by `⟨⟩ O`.
Confirm that these both give the correct answer for zero through four.

```agda
-- Your code goes here
inc : Bin → Bin 
inc ⟨⟩ = ⟨⟩ I 
inc (b O) = b I
inc (b I) = (inc b) O

to : ℕ → Bin 
to 0 = ⟨⟩ O
to (suc x) = inc (to x)  

from : Bin → ℕ 
from ⟨⟩  = 0 
from (b O) = 2 * from b 
from (b I) = 2 * from b + 1

```


```agda
-- import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _∸_)
```

