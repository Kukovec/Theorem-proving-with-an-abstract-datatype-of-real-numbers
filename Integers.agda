open import First
--import Interval

--_also_ = Interval._:also:_

--_≡_ = First._≡_

module Integers where

{-
  data ℤ₊ : Set where
    one : ℤ₊
    suc : ℤ₊ → ℤ₊

  :nat: : ℤ₊ → First.ℕ
  :nat: one = First.one
  :nat: (suc n) = First.suc (:nat: n)

  :z+: : First.ℕ → ℤ₊
  :z+: First.zero = one
  :z+: (First.suc First.zero) = one
  :z+: (First.suc n) = suc (:z+: n)
    
  posmin : (k l : ℤ₊) → ℤ₊
  posmin one     _       = one
  posmin _       one     = one
  posmin (suc k) (suc l) = suc (posmin k l)
  
  posmax : (k l : ℤ₊) → ℤ₊
  posmax one     k       = k
  posmax k       one     = k
  posmax (suc k) (suc l) = suc (posmax k l)

  _pos+_ : (k l : ℤ₊) → ℤ₊
  one     pos+ k = suc k
  (suc k) pos+ l = suc (k pos+ l)

  two = suc one

  data Z : Set where
    POS0 : First.ℕ → Z
    NEG : ℤ₊ → Z

  :neg: : Z → Z
  :neg: (POS0 First.zero) = POS0 (First.zero)
  :neg: (POS0 (First.suc n)) = NEG (:z+: (First.suc n))
  :neg: (NEG z) = POS0 (:nat: z)

  toNat : Z → First.ℕ
  toNat (POS0 n) = n
  toNat _ = First.zero

  max : (k l : Z) → Z
  max (POS0 k) (NEG l) = POS0 k
  max (POS0 k) (POS0 l) = POS0 (First.max k l)
  max (NEG l) (POS0 k) = POS0 k
  max (NEG k) (NEG l) = NEG (posmin k l)

  _:+:_ : Z → Z → Z
  (POS0 k) :+: (POS0 l) = POS0 (k First.nat+ l)
  _ :+: _ = NEG one

  _:-:_ : (k l : Z) → Z
  k :-: l = k :+: (:neg: l)

  data Bool : Set where
    T : Bool
    F : Bool

  isPos : Z → Bool
  isPos (POS0 _) = T
  isPos (NEG _) = F

  _*1[_] : Z → Bool → Z
  x *1[ T ] = x
  x *1[ F ] = POS0 (First.zero)

  _*1[_≥_] : Z → Z → Z → Z
  z *1[ x ≥ y ] = z *1[ isPos (x :-: y) ]

  postulate altMaxLemma : (k l : Z) →
                        max k l ≡ ((k :+: ((k :-: l) *1[ k ≥ l ])) :+: ((l :-: k) *1[ l ≥ k ]))

  postulate maxLemma : (k l : Z) → (max k l) ≡ (k :+: (max (POS0 First.zero) (l :-: k)))

  postulate joinTonat : (k l : First.ℕ) →
                      ((toNat (POS0 k)) First.nat+ (toNat (POS0 l))) ≡ (toNat (POS0 (k First.nat+ l)))

  postulate maxComm : (k l : Z) → max k l ≡ max l k

  alwaysPos : (k l : Z) → isPos(max k l :-: k) ≡ T
  alwaysPos k l = Interval.fcong (isPos) (Interval.fcong (λ (x : Z) → x :-: k) (altMaxLemma k l))  also {!!}
-}

{-
  data ℤ : Set where
    zero : ℤ
    POS  : ℤ₊ → ℤ
    NEG  : ℤ₊ → ℤ

  :neg: : ℤ → ℤ
  :neg: zero = zero
  :neg: (POS k) = NEG k
  :neg: (NEG k) = POS k

  min :(k l : ℤ) → ℤ
  min (POS k) (NEG l) = NEG l
  min (POS k) (POS l) = POS (posmin k l)
  min (NEG l) (POS k) = NEG l
  min (NEG k) (NEG l) = NEG (posmax k l)
  min zero    (NEG k) = NEG k
  min zero    _       = zero
  min (NEG k) zero    = NEG k
  min _       zero    = zero

  max :(k l : ℤ) → ℤ
  max k l = :neg: (min (:neg: k) (:neg: l))
  
  toNat : (k : ℤ) → First.ℕ
  toNat (POS one)     = First.one
  toNat (POS (suc k)) = First.suc (toNat (POS k))
  toNat _             = First.zero
 

  _:+:_ : (k l : ℤ) → ℤ
  zero          :+: l             = l
  l             :+: zero          = l
  
  (POS k)       :+: (POS l)       = POS (k pos+ l)
  (NEG k)       :+: (NEG l)       = NEG (k pos+ l)

  (POS (suc k)) :+: (NEG one)     = POS k
  (POS one)     :+: (NEG one)     = zero
  (POS (suc k)) :+: (NEG (suc l)) = (POS k) :+: (NEG l)
  (POS one)     :+: (NEG (suc l)) = NEG l

  (NEG one)     :+: (POS (suc k)) = POS k
  (NEG one)     :+: (POS one)     = zero
  (NEG (suc l)) :+: (POS (suc k)) = (POS k) :+: (NEG l)
  (NEG (suc l)) :+: (POS one)     = NEG l



-}

  data ℤ : Set where
    POS : ℕ → ℤ
    NEG : ℕ → ℤ -- NEG x == -( x + 1)

  :neg: : ℤ → ℤ
  :neg: (POS zero)  = POS zero
  :neg: (POS (suc k)) = NEG k
  :neg: (NEG k) = POS (suc k)

  toNat : (k : ℤ) → First.ℕ
  toNat (POS k) = k
  toNat _       = zero

  _:+:_ : (k l : ℤ) → ℤ
  POS zero :+: k = k
  POS k :+: (POS l) = POS (k nat+ l)
  NEG k :+: (NEG l) = NEG (suc (k nat+ l))
  
  POS (suc k) :+: (NEG zero) = POS k
  POS (suc k) :+: (NEG (suc l)) = (POS k) :+: (NEG l)

  (NEG l) :+: (POS zero) = NEG l
  (NEG zero) :+: POS (suc k) = POS k
  (NEG (suc l)) :+: POS (suc k) = (POS k) :+: (NEG l)

  _:-:_ : (k l : ℤ) → ℤ
  k :-: l = k :+: (:neg: l)

  natMax : ℕ → ℕ → ℕ
  natMax n zero = n
  natMax zero n = n
  natMax (suc n) (suc k) = suc (natMax n k)

  natMin : ℕ → ℕ → ℕ
  natMin n zero = zero
  natMin zero n = zero
  natMin (suc n) (suc k) = suc (natMin n k)

  max : ℤ →  ℤ → ℤ
  max (POS k) (NEG l) = POS k
  max (POS k) (POS l) = POS (natMax k l)
  max (NEG k) (POS l) = POS l
  max (NEG k) (NEG l) = NEG (natMin k l)
