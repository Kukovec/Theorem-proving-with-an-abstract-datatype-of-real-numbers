open import First

--ℕ = First.ℕ
--_≡_ = First._≡_
--zero = First.zero


module Interval where

  data AbstractInterval : Set where
    One : AbstractInterval
    -One : AbstractInterval
    M : (ℕ → AbstractInterval) → AbstractInterval
    m : AbstractInterval → AbstractInterval → AbstractInterval
    aff : AbstractInterval → AbstractInterval → AbstractInterval → AbstractInterval
    dbl : AbstractInterval → AbstractInterval


-- Helper function, performs left-shifting on a sequence.
  shiftByOne :  (f : ℕ → AbstractInterval) → (n : ℕ) → AbstractInterval
  shiftByOne f n = f (suc n)

-- Axioms for M, m and aff
-- TODO : MLaw2, requires implication defined
--      : affLaw4, requires if, &&, ||, etc.

  postulate
    MLaw1 : (f : ℕ → AbstractInterval) →
      M f ≡ m (f zero) (M (shiftByOne f))
    
    mLaw1 : (t : AbstractInterval)  →
      m t t ≡ t
    mLaw2 : (t u : AbstractInterval) →
      m t u ≡ m u t
    mLaw3 : (t u v w : AbstractInterval) →
      m (m t u) (m v w) ≡ m (m t v) (m u w)
    
    affLaw1 : (t u : AbstractInterval) →
      aff t u One ≡ u
    affLaw2 : (t u : AbstractInterval) →
      aff t u -One ≡ t
    affLaw3 : (t u v w : AbstractInterval) →
      aff t u (m v w) ≡ m (aff t u v) (aff t u w)

-- Constants and derived operations
  Zero = m -One One

  neg_ :  AbstractInterval → AbstractInterval
  neg x = aff One (-One) x

  _*_ : AbstractInterval → AbstractInterval → AbstractInterval
  x * y = aff (neg x) x y

  flip : AbstractInterval → AbstractInterval
  flip One = -One
  flip _ = One 

  altOnes : ℕ → AbstractInterval
  altOnes zero = One
  altOnes (suc n) = flip (altOnes n)

  oneThird = M altOnes

  postulate y : AbstractInterval -- Abstract member for testing


-- Helper syntax

  infix 100 _:also:_
  _:also:_ : {A : Set}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
  refl :also: refl = refl

  fcong : {A B : Set}(f : A → B){x y : A} → x ≡ y → (f x) ≡ (f y)
  fcong f refl = refl

  mCong : {a b c d : AbstractInterval} → a ≡ c → b ≡ d → m a b ≡ m c d
  mCong refl refl = refl

-- Proofs
-- a) m (neg x) x ≡ Zero

  postulate *0 : (x : AbstractInterval) → x * Zero ≡ Zero

  multipliedMidpoint : (x a b : AbstractInterval) → x * (m a b) ≡ m (x * a) (x * b)
  multipliedMidpoint x a b = (affLaw3 (neg x) x a b) 

  someLaw : (x : AbstractInterval) → m (aff (neg x) x -One) (aff (neg x) x One) ≡ m (neg x) x
  someLaw x =  mCong (affLaw2 (neg x) x) (affLaw1 (neg x) x)
  
  zeroMidpoint : (x : AbstractInterval) →  m (neg x) x ≡ Zero
  zeroMidpoint x = sym (multipliedMidpoint x -One One :also: someLaw x):also: *0 x
  
-- b) x * Zero ≡ x:
  auxTimesZero1 : (x : AbstractInterval) →
    x * Zero ≡ m (aff (neg x) x -One) (aff (neg x) x One)
  auxTimesZero1 x = affLaw3 (neg x) x -One One


  auxTimesZero2 : (x : AbstractInterval) →
    m (neg x) x ≡ m (aff (neg x) x -One) (aff (neg x) x One)
  auxTimesZero2 x = sym (mCong (affLaw2 (neg x) x) (affLaw1 (neg x) x))

  postulate x-x : (x : AbstractInterval) → m (neg x) x ≡ Zero
  
  timesZero : (x : AbstractInterval) → x * Zero ≡ Zero
  timesZero x = (auxTimesZero1 x :also: sym (auxTimesZero2 x)) :also: (x-x x)

-- c) x * y ≡ y * x

  --timesCommutative : (x y : AbstractInterval) → x * y ≡ y * x
--  timesCommutative x y = 

{-

x * y =def= aff (neg x) x y
      =def= aff (aff 1 -1 x) x y
      =m1 = aff -x x (m y y)
      =a3 = m (aff -x x y) (aff -x x y)

-}
