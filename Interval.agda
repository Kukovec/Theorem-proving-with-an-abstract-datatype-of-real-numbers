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
    affLaw4 :(f : AbstractInterval → AbstractInterval)
      {x y : AbstractInterval} → f (m x y) ≡ m (f x) (f y) → f ≡ aff (f -One) (f One)

-- Constants and derived operations
  Zero = m -One One

  neg_ :  AbstractInterval → AbstractInterval
  neg_ = aff One (-One)

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

  infix 4 _:also:_
  _:also:_ : {A : Set}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
  refl :also: refl = refl

  fcong : {A B : Set}(f : A → B){x y : A} → x ≡ y → (f x) ≡ (f y)
  fcong f refl = refl

  reverseFcong : {A B : Set}{f g : A → B}(x : A) → f ≡ g → f x ≡ g x
  reverseFcong x refl = refl

  isTrue : {A : Set}(x : A) → x ≡ x
  isTrue x = refl

  mCong : {a b c d : AbstractInterval} → a ≡ c → b ≡ d → m a b ≡ m c d
  mCong refl refl = refl

  Id : {A : Set}(x : A) → A
  Id x = x

-- Proofs
-- neg (neg x) ≡ x

  singleNeg : neg One ≡ -One
  singleNeg = affLaw1 One -One

  singleNeg2 : neg -One ≡ One
  singleNeg2 = affLaw2 One -One

  doubleNeg : AbstractInterval → AbstractInterval
  doubleNeg x = neg (neg x)

  doubleNegOne : doubleNeg One ≡ One
  doubleNegOne = fcong (neg_) singleNeg :also: singleNeg2
  

  multipliedMidpointLemma : (x a b : AbstractInterval) → x * (m a b) ≡ m (x * a) (x * b)
  multipliedMidpointLemma x a b = (affLaw3 (neg x) x a b)

  doubleNegLemma : {y z : AbstractInterval}(x : AbstractInterval) → y ≡ z → aff y -One x ≡ aff z -One x
  doubleNegLemma x refl = refl

  negIsMultiplication : (x : AbstractInterval) → neg x ≡ -One * x
  negIsMultiplication x = doubleNegLemma x (sym doubleNegOne)
                          :also: doubleNegLemma x (fcong neg_ singleNeg)

  doubleNegAddition : (x y : AbstractInterval) → doubleNeg (m x y) ≡ m (doubleNeg x) (doubleNeg y)
  doubleNegAddition x y = (((((fcong (neg_) (negIsMultiplication (m x y))) :also:
                          negIsMultiplication (-One * (m x y))) :also:
                          fcong (_*_ -One) (multipliedMidpointLemma -One x y)) :also:
                          (multipliedMidpointLemma -One (-One * x) (-One * y))) :also:
                          mCong (fcong (_*_ -One) (sym (negIsMultiplication x))) (fcong (_*_ -One) (sym (negIsMultiplication y)))) :also:
                          mCong (sym (negIsMultiplication (neg x))) (sym (negIsMultiplication (neg y)))

  IdAdditive : {x y : AbstractInterval} → Id (m x y) ≡ m (Id x) (Id y)
  IdAdditive = refl

  doubleNegOk :  {x y : AbstractInterval} → doubleNeg (m x y) ≡ m (doubleNeg x) (doubleNeg y)
  doubleNegOk = doubleNegAddition _ _

  --doubleNegEquality : doubleNeg ≡ aff (doubleNeg -One) (doubleNeg One)
  --doubleNegEquality = affLaw4 (doubleNegAddition (_) (_))
  {-
  doubleNegIdentity : (x : AbstractInterval) → doubleNeg x ≡ x
  doubleNegIdentity One = doubleNegOne
  doubleNegIdentity -One = fcong (neg_) singleNeg2 :also: singleNeg
  doubleNegIdentity x = ((affLaw4 doubleNegOk ) ):also: (affLaw4 IdAdditive)
  -}

-- b) m (neg x) x ≡ Zero

  postulate *0 : (x : AbstractInterval) → x * Zero ≡ Zero

   

  someLaw : (x : AbstractInterval) → m (aff (neg x) x -One) (aff (neg x) x One) ≡ m (neg x) x
  someLaw x =  mCong (affLaw2 (neg x) x) (affLaw1 (neg x) x)
  
  zeroMidpoint : (x : AbstractInterval) →  m (neg x) x ≡ Zero
  zeroMidpoint x = sym (multipliedMidpointLemma x -One One :also: someLaw x):also: *0 x
  
-- c) x * Zero ≡ x:
  auxTimesZero1 : (x : AbstractInterval) →
    x * Zero ≡ m (aff (neg x) x -One) (aff (neg x) x One)
  auxTimesZero1 x = affLaw3 (neg x) x -One One


  auxTimesZero2 : (x : AbstractInterval) →
    m (neg x) x ≡ m (aff (neg x) x -One) (aff (neg x) x One)
  auxTimesZero2 x = sym (mCong (affLaw2 (neg x) x) (affLaw1 (neg x) x))

  postulate x-x : (x : AbstractInterval) → m (neg x) x ≡ Zero
  
  timesZero : (x : AbstractInterval) → x * Zero ≡ Zero
  timesZero x = (auxTimesZero1 x :also: sym (auxTimesZero2 x)) :also: (x-x x)

-- d) x * y ≡ y * x

  --timesCommutative : (x y : AbstractInterval) → x * y ≡ y * x
--  timesCommutative x y = 

{-

x * y =def= aff (neg x) x y
      =def= aff (aff 1 -1 x) x y
      =m1 = aff -x x (m y y)
      =a3 = m (aff -x x y) (aff -x x y)

-}
