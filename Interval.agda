open import First

module Interval where

-- Defines the interface of the abstract interval type
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
-- TODO : MLaw2, when needed

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
    affLaw4 :(f : AbstractInterval → AbstractInterval) → 
      ((x y : AbstractInterval) → f (m x y) ≡ m (f x) (f y)) → f ≡ aff (f -One) (f One)

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

  reverseFcong : {A B : Set}{f g : A → B}(x : A) → f ≡ g → (f x) ≡ (g x)
  reverseFcong x refl = refl

  doubleFcong : {A B C : Set}{a c : A}{b d : B}(f : A → B → C) →
    a ≡ c → b ≡ d → f a b ≡ f c d
  doubleFcong f refl refl = refl

  mCong : {a b c d : AbstractInterval} → a ≡ c → b ≡ d → m a b ≡ m c d
  mCong refl refl = doubleFcong m refl refl

  Id : {A : Set}(x : A) → A
  Id x = x

  isTrue : {A : Set}(x : A) → x ≡ x
  isTrue x = refl

-- **************
-- *   Proofs   *
-- **************

-- +-----------------+
-- | neg (neg x) ≡ x |
-- +-----------------+

  -- Helper lemmas for base cases of applying neg to One or -One
  singleNeg : neg One ≡ -One
  singleNeg = affLaw1 One -One

  singleNeg2 : neg -One ≡ One
  singleNeg2 = affLaw2 One -One
  
  -- Function performing double negation
  doubleNeg : AbstractInterval → AbstractInterval
  doubleNeg x = neg (neg x)
  
  -- Negation satisfies the conditions for affLaw4
  negAddition : (x y : AbstractInterval) → neg (m x y) ≡ m (neg x) (neg y)
  negAddition x y = affLaw3 One -One x y

  -- Consequently, so does doubleNeg
  doubleNegAddition : (x y : AbstractInterval) → doubleNeg (m x y) ≡ m (doubleNeg x) (doubleNeg y)
  doubleNegAddition x y = fcong (neg_) (negAddition x y) :also: negAddition (neg x) (neg y)

  -- After applying affLaw4, the result is:
  doubleNegEquality : doubleNeg ≡ aff (doubleNeg -One) (doubleNeg One)
  doubleNegEquality = affLaw4 (doubleNeg) (doubleNegAddition)

  -- We now reduce doubleNeg One and doubleNeg -One to One and -One respectively
  doubleNegIdentityOne : doubleNeg One ≡ One
  doubleNegIdentityOne = fcong (neg_) singleNeg :also: singleNeg2
  doubleNegIdentityNegOne : doubleNeg -One ≡ -One
  doubleNegIdentityNegOne = fcong (neg_) singleNeg2 :also: singleNeg

  -- The final law obtained gives us the connection between doubleNeg and aff
  doubleNegReducedEquality : doubleNeg ≡ aff -One One
  doubleNegReducedEquality =
    doubleNegEquality :also: doubleFcong aff doubleNegIdentityNegOne doubleNegIdentityOne

  -- We now prove that Id also equals Aff -One One

  IdAddition : (x y : AbstractInterval) → Id (m x y) ≡ m (Id x) (Id y)
  IdAddition x y = refl

  IdEquality : Id ≡ aff -One One
  IdEquality = affLaw4 Id IdAddition
  
  -- Transitivity implies doubleNeg ≡ Id and (reverse) congurence gives us doubleNeg x ≡ Id x (= x)
  doubleNegIdentity : doubleNeg ≡ Id
  doubleNegIdentity = doubleNegReducedEquality :also: sym IdEquality

  doubleNegIdentityUse : (x : AbstractInterval) → doubleNeg x ≡ x
  doubleNegIdentityUse x = reverseFcong x doubleNegIdentity
 
-- +------------------+
-- | neg x ≡ -One * x |
-- +------------------+


  -- We introduce a lemma that is a special case of congruence, to break up the actual proof
  negMultiLemma : {y z : AbstractInterval}(x : AbstractInterval) → y ≡ z → aff y -One x ≡ aff z -One x
  negMultiLemma x eq = reverseFcong x (doubleFcong aff eq (isTrue -One))
  
  negIsMultiplication : (x : AbstractInterval) → neg x ≡ -One * x
  negIsMultiplication x = negMultiLemma x (sym (doubleNegIdentityOne)) :also: negMultiLemma x (fcong neg_ singleNeg)

-- +---------------------------------+
-- | x * (m a b) ≡ m (x * a) (x * b) |
-- +---------------------------------+

  -- Follows trivially from affLaw3
  multipliedMidpointLemma : (x a b : AbstractInterval) → x * (m a b) ≡ m (x * a) (x * b)
  multipliedMidpointLemma x a b = (affLaw3 (neg x) x a b)
 
-- +--------------------+
-- | m x (neg x) ≡ Zero |
-- +--------------------+

  -- We will prove that negMidpoint and zeroFunction defined below are equivalent
  zeroFunction : (x : AbstractInterval) → AbstractInterval
  zeroFunction x = Zero

  negMidpoint : (x : AbstractInterval) → AbstractInterval
  negMidpoint x = m x (neg x)

  -- First we show that negMidpoint and zeroFunction satisfiy the conditions to use affLaw4
  negMidpointAddition : (x y : AbstractInterval) → negMidpoint (m x y) ≡ m (negMidpoint x) (negMidpoint y)
  negMidpointAddition x y = fcong (m (m x y)) (negAddition x y) :also: mLaw3 x y (neg x) (neg y)

  zeroFunctionAddition : (x y : AbstractInterval) → zeroFunction (m x y) ≡ m (zeroFunction x) (zeroFunction y)
  zeroFunctionAddition x y = sym (mLaw1 Zero)

  -- Next we show that negMidpoint maps One and -One to Zero
  negMidpointOne : negMidpoint One ≡ Zero
  negMidpointOne = mCong (isTrue One) singleNeg :also: mLaw2 One -One
  negMidpointNegOne : negMidpoint -One ≡ Zero
  negMidpointNegOne = mCong (isTrue -One) singleNeg2

  -- From that we obtain a neat expression for negMidpoint by using affLaw4 
  negMidpointEquality : negMidpoint ≡ aff Zero Zero
  negMidpointEquality = affLaw4 negMidpoint negMidpointAddition :also: doubleFcong aff negMidpointNegOne negMidpointOne

  -- Finally, we show that zeroFunction satisfies the same relation, which is trivial
  zeroFunctionEquality : zeroFunction ≡ aff Zero Zero
  zeroFunctionEquality = affLaw4 zeroFunction zeroFunctionAddition

  -- Transitivity and (reverse) congruence yield the desired result
  negMidpointIdentity : negMidpoint ≡ zeroFunction
  negMidpointIdentity = negMidpointEquality :also: sym zeroFunctionEquality

  negMidpointIdentityUse : (x : AbstractInterval) → m x (neg x) ≡ Zero
  negMidpointIdentityUse x = reverseFcong x negMidpointIdentity

-- +-----------------+
-- | x * Zero ≡ Zero |
-- +-----------------+

  -- This proof follows from the fact that m (neg x) x ≡ Zero
  -- First we introduce a lemma linking multiplication by zero with negMidpoint
  timesZeroLemma : (x : AbstractInterval) → x * Zero ≡ m (neg x) x
  timesZeroLemma x = affLaw3 (neg x) x -One One :also: mCong (affLaw2 (neg x) x) (affLaw1 (neg x) x)

  -- The rest is then trivially proven with the help of mLaw2
  timesZero : (x : AbstractInterval) → x * Zero ≡ Zero
  timesZero x = timesZeroLemma x :also: (mLaw2 (neg x) x :also: negMidpointIdentityUse x) 

-- +---------------+
-- | x * y ≡ y * x |
-- +---------------+

{- TODO -}
