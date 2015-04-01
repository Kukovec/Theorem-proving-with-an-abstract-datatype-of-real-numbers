{-
  This file contains outdated proofs of various theorems, which were saved so you could
  see the horrible inefficiency this author displayed whilst familiarizing himself with Agda or just
  generally attempting to prove things in a roundabout way. The lemmas they rely on are often omitted.


--  [ doubleNeg x ≡ x ]

  doubleNegAddition : ( x y : AbstractInterval ) → doubleNeg (m x y) ≡ m (doubleNeg x) (doubleNeg y)
  doubleNegAddition x y  = (((((fcong (neg_) (negIsMultiplication (m x y))) :also:
                          negIsMultiplication (-One * (m x y))) 
                         :also:
                          fcong (_*_ -One) (multipliedMidpointLemma -One x y)) 
                         :also:
                          (multipliedMidpointLemma -One (-One * x) (-One * y))) 
                         :also:
                          mCong (fcong (_*_ -One) (sym (negIsMultiplication x))) (fcong (_*_ -One) (sym (negIsMultiplication y)))) 
                         :also:
                          mCong (sym (negIsMultiplication (neg x))) (sym (negIsMultiplication (neg y)))
  
-- [ x * Zero ≡ Zero ]


  auxTimesZero1 : (x : AbstractInterval) →
    x * Zero ≡ m (aff (neg x) x -One) (aff (neg x) x One)
  auxTimesZero1 x = affLaw3 (neg x) x -One One

  auxTimesZero2 : (x : AbstractInterval) →
    m (neg x) x ≡ m (aff (neg x) x -One) (aff (neg x) x One)
  auxTimesZero2 x = sym (mCong (affLaw2 (neg x) x) (affLaw1 (neg x) x))

  postulate x-x : (x : AbstractInterval) → m (neg x) x ≡ Zero

  timesZero : (x : AbstractInterval) → x * Zero ≡ Zero
  timesZero x = (auxTimesZero1 x :also: sym (auxTimesZero2 x)) :also: (x-x x)


-}

