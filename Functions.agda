open import Interval
open import Integers
open import First



module Functions where

  divByPow : (x : AbstractInterval) → (n : First.ℕ) → AbstractInterval
  divByPow x zero = x
  divByPow x (suc n) = m (divByPow x n) Zero

  data ℝ : Set where
    <_,_> : (x : AbstractInterval) → (z : ℤ) → ℝ -- represents x * 2^z

  projAI : ℝ → AbstractInterval
  projAI < x , k > = x
  projℤ : ℝ → ℤ
  projℤ < x , k > = k


  - : ℝ → ℝ
  - < x , z > = < (neg x) , z >

  infix 4 _+_
  _+_ : ℝ → ℝ → ℝ
  < x , z > + < y , w > = < m
                            (divByPow x (toNat (max z w :-: z)))
                            (divByPow x (toNat (max z w :-: w)))
                          , max z w :+: (POS one) >

  infix 4 _×_
  _×_ : ℝ → ℝ → ℝ
  < x , z > × < y , w > = < x * y , z :+: w >

  --~ : {x y : AbstractInterval} {k l : ℤ} → (divByPow x  (toNat (max k l :-: k)) ≡ divByPow y (toNat (max k l :-: l))) → (< x , k > ≡ < y , l >)
  --~ First.refl = First.refl

  infix 4 _~_
  data _~_ : ℝ → ℝ → Set where
    equiv : (x y : AbstractInterval) → (k l : ℤ) → divByPow x  (toNat (max k l :-: k)) ≡ divByPow y (toNat (max k l :-: l)) → < x , k > ~ < y , l >


--  _~_ : ℝ → ℝ → Set
--  < x , k > ~ < y , l > = (divByPow x  (toNat (max k l :-: k)) ≡ divByPow y (toNat (max k l :-: l)))

  rOne : ℝ
  rOne = < One , POS zero >
  -rOne : ℝ
  -rOne = < -One , POS zero >
  rZero : ℝ
  rZero = < Zero , POS zero >

  data pair<_,_> (A B : Set) : Set where
    [_,_] : A → B → pair< A , B >

  first : {A B : Set} → pair< A , B > → A
  first [ x , y ] = x

  second : {A B : Set} → pair< A , B > → B
  second [ x , y ] = y


  data bool : Set where
    true  : bool
    false : bool

  _≤_ : ℕ → ℕ → bool
  zero    ≤ n       = true
  (suc k) ≤ zero    = false
  (suc k) ≤ (suc n) = k ≤ n

  _:natsub:_ : ℕ → ℕ → ℕ
  k       :natsub: zero    = k
  zero    :natsub: k       = zero
  (suc k) :natsub: (suc n) = k :natsub: n

  if_then_else_ : {A : Set} → bool → A → A → A
  if true then x else y = x
  if false then x else y = y

  pow2 : ℕ → ℕ
  pow2 zero = First.one
  pow2 (suc n)= (suc (suc zero)) nat* (pow2 n )

  pow : AbstractInterval → ℕ → AbstractInterval
  pow x zero = One
  pow x (suc n) = x * (pow x n)

  2^_-1 : ℕ → ℕ
  2^ zero -1 = zero
  2^ (suc n) -1 = pow2 n nat+ (2^ n -1 )

  increment : ℕ → ℕ
  increment k = ((suc (suc zero)) nat* k) nat+ (suc zero)

  divide1 : (k r : ℕ) → pair< AbstractInterval , ℕ >
  divide1 k r = if (k ≤ r) then [ One , increment (k :natsub: r)] else [ Zero , increment r ]  -- represents 1/k with initial remainder r

  fullDivision : (k r : ℕ) → ((n : ℕ) → pair< AbstractInterval , ℕ >)
  fullDivision k r zero = divide1 k r
  fullDivision k r (suc n) = divide1 k (second (fullDivision k r n))

  remainder : ℕ → ℕ → ℕ → ℕ
  remainder k r n = second (fullDivision k r n)
  
  divValue : ℕ → ℕ → ℕ → AbstractInterval
  divValue k r n = first (fullDivision k r n)

  ft = 2^ (pow2 (suc (suc zero))) -1 -- 15

  divFt = divValue ft one -- n-th bit of 1/15 base 2

  -- Offset MUST be >= 2 (or 3)
  expOffset : ℕ
  expOffset = suc (suc (suc zero)) -- 3

  factorial : ℕ → ℕ
  factorial zero = suc zero
  factorial (suc k) = (suc k) nat* (factorial k)

  series : (x : AbstractInterval) → (ℕ → AbstractInterval)
  series x i = (pow x i) * (
               if ((suc i) ≤ expOffset)
               --then ((M (divValue ((pow2 expOffset) nat* (factorial i)) (2^ (suc i) -1))))
               then (divByPow (M (divValue (factorial i) one )) (expOffset :natsub: i))
               else ((M (divValue (factorial i) (2^ (suc i :natsub: expOffset) -1))))
               )

  e^_ : AbstractInterval → AbstractInterval
  e^ x = M (series x) -- actually 1/2^expOffset e^x, to keep the value bounded by One

  square : ℝ → ℝ
  square x = x × x

  squareIter : ℝ → ℕ → ℝ
  squareIter x zero = x
  squareIter x (suc n) = square (squareIter x n)

  exp : ℝ → ℝ
  exp < x , POS n > = squareIter < e^ x , POS expOffset > n
  exp < x , NEG n > = < e^ (divByPow x (suc n)) , POS expOffset >

  E = exp rOne
 
-- **************
-- *   Proofs   *
-- **************

-- +-------------+
-- | - (- x) ≡ x |
-- +-------------+

  realDoubleNeg : (t : ℝ) → - (- t) ≡ t
  realDoubleNeg < x , z > = doubleFcong <_,_> (doubleNegIdentityUse x) refl

-- +------------------+
-- | - x ≡ -rOne × x |
-- +------------------+

  realNegMulti : (t : ℝ) → - t ≡ (-rOne × t)
  realNegMulti < x , z > = doubleFcong <_,_> (negIsMultiplication x) refl

-- +-------------------+
-- | x × rZero ~ rZero |
-- +-------------------+

-- need : < 0 , x > ≡ < 0 , y > ∀ x,y 

  postulate realTimesZero : (t : ℝ) → (t × rZero) ≡ rZero
--  realTimesZero < x , z > = doubleFcong <_,_> (timesZero x) {!!}

-- +---------------+
-- | x + rZero ~ x |
-- +---------------+

  postulate realPlusZero : (t : ℝ) → (t + rZero) ≡ t
--  realPlusZero < x , z > = doubleFcong <_,_> {!!} {!!} 

-- +---------------+
-- | x × y ≡ y × x |
-- +---------------+

  postulate :+:comm : (z w : ℤ) → z :+: w ≡ w :+: z

  realMultiComm : (t s : ℝ) → (t × s) ≡ (s × t)
  realMultiComm < x , z > < y , w > =  doubleFcong <_,_> (multiComm x y) (:+:comm z w)

-- +-----------------------+
-- | x × (- y) ≡ - (x × y) |
-- +-----------------------+

  realShiftNeg : (t s : ℝ) → (t × (- s)) ≡ - (t × s)
  realShiftNeg < x , z > < y , w > = doubleFcong <_,_> (sym (shiftNeg x y)) refl

-- +--------------------------+
-- | (x × y) × z ≡ x × (y × z)|
-- +--------------------------+

  postulate :+:assoc : (z w k : ℤ) → (z :+: w) :+: k ≡ z :+: (w :+: k)

  realMultiAssoc : (α β γ : ℝ) → ((α × β) × γ) ≡ (α × (β × γ))
  realMultiAssoc < x , z > < y , w > < u , k > =
    doubleFcong <_,_> (multiAssoc x y u) (:+:assoc z w k)





{-
  posmaxSym : (k l : ℤ₊) → posmax k l First.≡ posmax l k
  posmaxSym k one = isTrue k :also: ?
  posmaxSym one l = {!!}
  posmaxSym (suc k) (suc l) = fcong suc (posmaxSym k l)

-}

--  postulate  maxSym : (k l : ℤ) → max k l ≡ max l k
--  maxSym {k} {l} = {!!}
{-

  aux~Sym : AbstractInterval → ℤ → ℤ → AbstractInterval
  aux~Sym x k = λ (t : ℤ) → divByPow x (toNat (t :-: k))

  aux1sym : {x y : AbstractInterval}{k l : ℤ} →
    divByPow x  (toNat (max k l :-: k)) ≡ divByPow y (toNat (max k l :-: l)) → divByPow y (toNat (max l k :-: l)) ≡ divByPow x (toNat (max l k :-: k))
  aux1sym {x} {y} {k} {l} proof =  ((fcong (aux~Sym y l)(maxSym k l)) :also: ? )
-}
--  ~sym : {z w : ℝ} → z ~ w → w ~ z
--  ~sym (equiv x y k l proof) = equiv y x l k {!!} -- ((fcong (aux~Sym y l)(maxSym k l)) :also: ? ) -- (First.sym proof :also: (fcong (aux~Sym x k) (maxSym k l))))


-- (First.sym ((fcong (aux~Sym x k) (maxSym k l)) :also:  proof) :also: (fcong (aux~Sym y l) (maxSym k l)))

--    rnO = ⟨ -One , zero ⟩
{-
  pow : (x : AbstractInterval) → (n : ℕ) → AbstractInterval
  pow x zero = One
  pow x (suc n) = x * (pow x n)

  factorial : (n : ℕ) → ℕ
  factorial zero = one
  factorial (suc n) = (factorial n) nat* (suc n)

  powerSeriesAI : (a : ℕ → AbstractInterval) → (x : AbstractInterval) → AbstractInterval
  powerSeriesAI a x = M (λ (n : ℕ) → (a n) * (pow x n))
-}
  times* : (x y : AbstractInterval) → AbstractInterval
  times* = aff -One

  sq* :  (x : AbstractInterval) → AbstractInterval
  sq* x = times* x x
