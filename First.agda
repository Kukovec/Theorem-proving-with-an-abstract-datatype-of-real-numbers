module First where

  data ℕ : Set where
    zero : ℕ
    suc : ℕ → ℕ

-- constants for testing purposes
  one = suc zero
  four = suc(suc(suc(suc(zero))))

-- addition
  _+_ : ℕ → ℕ → ℕ
  zero + m = m
  (suc n) + m = suc (n + m) -- [def (1)]

-- multiplication defined through addition
  _*_ : ℕ → ℕ → ℕ
  zero * m = zero
  (suc n) * m = m + (n * m)

-- equivalence operator
  infix 4 _≡_
  data _≡_ (m : ℕ) : ℕ → Set where
    refl : m ≡ m

-- symmetricity
  sym : {m n : ℕ} → m ≡ n → n ≡ m
-- the reflexive relation x ≡ x is symetric
  sym refl = refl

-- transitivity
  trans : {m n p : ℕ} → m ≡ n → n ≡ p → m ≡ p
-- given a reflexive first term (i.e. m is n) transitivity is self-implied
  trans refl n≡p = n≡p

-- congruence
  cong : {m n : ℕ} → m ≡ n → suc m ≡ suc n
-- if the lhs relation is reflexive, so is the rhs
  cong refl = refl
-- associativity
  +asoc : (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
-- given m = zero, for any n and p associativity follows from reflexivity
  +asoc zero      _ _ = refl
-- in the general case, asociativity for suc m is equivalent to asociativity for m (induction on m).
  +asoc (suc m) n p = cong (+asoc m n p)

  -- proves m + zero = zero + m (= m)
  aux1 : (m : ℕ) → m + zero ≡ m
  -- zero + zero = zero, which ≡ zero via reflexivity
  aux1 zero = refl
-- Induction. Given that aux1 holds for m it must hold for suc m, because of congruence. With regular notation, == representing ≡
{-
i)  0 + 0 = 0 == 0
ii) (suc a) + 0 == suc (a+0)  [(1)]
iii) a+0 == a ==> (suc a) + 0 == suc (a+0) == suc a
-}
  aux1 (suc m) = cong (aux1 m)
 
 {- incomplete commutativity, induction on a

i) 0 + b == b + 0, proof in aux1
ii) (suc a) + b == suc (a + b)  [(1)]
iii) a + b == b + a [I.H.] ==> suc (a+b) == suc (b+a) [congruence]
iv) suc (b + a) == (suc b) + a [(1)]
v) suc b == b + suc 0 [aux2, TBD]
vi) (suc b) + a == (b + suc 0) + a == b + (suc 0 + a) [associativity]
vii) suc 0 + a == suc a [aux3, TBD] ==> (suc a) + b = b + (suc a)



  +comm : (m n : ℕ) → m + n ≡ n + m
  +comm zero m = sym (aux1 m)
  +comm (suc n) m = cong (+comm n m)
 -}
