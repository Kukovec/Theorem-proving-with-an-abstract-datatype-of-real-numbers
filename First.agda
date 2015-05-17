module First where

  data ℕ : Set where
    zero : ℕ
    suc : ℕ → ℕ

-- constants for testing purposes
  one = suc zero
  four = suc(suc(suc(suc(zero))))

-- addition
  _nat+_ : ℕ → ℕ → ℕ
  zero nat+ m = m
  (suc n) nat+ m = suc (n nat+ m) -- [def (1)]
-- m(aff -x x -1, aff -x x 1) ≡ m (x -x)

-- multiplication defined through addition
  _nat*_ : ℕ → ℕ → ℕ
  zero nat* m = zero
  (suc n) nat* m = m nat+ (n nat* m)

-- equivalence operator, polymorphic for all members of Set subtypes
  infix 4 _≡_
  data _≡_ {A : Set}(m : A) : A → Set where
    refl : m ≡ m

-- symmetricity
  sym : {A : Set}{m n : A} → m ≡ n → n ≡ m
-- the reflexive relation x ≡ x is symetric
  sym refl = refl

-- transitivity
  trans : {A : Set}{m n p : A} → m ≡ n → n ≡ p → m ≡ p
-- given a reflexive first term (i.e. m is n) transitivity is self-implied
  trans refl eq = eq

-- congruence
  cong : {m n : ℕ} → m ≡ n → suc m ≡ suc n
-- if the lhs relation is reflexive, so is the rhs
  cong refl = refl
-- associativity
  +asoc : (m n p : ℕ) → (m nat+ n) nat+ p ≡ m nat+ (n nat+ p)
-- given m = zero, for any n and p associativity follows from reflexivity
  +asoc zero      _ _ = refl
-- in the general case, asociativity for suc m is equivalent to asociativity for m (induction on m).
  +asoc (suc m) n p = cong (+asoc m n p)

  -- proves m + zero = zero + m (= m)
  aux1 : (m : ℕ) → m nat+ zero ≡ m
  -- zero + zero = zero, which ≡ zero via reflexivity
  aux1 zero = refl
-- Induction. Given that aux1 holds for m it must hold for suc m, because of congruence. With regular notation, == representing ≡
{-
i)  0 + 0 = 0 == 0
ii) (suc a) + 0 == suc (a+0)  [(1)]
iii) a+0 == a ==> (suc a) + 0 == suc (a+0) == suc a
-}

  aux1 (suc m) = cong (aux1 m)

  aux2 : (m : ℕ) → m nat+ (suc zero) ≡ suc m
  aux2 zero = refl
  aux2 (suc m) = cong (aux2 m)

  _≡⟨_⟩_ : (x : ℕ) {y z : ℕ} → x ≡ y → y ≡ z → x ≡ z
  x ≡⟨ refl ⟩ refl = refl

  _∎ :(x : ℕ) → x ≡ x
  x ∎ = refl


 -- aux3 : {m n : ℕ} →  m ≡ n → m + (suc zero) ≡ n + (suc zero)
 -- aux3 refl = refl
 
 {- incomplete commutativity, induction on a

i) 0 + b == b + 0, proof in aux1
ii) (suc a) + b == suc (a + b)  [(1)]
iii) a + b == b + a [I.H.] ==> suc (a+b) == suc (b+a) [congruence]
iv) suc (b + a) == (suc b) + a [(1)]
v) suc b == b + suc 0 [aux2, TBD]
vi) (suc b) + a == (b + suc 0) + a == b + (suc 0 + a) [associativity]
vii) suc 0 + a == suc a [(1)] ==> (suc a) + b = b + (suc a)

-}


  iterCong : {m n : ℕ}(p : ℕ) → m ≡ n → m nat+ p ≡ n nat+ p
  iterCong _ refl = refl

  +comm : (m n : ℕ) → m nat+ n ≡ n nat+ m
  +comm zero n = sym (aux1 n)
-- I wrote it down, looks awful, but it wroks. 
  +comm (suc m) n = trans ( trans ( trans (trans (iterCong n (sym (aux2 m) )) (+asoc m one n)) (+comm m (suc n))) (iterCong m (sym (aux2 n))) ) (+asoc n one m)

{-
  max : ℕ → ℕ → ℕ
  max zero k = k
  max k zero = k
  max (suc l) (suc k) = suc (max k l)

  min : ℕ → ℕ → ℕ
  min zero k = zero
  min k zero = zero
  min (suc k) (suc l) = suc (min k l)
-}

