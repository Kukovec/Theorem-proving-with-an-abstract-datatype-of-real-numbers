import First

ℕ = First.ℕ
_≡_ = First._≡_ 

module Interval where

  data AbstractInterval : Set where
    One : AbstractInterval
    -One : AbstractInterval
    M : (ℕ → AbstractInterval) → AbstractInterval
    m : AbstractInterval → AbstractInterval → AbstractInterval
    aff : AbstractInterval → AbstractInterval → AbstractInterval → AbstractInterval
    dbl : AbstractInterval → AbstractInterval

  Zero = m -One One
  neg_ :  AbstractInterval → AbstractInterval
  neg x = aff One (-One) x

  _*_ : AbstractInterval → AbstractInterval → AbstractInterval
  x * y = aff (neg x) x y

