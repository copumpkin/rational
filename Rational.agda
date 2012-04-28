module Rational where

import Level
open import Function
open import Data.Sign as Sign using (Sign) renaming (_*_ to _S*_)
open import Data.Nat as ℕ renaming (_+_ to _ℕ+_; _*_ to _ℕ*_; _≤_ to _ℕ≤_; _<_ to _ℕ<_)
open import Data.Integer using (ℤ; +_; -[1+_]) renaming (_+_ to _ℤ+_; _*_ to _ℤ*_; -_ to ℤ-_; _◃_ to _ℤ◃_; ∣_∣ to ℤ∣_∣; _≤_ to _ℤ≤_)
import Data.Integer as ℤ
open import Data.Integer.Properties
open import Data.Nat.Coprimality hiding (sym)
open import Data.Nat.Divisibility
open import Data.Nat.GCD
open import Data.Nat.LCM
open import Data.Product

open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open import Rational.Nonnegative

-- This is old code and might not work. I've been focusing on Rational.Nonnegative and will move back here later

record ℚ : Set where
  constructor rat
  field
    numerator     : ℤ
    denominator-1 : ℕ
    .coprime      : Coprime ℤ∣ numerator ∣ (suc denominator-1)

  denominator : ℤ
  denominator = + suc denominator-1

record Lift (_≲_ : Rel ℤ Level.zero) (p q : ℚ) : Set where
  constructor lifted
  field
    pf : (ℚ.numerator p ℤ* ℚ.denominator q) ≲ (ℚ.numerator q ℤ* ℚ.denominator p)

_≤_ : Rel ℚ _
_≤_ = Lift _ℤ≤_

_<_ : Rel ℚ _
_<_ = Lift {!!}


sign : ℚ → Sign
sign (rat n d c) = ℤ.sign n


infixl 7 _÷_

_÷_ : (numerator : ℤ) (denominator : ℕ)
      {≢0 : False (ℕ._≟_ denominator 0)} →
      ℚ
(n ÷ zero) {≢0 = ()}
(n ÷ suc d) {c} with ℤ∣ n ∣ | suc d | gcd′ ℤ∣ n ∣ (suc d)
n ÷ suc d | .(q₁ ℕ* g) | .(q₂ ℕ* g) | g , gcd-* q₁ q₂ c = rat (ℤ.sign n ℤ◃ q₁) (pred q₂) {!!}


_◃_ : Sign → ℚ⁺ → ℚ
s ◃ rat⁺ n d c = rat (s ℤ◃ n) d (λ { {i} (p , q) → c (subst (_∣_ i) (abs-◃ s n) p , q) })

∣_∣ : ℚ → ℚ⁺
∣ rat n d c ∣ = rat⁺ ℤ∣ n ∣ d c

◃-left-inverse : ∀ q → sign q ◃ ∣ q ∣ ≡ q
◃-left-inverse (rat -[1+ n ]  d c) = refl
◃-left-inverse (rat (+ zero)  d c) = refl
◃-left-inverse (rat (+ suc n) d c) = refl

data SignAbs : ℚ → Set where
  _◂_ : (s : Sign) (q : ℚ⁺) → SignAbs (s ◃ q)

signAbs : ∀ q → SignAbs q
signAbs q = subst SignAbs (◃-left-inverse q) (sign q ◂ ∣ q ∣)

0# : ℚ
0# = rat (+ 0) 0 (∣1⇒≡1 ∘ proj₂)

1# : ℚ
1# = rat (+ 1) 0 (1-coprimeTo 1)



negate : ℚ → ℚ
negate q with signAbs q
negate ._ | s ◂ q⁺ = Sign.opposite s ◃ q⁺

negate-involution : ∀ q → negate (negate q) ≡ q
negate-involution (rat -[1+ n ]  d c) = refl
negate-involution (rat (+ zero)  d c) = refl
negate-involution (rat (+ suc n) d c) = refl

invert : ℚ → ℚ
invert (rat -[1+ n ]  d c) = rat -[1+ d ] n (λ { (x , y) → c (y , x) })
invert (rat (+ zero)  d c) = rat (+ zero) d c
invert (rat (+ suc n) d c) = rat (+ suc d) n λ { (x , y) → c (y , x) }

⁻invert-involution : ∀ q → invert (invert q) ≡ q
⁻invert-involution (rat -[1+ n ]  d c) = refl
⁻invert-involution (rat (+ zero)  d c) = refl
⁻invert-involution (rat (+ suc n) d c) = refl


_+_ : ℚ → ℚ → ℚ
rat n d c + rat n′ d′ c′ with lcm (suc d) (suc d′)
rat n d c + rat n′ d′ c′ | l , LCM.is (divides q eq , divides q′ eq′) least = rat ((+ q ℤ* n) ℤ+ (+ q′ ℤ* n′)) (pred l) (λ {i} → coprime {i})
  where
  .coprime : Coprime ℤ∣ (+ q ℤ* n) ℤ+ (+ q′ ℤ* n′) ∣ (suc (pred l))
  coprime {i} (div₁ , div₂) = {!!}



_*_ : ℚ → ℚ → ℚ
p * q with signAbs p | signAbs q
._ * ._ | sp ◂ p⁺ | sq ◂ q⁺ = (sp S* sq) ◃ (p⁺ *⁺ q⁺)
  where
  _*⁺_ : ℚ⁺ → ℚ⁺ → ℚ⁺
  rat⁺ n d c *⁺ rat⁺ n′ d′ c′ with gcd n (suc d′) | gcd n′ (suc d)
  rat⁺ n d c *⁺ rat⁺ n′ d′ c′ | g , GCD.is (g∣n , g∣1+d′) gr | g′ , GCD.is (g′∣n′ , g′∣1+d) gr′
    = rat⁺ (quotient g∣n ℕ* quotient g′∣n′) (pred (quotient g∣1+d′ ℕ* quotient g′∣1+d)) λ { (p , q) → {!!} }


x = + 5 ÷ 7
y = + 8 ÷ 3

test = x * y






{-

  _*⁺_ : ℚ⁺ → ℚ⁺ → ℚ⁺ 
  rat⁺ n d c *⁺ rat⁺ n′ d′ c′ with suc d | inspect suc d | suc d′ | inspect suc d′
  rat⁺ n d c *⁺ rat⁺ n′ d′ c′ | sd | [ psd ] | sd′ | [ psd′ ] with gcd′ n sd′ | gcd′ n′ sd
  rat⁺ .(q₁ ℕ* g) d c *⁺ rat⁺ .(q₃ ℕ* g′) d′ c′ | .(q₄ ℕ* g′) | [ psd ] | .(q₂ ℕ* g) | [ psd′ ] | g , gcd-* q₁ q₂ c₁ | g′ , gcd-* q₃ q₄ c₂
    = rat⁺ (q₁ ℕ* q₃) (pred (q₂ ℕ* q₄)) {!!}




{-
Goal : Coprime (q₁ ℕ* q₃) (suc (pred (q₂ ℕ* q₄)))

c   : Coprime (q₁ ℕ* g) (q₄ ℕ* g′)
c′  : Coprime (q₃ ℕ* g′) (q₂ ℕ* g)
c₁  : Coprime q₁ q₂
c₂  : Coprime q₃ q₄
-}

{-
  rat⁺ n d c *⁺ rat⁺ n′ d′ c′ with gcd n (suc d′) | gcd n′ (suc d)
  rat⁺ n d c *⁺ rat⁺ n′ d′ c′ | g , GCD.is (g∣n , g∣1+d′) gr | g′ , GCD.is (g′∣n′ , g′∣1+d) gr′
    = rat⁺ (quotient g∣n ℕ* quotient g′∣n′) (pred (quotient g′∣n′ ℕ* quotient g′∣1+d)) λ { (p , q) → {!!} }
--    where
--    coprime : Coprime (quotient g∣n ℕ* quotient g′∣n) (suc (pred (quotient g′∣n′ ℕ* quotient g′∣1+d)))
--    coprime = ?
-}
-}