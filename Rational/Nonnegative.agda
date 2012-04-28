module Rational.Nonnegative where

open import Function

open import Data.Empty
open import Data.Unit using (hide)
open import Data.Nat as ℕ
open import Data.Nat.Divisibility
open import Data.Nat.Coprimality as Coprimality
open import Data.Nat.GCD
open import Data.Nat.LCM
open import Data.Nat.Properties
open import Data.Product

open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PropEq
import Relation.Binary.EqReasoning as EqReasoning

open import Algebra.Structures
open SemiringSolver
module P = Poset poset

postulate
  .irrAxiom : ∀ {a} {A : Set a} → .A → A
{-# BUILTIN IRRAXIOM irrAxiom #-}

relevant : ∀ {a} {A : Set a} {i j : A} → .(i ≡ j) → i ≡ j
relevant pf = trustMe -- should be safe here, see https://lists.chalmers.se/pipermail/agda/2011/003206.html
  where open import Relation.Binary.PropositionalEquality.TrustMe


-- infixl 7 _*⁺_
-- infixl 6 _+⁺_
-- infix  4 _≤⁺_ -- _≤?_


module ℕ-csr = IsCommutativeSemiring isCommutativeSemiring 

record ℚ⁺ : Set where
  constructor rat⁺
  field
    numerator     : ℕ
    denominator-1 : ℕ

  denominator : ℕ
  denominator = suc denominator-1

  field
    .coprime      : Coprime numerator denominator

open ℚ⁺

record Lift⁺ {ℓ} (_≲_ : Rel ℕ ℓ) (p q : ℚ⁺) : Set ℓ where
  constructor lifted⁺
  field
    pf : (numerator p * denominator q) ≲ (numerator q * denominator p)

_≤⁺_ : Rel ℚ⁺ _
_≤⁺_ = Lift⁺ _≤_

_<⁺_ : Rel ℚ⁺ _
_<⁺_ = Lift⁺ _<_


_÷⁺_ : (numerator : ℕ) (denominator : ℕ)
      {≢0 : False (ℕ._≟_ denominator 0)} →
      ℚ⁺
(n  ÷⁺ d ) with gcd′ n d
(._ ÷⁺ ._) {} | g , gcd-* q₁ zero c
(._ ÷⁺ ._)    | g , gcd-* q₁ (suc q₂) c = rat⁺ q₁ q₂ c

.÷⁺-universal : ∀ q → numerator q ÷⁺ denominator q ≡ q
÷⁺-universal (rat⁺ n d c) = helper n d c (suc d) refl
  where
  lemma : ∀ {n m} → n ≡ suc m → False (ℕ._≟_ n 0)
  lemma refl = _

  helper : ∀ n d .(c : Coprime n (suc d)) k (eq : k ≡ suc d) → (n ÷⁺ k) {lemma eq} ≡ rat⁺ n d c
  helper n  d c k  eq with gcd′ n k
  helper n  d c k  eq | g  , gcd with GCD.unique (subst (λ q → GCD n q g) eq (gcd′-gcd gcd)) (coprime-gcd (irrAxiom c)) | gcd
  helper ._ d c ._ () | g  , gcd | _    | gcd-* q₁ zero c′
  helper ._ d c ._ eq | .1 , gcd | refl | gcd-* q₁ (suc q₂) c′ rewrite proj₂ ℕ-csr.*-identity q₁ | proj₂ ℕ-csr.*-identity q₂ | cong pred eq = refl


0#⁺ : ℚ⁺
0#⁺ = rat⁺ 0 0 (∣1⇒≡1 ∘ proj₂)

1#⁺ : ℚ⁺
1#⁺ = rat⁺ 1 0 (1-coprimeTo 1)

-- These belong in another file, possibly in the standard library modules they're proving things about
module Lemmas where

  ∣⇒GCD : ∀ {x y} → x ∣ y → GCD x y x
  ∣⇒GCD d = GCD.is (P.refl , d) proj₁

  LCM-id : ∀ a → LCM 1 a a
  LCM-id a = LCM.is (1∣ a , P.refl) proj₂

  LCM-sym : ∀ {a b c} → LCM a b c → LCM b a c
  LCM-sym (LCM.is p l) = LCM.is (swap p) (l ∘ swap)

  LCM-symˡ : ∀ {a b c} (l₁ : LCM (suc a) b c) (l₂ : LCM b (suc a) c) → quotient (proj₁ (LCM.commonMultiple l₁)) ≡ quotient (proj₂ (LCM.commonMultiple l₂))
  LCM-symˡ (LCM.is (divides q₁ eq₁ , _) least₁) (LCM.is (_ , divides q₄ eq₄) least₂) = cancel-*-right q₁ q₄ (trans (PropEq.sym eq₁) eq₄)

  private
    shuffle : ∀ x y z → x * (y * z) ≡ y * (x * z)
    shuffle = solve 3 (λ x y z → x :* (y :* z) := y :* (x :* z)) refl

  *-GCD-distrib : ∀ x {g y z} → GCD y z g → GCD (x * y) (x * z) (x * g)
  *-GCD-distrib x gcd with gcd-gcd′ gcd
  *-GCD-distrib x {g} gcd | gcd-* q₁ q₂ c rewrite shuffle x q₁ g | shuffle x q₂ g = gcd′-gcd (gcd-* q₁ q₂ c)

  ∣-*-GCD : ∀ {ga a b n gb} → GCD n a ga → GCD n b gb → n ∣ a * b → n ∣ ga * gb
  ∣-*-GCD {ga} {a} {b} g₁ g₂ n∣a*b with *-GCD-distrib ga g₂ | *-GCD-distrib b g₁
  ∣-*-GCD {ga} {a} {b} g₁ g₂ n∣a*b | GCD.is _ gr | GCD.is _ gr′ rewrite ℕ-csr.*-comm ga b | ℕ-csr.*-comm a b = gr (∣-* ga , gr′ (∣-* b , n∣a*b))

  Coprime-* : ∀ a b c → Coprime c a → Coprime c b → Coprime c (a * b)
  Coprime-* a b c cca ccb {n} (n∣c , n∣a*b) with gcd n a | gcd n b
  Coprime-* a b c cca ccb {n} (n∣c , n∣a*b) | g₁ , gcd₁ | g₂ , gcd₂ 
    = ∣1⇒≡1 (∣-*-GCD (subst (GCD n a) (cca (P.trans (proj₁ (GCD.commonDivisor gcd₁)) n∣c , proj₂ (GCD.commonDivisor gcd₁))) gcd₁) 
                    (subst (GCD n b) (ccb (P.trans (proj₁ (GCD.commonDivisor gcd₂)) n∣c , proj₂ (GCD.commonDivisor gcd₂))) gcd₂) n∣a*b)

  ∣-*′ : ∀ k {n} → n ∣ n * k
  ∣-*′ k {n} rewrite ℕ-csr.*-comm n k = ∣-* k

  suc≢0 : ∀ {n} → suc n ≢ 0
  suc≢0 ()

open Lemmas

-- The straightforward approach
_+⁺′_ : ℚ⁺ → ℚ⁺ → ℚ⁺
rat⁺ n d c +⁺′ rat⁺ n′ d′ c′ = (n * suc d′ + suc d * n′) ÷⁺ (suc d * suc d′)

_+⁺_ : ℚ⁺ → ℚ⁺ → ℚ⁺
rat⁺ n d c +⁺ rat⁺ n′ d′ c′ with lcm (suc d) (suc d′)
rat⁺ n d c +⁺ rat⁺ n′ d′ c′ | zero  , LCM.is _ least = ⊥-elim (suc≢0 (0∣⇒≡0 (least {suc d * suc d′} (∣-*′ (suc d′) , ∣-* (suc d)))))
rat⁺ n d c +⁺ rat⁺ n′ d′ c′ | suc l , LCM.is (divides q _ , divides q′ _) _ = (n * q + n′ * q′) ÷⁺ suc l

+⁺-equiv : ∀ p q → p +⁺ q ≡ p +⁺′ q
+⁺-equiv (rat⁺ n d c) (rat⁺ n′ d′ c′) = helper c c′ refl refl (gcd′ (n * suc d′ + suc d * n′) (suc d * suc d′)) refl (lcm (suc d) (suc d′)) refl
  where
  helper : ∀ {n d} .(c : Coprime n (suc d)) {n′ d′} .(c′ : Coprime n′ (suc d′)) {p q} (eq₁ : p ≡ n * suc d′ + suc d * n′) (eq₂ : q ≡ suc d * suc d′)
         → (g : ∃ (GCD′ p q)) → g ≡ gcd′ p q → (l : ∃ (LCM (suc d) (suc d′))) → l ≡ lcm (suc d) (suc d′)
         → rat⁺ n d c +⁺ rat⁺ n′ d′ c′ ≡ rat⁺ n d c +⁺′ rat⁺ n′ d′ c′
  helper c c′ eq₁ eq₂ (g , gcd) geq (l , lcm) leq = {!geq!}

-- (n * q + n′ * q′) ÷⁺ suc l
-- (n * suc d′ + suc d * n′) ÷⁺ (suc d * suc d′)
{-
lemma : ∀ a b → 1 + a ≡ b * (1 + a) → b ≡ 1
lemma a b eq = PropEq.sym (cancel-*-right 1 b (PropEq.trans (proj₁ ℕ-csr.*-identity (1 + a)) eq))
-}
{-
+⁺-comm : ∀ p q → p +⁺ q ≡ q +⁺ p
+⁺-comm (rat⁺ n d c) (rat⁺ n′ d′ c′) with lcm (suc d) (suc d′) | lcm (suc d′) (suc d) -- ideally I wouldn't bother doing the LCM twice, but this is easier
+⁺-comm (rat⁺ n d c) (rat⁺ n′ d′ c′) | l₁ , lcm₁ |  l₂ , lcm₂ with LCM.unique lcm₁ (LCM-sym lcm₂)
+⁺-comm (rat⁺ n d c) (rat⁺ n′ d′ c′) | zero , LCM.is _ least₁ | ._ , LCM.is _ least₂ | refl = ⊥-elim (suc≢0 (0∣⇒≡0 (least₁ {suc d * suc d′} (∣-*′ (suc d′) , ∣-* (suc d)))))
+⁺-comm (rat⁺ n d c) (rat⁺ n′ d′ c′) | (suc l₁) , LCM.is (divides q₁ eq₁ , divides q₂ eq₂) least₁ | ._ , LCM.is (divides q₃ eq₃ , divides q₄ eq₄) least₂ | refl =
  begin
    (n * q₁ + n′ * q₂) ÷⁺ suc l₁
  ≡⟨ cong (λ q → q ÷⁺ suc l₁) (ℕ-csr.+-comm (n * q₁) (n′ * q₂)) ⟩
    (n′ * q₂ + n * q₁) ÷⁺ suc l₁
  ≡⟨ cong (λ q → (n′ * q + n * q₁) ÷⁺ suc l₁) (PropEq.sym (LCM-symˡ (LCM.is (divides q₃ eq₃ , divides q₄ eq₄) least₂) (LCM.is (divides q₁ eq₁ , divides q₂ eq₂) least₁))) ⟩
    (n′ * q₃ + n * q₁) ÷⁺ suc l₁
  ≡⟨ cong (λ q → (n′ * q₃ + n * q) ÷⁺ suc l₁) (LCM-symˡ (LCM.is (divides q₁ eq₁ , divides q₂ eq₂) least₁) (LCM.is (divides q₃ eq₃ , divides q₄ eq₄) least₂)) ⟩
    (n′ * q₃ + n * q₄) ÷⁺ suc l₁
  ∎
  where open EqReasoning (setoid ℚ⁺)
-}

{-
+⁺-assoc : ∀ p q r → (p +⁺ q) +⁺ r ≡ p +⁺ (q +⁺ r)
+⁺-assoc (rat⁺ n d c) (rat⁺ n′ d′ c′) (rat⁺ n′′ d′′ c′′) = {!!} 
-}
{-
with lcm (suc d) (suc d′) | lcm (suc d′) (suc d′′)
+⁺-assoc (rat⁺ n d c) (rat⁺ n′ d′ c′) (rat⁺ n′′ d′′ c′′) | l₁ , lcm₁ | l₂ , lcm₂ = ?
-}
{-
+⁺-idˡ : ∀ q → 0#⁺ +⁺ q ≡ q
+⁺-idˡ (rat⁺ n d c) with lcm 1 (suc d)
+⁺-idˡ (rat⁺ n d c) | zero  , LCM.is _ least = ⊥-elim (suc≢0 (0∣⇒≡0 (least (∣-*′ (suc d) , ∣-* 1))))
+⁺-idˡ (rat⁺ n d c) | suc l , q with LCM.unique q (LCM-id (suc d))
+⁺-idˡ (rat⁺ n d c) | suc l , LCM.is (divides q₁ eq₁ , divides q₂ eq₂) least | eq =
  begin
    (n * q₂) ÷⁺ suc l
  ≡⟨ cong (λ q → (n * q) ÷⁺ suc l) (lemma d q₂ (trans (PropEq.sym eq) eq₂)) ⟩
    (n * 1) ÷⁺ suc l  
  ≡⟨ cong (λ q → q ÷⁺ suc l) (proj₂ ℕ-csr.*-identity n) ⟩
    n ÷⁺ suc l
  ≡⟨ cong (λ q → n ÷⁺ suc q) (cong pred eq) ⟩
    n ÷⁺ suc d
  ≡⟨ ÷⁺-universal (rat⁺ n d c) ⟩
    rat⁺ n d c
  ∎
  where open EqReasoning (setoid ℚ⁺)

+⁺-idʳ : ∀ q → q +⁺ 0#⁺ ≡ q
+⁺-idʳ (rat⁺ n d c) with lcm (suc d) 1
+⁺-idʳ (rat⁺ n d c) | zero  , LCM.is _ least = ⊥-elim (suc≢0 (0∣⇒≡0 (least (∣-* 1 , ∣-*′ (suc d)))))
+⁺-idʳ (rat⁺ n d c) | suc l , q with LCM.unique q (LCM-sym (LCM-id (suc d)))
+⁺-idʳ (rat⁺ n d c) | suc l , LCM.is (divides q₁ eq₁ , divides q₂ eq₂) least | eq =
  begin
    (n * q₁ + 0 * q₂) ÷⁺ suc l
  ≈⟨ cong (λ q → (n * q + 0 * q₂) ÷⁺ suc l) (lemma d q₁ (trans (PropEq.sym eq) eq₁)) ⟩
    (n * 1 + 0 * q₂) ÷⁺ suc l
  ≡⟨ refl ⟩
    (n * 1 + 0) ÷⁺ suc l
  ≡⟨ cong (λ q → q ÷⁺ suc l) (solve 1 (λ n → n :* con 1 :+ con 0 := n) refl n) ⟩
    n ÷⁺ suc l
  ≈⟨ cong (λ q → n ÷⁺ suc q) (cong pred eq) ⟩
    n ÷⁺ suc d
  ≈⟨ ÷⁺-universal (rat⁺ n d c) ⟩
    rat⁺ n d c
  ∎
  where open EqReasoning (setoid ℚ⁺)
-}


{-
_*⁺′_ : ℚ⁺ → ℚ⁺ → ℚ⁺
rat⁺ n d c *⁺′ rat⁺ n′ d′ c′ = (n * n′) ÷⁺ (suc d * suc d′)

x*y≢0⇒x≢0 : ∀ x {y} → x * y ≢ 0 → x ≢ 0
x*y≢0⇒x≢0 zero pf = pf
x*y≢0⇒x≢0 (suc x) {zero}  pf = λ ()
x*y≢0⇒x≢0 (suc x) {suc y} pf = λ ()

x≢0⇒y≢0⇒x*y≢0 : ∀ {x y} → x ≢ 0 → y ≢ 0 → x * y ≢ 0
x≢0⇒y≢0⇒x*y≢0 {zero} pf₁ pf₂ = pf₁
x≢0⇒y≢0⇒x*y≢0 {suc x} {zero}  pf₁ pf₂ = λ _ → pf₂ refl
x≢0⇒y≢0⇒x*y≢0 {suc x} {suc y} pf₁ pf₂ = λ ()


_*⁺_ : ℚ⁺ → ℚ⁺ → ℚ⁺
rat⁺ n d c *⁺ rat⁺ n′ d′ c′ = helper c c′ (λ ()) (λ ()) (gcd′ n (suc d′)) (gcd′ n′ (suc d))
  module *⁺ where
  helper : ∀ {n d n′ d′} .(c : Coprime n d) .(c′ : Coprime n′ d′) → d ≢ 0 → d′ ≢ 0 → ∃ (GCD′ n d′) → ∃ (GCD′ n′ d) → ℚ⁺
  helper c₁ c₂ d≢0 d′≢0 (g , gcd-* q₁ q₂ c₃) (g′ , gcd-* q₃ q₄ c₄) with q₂ * q₄ | inspect (_*_ q₂) q₄
  helper c₁ c₂ d≢0 d′≢0 (g , gcd-* q₁ q₂ c₃) (g′ , gcd-* q₃ q₄ c₄) | zero  | [ eq ] = ⊥-elim (x≢0⇒y≢0⇒x*y≢0 (x*y≢0⇒x≢0 q₂ d′≢0) (x*y≢0⇒x≢0 q₄ d≢0) eq)
  helper c₁ c₂ d≢0 d′≢0 (g , gcd-* q₁ q₂ c₃) (g′ , gcd-* q₃ q₄ c₄) | suc p | [ eq ]
      = rat⁺ (q₁ * q₃) p (subst (Coprime (q₁ * q₃)) eq proof)
    where
    .proof : Coprime (q₁ * q₃) (q₂ * q₄)
    proof
      = Coprime-* q₂ q₄ (q₁ * q₃)
          (Coprimality.sym (Coprime-* q₁ q₃ q₂ (Coprimality.sym c₃) (λ { (l , r) → c₂ (P.trans r (∣-*′ g′) , P.trans l (∣-*′ g)) }))) 
          (Coprimality.sym (Coprime-* q₁ q₃ q₄ (λ { (l , r) → c₁ (P.trans r (∣-*′ g) , P.trans l (∣-*′ g′)) }) (Coprimality.sym c₄)))
-}

{-

+⁺≡+⁺′ : ∀ x y → x +⁺ y ≡ x +⁺′ y
+⁺≡+⁺′ x y = {!!}
-}

{-



-}


{-
invert : ℚ⁺ → ℚ⁺
invert (rat⁺ zero d c) = rat⁺ zero d c
invert (rat⁺ (suc n) d c) = rat⁺ (suc d) n λ { (div₁ , div₂) → c (div₂ , div₁) }

⁻invert-involution : ∀ q → invert (invert q) ≡ q
⁻invert-involution (rat⁺ zero d c) = refl
⁻invert-involution (rat⁺ (suc n) d c) = refl
-}
{-
_*⁺_ : ℚ⁺ → ℚ⁺ → ℚ⁺ 
rat⁺ n d c *⁺ rat⁺ n′ d′ c′ with suc d | inspect suc d | suc d′ | inspect suc d′
rat⁺ n d c *⁺ rat⁺ n′ d′ c′ | sd | [ psd ] | sd′ | [ psd′ ] with gcd′ n sd′ | gcd′ n′ sd
rat⁺ .(q₁ * g) d c *⁺ rat⁺ .(q₃ * g′) d′ c′ | .(q₄ * g′) | [ psd ] | .(q₂ * g) | [ psd′ ] | g , gcd-* q₁ q₂ c₁ | g′ , gcd-* q₃ q₄ c₂
  = rat⁺ (q₁ * q₃) (pred (q₂ * q₄)) {!!}
-}
{-
_*⁺_ : ℚ⁺ → ℚ⁺ → ℚ⁺
rat⁺ n d c *⁺ rat⁺ n′ d′ c′ with gcd n (suc d′) | gcd n′ (suc d)
rat⁺ n d c *⁺ rat⁺ n′ d′ c′ | g , GCD.is (g∣n , g∣1+d′) gr | g′ , GCD.is (g′∣n′ , g′∣1+d) gr′
  = rat⁺ (quotient g∣n ℕ* quotient g′∣n′) (pred (quotient g∣1+d′ ℕ* quotient g′∣1+d)) {!!}
-}
