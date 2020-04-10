module eins-minus-null where

{-
followed

* https://plfa.github.io/Naturals/
* https://plfa.github.io/Induction/

for the majority of the proofs
-}

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)

-- recursive definition of set of naturals
data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

-- definition of addition
_+_ : ℕ → ℕ → ℕ
zero     + m = m
(succ n) + m = succ (n + m)

-- definition of 'monus'  -  bounded subtraction
_-_ : ℕ → ℕ → ℕ
n        - zero     = n
zero     - m        = zero
(succ n) - (succ m) = n - m


-- lemma needed for proof of commutativity
+-identity : ∀ (n : ℕ) → n + zero ≡ n
-- base case
+-identity zero =
  begin
    zero + zero
  ≡⟨⟩
    zero
  ∎
-- inductive case
+-identity (succ m) =
  begin
    (succ m) + zero
  ≡⟨⟩
    succ (m + zero)
  -- succ is a congruence for +-identity
  ≡⟨ cong succ (+-identity m) ⟩
    succ m
  ∎

-- another lemma needed for proof of commutativity
+-succ : ∀ (n m : ℕ) → n + succ m ≡ succ (n + m)
-- base case
+-succ zero m =
  begin
    zero + succ m
  ≡⟨⟩
    succ m
  ≡⟨⟩
    succ (zero + m)
  ∎
-- inductive case
+-succ (succ n) m =
  begin
    succ n + succ m
  ≡⟨⟩
    succ (n + succ m)
  ≡⟨ cong succ (+-succ n m) ⟩
    succ (succ (n + m))
  ≡⟨⟩
    succ (succ n + m)
  ∎

-- addition is commutative; proof is needed for main theorem
+-commutativity : ∀ (m n : ℕ) → m + n ≡ n + m
-- base case
+-commutativity m zero =
  begin
    m + zero
  -- use previous lemma
  ≡⟨ +-identity m ⟩
    m
  ≡⟨⟩
    zero + m
  ∎
-- inductive case
+-commutativity m (succ n) =
  begin
    m + (succ n)
  ≡⟨ +-succ m n ⟩
    succ (m + n)
  ≡⟨ cong succ (+-commutativity m n) ⟩
    succ (n + m)
  ≡⟨⟩
    (succ n) + m
  ∎


-- proof of the main theorem
one : ℕ
one = succ zero

main-theorem : (one - zero) ≡ (one + zero)
main-theorem =
  begin
    one - zero
  ≡⟨⟩
    one
  ≡⟨⟩
    zero + one
  ≡⟨ +-commutativity zero one ⟩
    one + zero
  ∎
