{-# OPTIONS --cubical #-}
module HornPrelude where

open import Agda.Primitive public
open import Agda.Primitive.Cubical public
  renaming (primINeg to ~_; primIMax to _∨_; primIMin to _∧_)
open import Agda.Builtin.Cubical.Path public
open import Agda.Builtin.Cubical.Glue public
open import Agda.Builtin.Cubical.Sub public renaming (Sub to _[_↦_]; primSubOut to outS)
open import Agda.Builtin.Sigma public
open import Agda.Builtin.Nat public using (zero; suc) renaming (Nat to ℕ)
open import Agda.Builtin.Bool public using (true; false) renaming (Bool to 𝔹)

ann : ∀ {ℓ} (A : Set ℓ) → A → A
ann A t = t

natrec : ∀ {ℓ} (P : ℕ → Set ℓ) → P zero → ((n : ℕ) → P n → P (suc n)) → (n : ℕ) → P n
natrec P z f zero = z
natrec P z f (suc n) = f n (natrec P z f n)

bif : ∀ {ℓ} (P : 𝔹 → Set ℓ) → P true → P false → (b : 𝔹) → P b
bif P t f true = t
bif P t f false = f

data S¹ : Set where
  base : S¹
  loop : base ≡ base

s1rec : ∀ {ℓ} (A : Set ℓ) (b : A) → b ≡ b → S¹ → A
s1rec A b l base = b
s1rec A b l (loop i) = l i

-- Horn states equivalences as plain Σ-types; Agda's Glue wants its record.
mkEquiv : ∀ {ℓ ℓ'} {T : Set ℓ} {A : Set ℓ'}
  → Σ (T → A) (λ f → (y : A) → Σ (Σ T (λ x → f x ≡ y)) (λ c → (w : Σ T (λ x → f x ≡ y)) → c ≡ w))
  → T ≃ A
mkEquiv e = fst e , record { equiv-proof = snd e }

-- Horn's compositions live in one universe; a constant level keeps Agda's
-- level metavariable a pattern.
compC : ∀ {ℓ} (A : I → Set ℓ) {φ : I} (u : ∀ i → Partial φ (A i)) (a : A i0 [ φ ↦ u i0 ]) → A i1
compC A u a = primComp A u (outS a)

transpC : ∀ {ℓ} (A : I → Set ℓ) (a : A i0) → A i1
transpC A a = primTransp A i0 a

-- Glue at a single level, so that Agda's level metavariables stay solvable.
GlueC : ∀ {ℓ} (A : Set ℓ) {φ : I} (T : Partial φ (Set ℓ)) (e : PartialP φ (λ o → T o ≃ A)) → Set ℓ
GlueC A T e = primGlue A T e

glueC : ∀ {ℓ} {A : Set ℓ} {φ : I} {T : Partial φ (Set ℓ)} {e : PartialP φ (λ o → T o ≃ A)}
  → (t : PartialP φ T) → A [ φ ↦ (λ o → fst (e o) (t o)) ] → GlueC A T e
glueC {A = A} {φ = φ} {T = T} {e = e} t a = prim^glue {A = A} {φ = φ} {T = T} {e = e} t (outS a)
