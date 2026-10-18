{-# OPTIONS --safe --without-K #-}
------------------------------------------------------------------------
-- The unification algorithm of src/schematic.rs, and proofs that it
-- provides what Implication.agda assumes of it.
--
-- `invert` in Implication.agda takes each case at a unifier θ of the
-- hypothesis and a rule's conclusion with
--
--   IsMGU θ s t : every unifier ρ of s and t factors through θ
--                 (ρ x ≡ ρ(θ x)), and θ keeps sorts;
--   NoUnifier s t : no ρ unifies s and t, for a rule that drops out.
--
-- `mgu` below is Robinson's algorithm as the Rust checker runs it: a stack
-- of pairs, each taken under the substitution so far; equal terms are
-- dropped, a variable on the left is bound first, then one on the right,
-- after an occurs check; equal heads push their argument pairs, the last on
-- top. Binding x to u composes [x := u] after θ. The case judgments the
-- checker compares depend on exactly which unifier comes out, so the order
-- matters even though every result is most general.
--
-- The algorithm takes fuel to be structurally recursive; running out is a
-- third outcome, `stuck`, which a checker rejects. `mgu-sound` and
-- `mgu-none` hold for any fuel.
------------------------------------------------------------------------
module Unify where

open import Schematic
open import Implication
open Σ

------------------------------------------------------------------------
-- The algorithm

data Outcome : Set where
  ok    : Subst → Outcome
  none  : Outcome
  stuck : Outcome

-- [x := u]
single : ℕ → Tm → Subst
single x u y with y ≟ x
... | yes _ = u
... | no _  = var y

mutual
  occ? : (x : ℕ) (t : Tm) → Dec (Occ x t)
  occ? x (var y) with x ≟ y
  ... | yes refl = yes here
  ... | no ne    = no (λ o → ne (occ-var o))
  occ? x (node f ts) with occs? x ts
  ... | yes o = yes (arg o)
  ... | no nu = no (λ { (arg o) → nu o })

  occs? : (x : ℕ) (ts : List Tm) → Dec (Occs x ts)
  occs? x []       = no (λ ())
  occs? x (t ∷ ts) with occ? x t | occs? x ts
  ... | yes o | _     = yes (hd o)
  ... | no _  | yes o = yes (tl o)
  ... | no n₁ | no n₂ = no (λ { (hd o) → n₁ o ; (tl o) → n₂ o })

-- Push the argument pairs, the last on top; `nothing` for different
-- lengths.
push : List Tm → List Tm → List (Tm × Tm) → Maybe (List (Tm × Tm))
push []       []       w = just w
push (s ∷ ss) (t ∷ ts) w = push ss ts ((s , t) ∷ w)
push []       (_ ∷ _)  w = nothing
push (_ ∷ _)  []       w = nothing

mutual
  unify : ℕ → Subst → List (Tm × Tm) → Outcome
  unify zero    θ w             = stuck
  unify (suc n) θ []            = ok θ
  unify (suc n) θ ((a , b) ∷ w) = turn n θ w (sub θ a) (sub θ b)

  turn : ℕ → Subst → List (Tm × Tm) → Tm → Tm → Outcome
  turn n θ w s t with s ≟ₜ t
  ... | yes _ = unify n θ w
  ... | no _  = orient n θ w s t

  orient : ℕ → Subst → List (Tm × Tm) → Tm → Tm → Outcome
  orient n θ w (var x)     t           = bind n θ w x t
  orient n θ w (node f ss) (var y)     = bind n θ w y (node f ss)
  orient n θ w (node f ss) (node g ts) with f ≟ g
  ... | no _  = none
  ... | yes _ with push ss ts w
  ...   | nothing = none
  ...   | just w′ = unify n θ w′

  bind : ℕ → Subst → List (Tm × Tm) → ℕ → Tm → Outcome
  bind n θ w x u with occ? x u
  ... | yes _ = none
  ... | no _  = unify n (single x u ∘ˢ θ) w

mgu : ℕ → Tm → Tm → Outcome
mgu n s t = unify n var ((s , t) ∷ [])

------------------------------------------------------------------------
-- Sizes: a variable cannot equal a term that properly contains it

data _≤_ : ℕ → ℕ → Set where
  z≤n : {n : ℕ} → zero ≤ n
  s≤s : {m n : ℕ} → m ≤ n → suc m ≤ suc n

≤-refl : (n : ℕ) → n ≤ n
≤-refl zero    = z≤n
≤-refl (suc n) = s≤s (≤-refl n)

≤-trans : {l m n : ℕ} → l ≤ m → m ≤ n → l ≤ n
≤-trans z≤n     _       = z≤n
≤-trans (s≤s p) (s≤s q) = s≤s (≤-trans p q)

≤-suc : {m n : ℕ} → m ≤ n → m ≤ suc n
≤-suc z≤n     = z≤n
≤-suc (s≤s p) = s≤s (≤-suc p)

≤-+ˡ : (m n : ℕ) → m ≤ (m + n)
≤-+ˡ zero    n = z≤n
≤-+ˡ (suc m) n = s≤s (≤-+ˡ m n)

≤-+ʳ : (m n : ℕ) → n ≤ (m + n)
≤-+ʳ zero    n = ≤-refl n
≤-+ʳ (suc m) n = ≤-suc (≤-+ʳ m n)

suc≰ : (n : ℕ) → ¬ (suc n ≤ n)
suc≰ zero    ()
suc≰ (suc n) (s≤s p) = suc≰ n p

mutual
  size : Tm → ℕ
  size (var x)     = suc zero
  size (node f ts) = suc (sizes ts)

  sizes : List Tm → ℕ
  sizes []       = zero
  sizes (t ∷ ts) = size t + sizes ts

mutual
  occ-size : (ρ : Subst) (t : Tm) {x : ℕ} → Occ x t → size (ρ x) ≤ size (sub ρ t)
  occ-size ρ (var x)     here    = ≤-refl (size (ρ x))
  occ-size ρ (node f ts) (arg o) = ≤-suc (occs-size ρ ts o)

  occs-size : (ρ : Subst) (ts : List Tm) {x : ℕ} → Occs x ts → size (ρ x) ≤ sizes (subs ρ ts)
  occs-size ρ (t ∷ ts) (hd o) = ≤-trans (occ-size ρ t o) (≤-+ˡ (size (sub ρ t)) (sizes (subs ρ ts)))
  occs-size ρ (t ∷ ts) (tl o) = ≤-trans (occs-size ρ ts o) (≤-+ʳ (size (sub ρ t)) (sizes (subs ρ ts)))

-- What the occurs check rules out.
cycle : (ρ : Subst) (x : ℕ) (u : Tm) → Occ x u → ¬ (var x ≡ u) → ¬ (ρ x ≡ sub ρ u)
cycle ρ x (var y)     o       ne e = ne (cong var (occ-var o))
cycle ρ x (node f ts) (arg o) ne e =
  suc≰ (size (ρ x)) (transport (λ v → suc (size (ρ x)) ≤ size v) (sym e) (s≤s (occs-size ρ ts o)))

------------------------------------------------------------------------
-- Equations between instances

node-head : {f g : ℕ} {ss ts : List Tm} → node f ss ≡ node g ts → f ≡ g
node-head refl = refl

node-args : {f g : ℕ} {ss ts : List Tm} → node f ss ≡ node g ts → ss ≡ ts
node-args refl = refl

none≢ok : {θ : Subst} → none ≡ ok θ → ⊥
none≢ok ()

ok≢none : {θ : Subst} → ok θ ≡ none → ⊥
ok≢none ()

Unifies : Subst → Tm × Tm → Set
Unifies ρ p = sub ρ (fst p) ≡ sub ρ (snd p)

-- ρ absorbs θ: ρ ≈ ρ ∘ θ.
Absorbs : Subst → Subst → Set
Absorbs ρ θ = ∀ x → ρ x ≡ sub ρ (θ x)

absorb : (ρ θ : Subst) → Absorbs ρ θ → (t : Tm) → sub ρ (sub θ t) ≡ sub ρ t
absorb ρ θ h t = trans (sub-comp ρ θ t) (sym (sub-ext ρ (ρ ∘ˢ θ) t (λ x _ → h x)))

-- A unifier that solves x := u absorbs [x := u] ∘ θ as well.
absorb-bind : (ρ θ : Subst) (x : ℕ) (u : Tm) → Absorbs ρ θ → ρ x ≡ sub ρ u
            → Absorbs ρ (single x u ∘ˢ θ)
absorb-bind ρ θ x u h ux z =
  trans (h z) (trans (sub-ext ρ (ρ ∘ˢ single x u) (θ z) (λ y _ → fix y)) (sym (sub-comp ρ (single x u) (θ z))))
  where
    fix : ∀ y → ρ y ≡ sub ρ (single x u y)
    fix y with y ≟ x
    ... | yes refl = ux
    ... | no _     = refl

push-all : (ρ : Subst) (ss ts : List Tm) (w w′ : List (Tm × Tm)) → push ss ts w ≡ just w′
         → subs ρ ss ≡ subs ρ ts → All (Unifies ρ) w → All (Unifies ρ) w′
push-all ρ []       []       w .w refl e us = us
push-all ρ (s ∷ ss) (t ∷ ts) w w′ p  e us = push-all ρ ss ts ((s , t) ∷ w) w′ p (∷-tail e) (∷-head e ∷ us)
push-all ρ []       (_ ∷ _)  w w′ () e us
push-all ρ (_ ∷ _)  []       w w′ () e us

push-none : (ρ : Subst) (ss ts : List Tm) (w : List (Tm × Tm)) → push ss ts w ≡ nothing
          → ¬ (subs ρ ss ≡ subs ρ ts)
push-none ρ []       []       w ()
push-none ρ (s ∷ ss) (t ∷ ts) w p e = push-none ρ ss ts ((s , t) ∷ w) p (∷-tail e)
push-none ρ []       (_ ∷ _)  w p ()
push-none ρ (_ ∷ _)  []       w p ()

------------------------------------------------------------------------
-- Every unifier of the remaining pairs that absorbs θ absorbs the result

mutual
  unify-factor : (n : ℕ) (θ : Subst) (w : List (Tm × Tm)) {θ′ : Subst} → unify n θ w ≡ ok θ′
               → (ρ : Subst) → Absorbs ρ θ → All (Unifies ρ) w → Absorbs ρ θ′
  unify-factor zero    θ w             () ρ h us
  unify-factor (suc n) θ []            refl ρ h us = h
  unify-factor (suc n) θ ((a , b) ∷ w) e ρ h (u ∷ us) =
    turn-factor n θ w (sub θ a) (sub θ b) e ρ h (trans (absorb ρ θ h a) (trans u (sym (absorb ρ θ h b)))) us

  turn-factor : (n : ℕ) (θ : Subst) (w : List (Tm × Tm)) (s t : Tm) {θ′ : Subst}
              → turn n θ w s t ≡ ok θ′ → (ρ : Subst) → Absorbs ρ θ → sub ρ s ≡ sub ρ t
              → All (Unifies ρ) w → Absorbs ρ θ′
  turn-factor n θ w s t e ρ h u us with s ≟ₜ t
  ... | yes _ = unify-factor n θ w e ρ h us
  ... | no _  = orient-factor n θ w s t e ρ h u us

  orient-factor : (n : ℕ) (θ : Subst) (w : List (Tm × Tm)) (s t : Tm) {θ′ : Subst}
                → orient n θ w s t ≡ ok θ′ → (ρ : Subst) → Absorbs ρ θ → sub ρ s ≡ sub ρ t
                → All (Unifies ρ) w → Absorbs ρ θ′
  orient-factor n θ w (var x)     t           e ρ h u us = bind-factor n θ w x t e ρ h u us
  orient-factor n θ w (node f ss) (var y)     e ρ h u us = bind-factor n θ w y (node f ss) e ρ h (sym u) us
  orient-factor n θ w (node f ss) (node g ts) e ρ h u us with f ≟ g
  ... | no _  = ⊥-elim (none≢ok e)
  ... | yes _ with push ss ts w in p
  ...   | nothing = ⊥-elim (none≢ok e)
  ...   | just w′ = unify-factor n θ w′ e ρ h (push-all ρ ss ts w w′ p (node-args u) us)

  bind-factor : (n : ℕ) (θ : Subst) (w : List (Tm × Tm)) (x : ℕ) (u : Tm) {θ′ : Subst}
              → bind n θ w x u ≡ ok θ′ → (ρ : Subst) → Absorbs ρ θ → ρ x ≡ sub ρ u
              → All (Unifies ρ) w → Absorbs ρ θ′
  bind-factor n θ w x u e ρ h ux us with occ? x u
  ... | yes _ = ⊥-elim (none≢ok e)
  ... | no _  = unify-factor n (single x u ∘ˢ θ) w e ρ (absorb-bind ρ θ x u h ux) us

------------------------------------------------------------------------
-- Failure: no unifier of the remaining pairs absorbs θ

mutual
  unify-fails : (n : ℕ) (θ : Subst) (w : List (Tm × Tm)) → unify n θ w ≡ none
              → (ρ : Subst) → Absorbs ρ θ → ¬ All (Unifies ρ) w
  unify-fails zero    θ w             () ρ h us
  unify-fails (suc n) θ []            () ρ h us
  unify-fails (suc n) θ ((a , b) ∷ w) e ρ h (u ∷ us) =
    turn-fails n θ w (sub θ a) (sub θ b) e ρ h (trans (absorb ρ θ h a) (trans u (sym (absorb ρ θ h b)))) us

  turn-fails : (n : ℕ) (θ : Subst) (w : List (Tm × Tm)) (s t : Tm)
             → turn n θ w s t ≡ none → (ρ : Subst) → Absorbs ρ θ → sub ρ s ≡ sub ρ t
             → ¬ All (Unifies ρ) w
  turn-fails n θ w s t e ρ h u us with s ≟ₜ t
  ... | yes _ = unify-fails n θ w e ρ h us
  ... | no ne = orient-fails n θ w s t ne e ρ h u us

  orient-fails : (n : ℕ) (θ : Subst) (w : List (Tm × Tm)) (s t : Tm) → ¬ (s ≡ t)
               → orient n θ w s t ≡ none → (ρ : Subst) → Absorbs ρ θ → sub ρ s ≡ sub ρ t
               → ¬ All (Unifies ρ) w
  orient-fails n θ w (var x)     t           ne e ρ h u us = bind-fails n θ w x t ne e ρ h u us
  orient-fails n θ w (node f ss) (var y)     ne e ρ h u us =
    bind-fails n θ w y (node f ss) (λ q → ne (sym q)) e ρ h (sym u) us
  orient-fails n θ w (node f ss) (node g ts) ne e ρ h u us with f ≟ g
  ... | no fg = fg (node-head u)
  ... | yes _ with push ss ts w in p
  ...   | nothing = push-none ρ ss ts w p (node-args u)
  ...   | just w′ = unify-fails n θ w′ e ρ h (push-all ρ ss ts w w′ p (node-args u) us)

  bind-fails : (n : ℕ) (θ : Subst) (w : List (Tm × Tm)) (x : ℕ) (u : Tm) → ¬ (var x ≡ u)
             → bind n θ w x u ≡ none → (ρ : Subst) → Absorbs ρ θ → ρ x ≡ sub ρ u
             → ¬ All (Unifies ρ) w
  bind-fails n θ w x u ne e ρ h ux us with occ? x u
  ... | yes o = cycle ρ x u o ne ux
  ... | no _  = unify-fails n (single x u ∘ˢ θ) w e ρ (absorb-bind ρ θ x u h ux) us

------------------------------------------------------------------------
-- Sorts

module Unification (Sg : Signature) (R : List Rule) where
  open Signature Sg
  open Calculus Sg R
  open Implications Sg R

  SameSort : Tm × Tm → Set
  SameSort p = Σ ℕ (λ k → WS (fst p) k × WS (snd p) k)

  WSθ : Subst → Set
  WSθ θ = ∀ x → WS (θ x) (vs x)

  ws-var : {x k : ℕ} → WS (var x) k → k ≡ vs x
  ws-var var = refl

  ws-args : {f k : ℕ} {ts : List Tm} → WS (node f ts) k → WSs ts (ins f)
  ws-args (node _ w) = w

  ws-θ : (θ : Subst) → WSθ θ → {t : Tm} {k : ℕ} → WS t k → WS (sub θ t) k
  ws-θ θ wθ w = ws-sub θ w (λ x _ → wθ x)

  ws-bind : (θ : Subst) (x : ℕ) (u : Tm) {k : ℕ} → WSθ θ → WS (var x) k → WS u k
          → WSθ (single x u ∘ˢ θ)
  ws-bind θ x u wθ wx wu z = ws-sub (single x u) (wθ z) (λ y _ → fix y)
    where
      fix : ∀ y → WS (single x u y) (vs y)
      fix y with y ≟ x
      ... | yes refl = transport (WS u) (ws-var wx) wu
      ... | no _     = var

  push-ws : (ss ts : List Tm) {ks : List ℕ} (w w′ : List (Tm × Tm)) → push ss ts w ≡ just w′
          → WSs ss ks → WSs ts ks → All SameSort w → All SameSort w′
  push-ws []       []       w .w refl [] [] ws = ws
  push-ws (s ∷ ss) (t ∷ ts) w w′ p (a ∷ as) (b ∷ bs) ws =
    push-ws ss ts ((s , t) ∷ w) w′ p as bs ((_ , a , b) ∷ ws)
  push-ws []       (_ ∷ _)  w w′ () _ _ _
  push-ws (_ ∷ _)  []       w w′ () _ _ _

  mutual
    unify-ws : (n : ℕ) (θ : Subst) (w : List (Tm × Tm)) {θ′ : Subst} → unify n θ w ≡ ok θ′
             → WSθ θ → All SameSort w → WSθ θ′
    unify-ws zero    θ w             () wθ ws
    unify-ws (suc n) θ []            refl wθ ws = wθ
    unify-ws (suc n) θ ((a , b) ∷ w) e wθ ((k , wa , wb) ∷ ws) =
      turn-ws n θ w (sub θ a) (sub θ b) e wθ (ws-θ θ wθ wa) (ws-θ θ wθ wb) ws

    turn-ws : (n : ℕ) (θ : Subst) (w : List (Tm × Tm)) (s t : Tm) {k : ℕ} {θ′ : Subst}
            → turn n θ w s t ≡ ok θ′ → WSθ θ → WS s k → WS t k → All SameSort w → WSθ θ′
    turn-ws n θ w s t e wθ ws wt wr with s ≟ₜ t
    ... | yes _ = unify-ws n θ w e wθ wr
    ... | no _  = orient-ws n θ w s t e wθ ws wt wr

    orient-ws : (n : ℕ) (θ : Subst) (w : List (Tm × Tm)) (s t : Tm) {k : ℕ} {θ′ : Subst}
              → orient n θ w s t ≡ ok θ′ → WSθ θ → WS s k → WS t k → All SameSort w → WSθ θ′
    orient-ws n θ w (var x)     t           e wθ ws wt wr = bind-ws n θ w x t e wθ ws wt wr
    orient-ws n θ w (node f ss) (var y)     e wθ ws wt wr = bind-ws n θ w y (node f ss) e wθ wt ws wr
    orient-ws n θ w (node f ss) (node g ts) e wθ ws wt wr with f ≟ g
    ... | no _    = ⊥-elim (none≢ok e)
    ... | yes refl with push ss ts w in p
    ...   | nothing = ⊥-elim (none≢ok e)
    ...   | just w′ = unify-ws n θ w′ e wθ (push-ws ss ts w w′ p (ws-args ws) (ws-args wt) wr)

    bind-ws : (n : ℕ) (θ : Subst) (w : List (Tm × Tm)) (x : ℕ) (u : Tm) {k : ℕ} {θ′ : Subst}
            → bind n θ w x u ≡ ok θ′ → WSθ θ → WS (var x) k → WS u k → All SameSort w → WSθ θ′
    bind-ws n θ w x u e wθ wx wu wr with occ? x u
    ... | yes _ = ⊥-elim (none≢ok e)
    ... | no _  = unify-ws n (single x u ∘ˢ θ) w e (ws-bind θ x u wθ wx wu) wr

  ----------------------------------------------------------------------
  -- What Implication.agda assumes

  mgu-sound : (n : ℕ) (s t : Tm) {k : ℕ} {θ : Subst} → WS s k → WS t k → mgu n s t ≡ ok θ
            → IsMGU θ s t
  mgu-sound n s t ws wt e =
    (λ ρ u → unify-factor n var ((s , t) ∷ []) e ρ (λ x → refl) (u ∷ []))
    , unify-ws n var ((s , t) ∷ []) e (λ x → var) ((_ , ws , wt) ∷ [])

  mgu-none : (n : ℕ) (s t : Tm) → mgu n s t ≡ none → NoUnifier s t
  mgu-none n s t e ρ u = unify-fails n var ((s , t) ∷ []) e ρ (λ x → refl) (u ∷ [])

------------------------------------------------------------------------
-- The unifier the Rust checker computes for le_trans's first inversion
-- (src/schematic.rs, examples/le-trans.proof): le (s P) B against the
-- renamed conclusion of le.succ, le (s M) (s N). The last argument pair is
-- taken first, and a variable on the left is bound: B := s N, P := M.

at : Outcome → ℕ → Maybe Tm
at (ok θ) x = just (θ x)
at _      x = nothing

private
  le s : List Tm → Tm
  le = node 0
  s  = node 1

  P B M N : Tm
  P = var 0
  B = var 1
  M = var 2
  N = var 3

  θ-le : Outcome
  θ-le = mgu 10 (le (s (P ∷ []) ∷ B ∷ [])) (le (s (M ∷ []) ∷ s (N ∷ []) ∷ []))

  _ : at θ-le 0 ≡ just M
  _ = refl

  _ : at θ-le 1 ≡ just (s (N ∷ []))
  _ = refl

  _ : at θ-le 2 ≡ just M
  _ = refl

  -- Variable against variable: the left one is bound.
  _ : at (mgu 10 P M) 0 ≡ just M
  _ = refl

  -- The occurs check, and a clash of heads.
  _ : mgu 10 P (s (P ∷ [])) ≡ none
  _ = refl

  _ : mgu 10 (s (P ∷ [])) (le []) ≡ none
  _ = refl
