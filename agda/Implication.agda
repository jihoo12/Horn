{-# OPTIONS --safe --without-K #-}
------------------------------------------------------------------------
-- Soundness of implicational schematic certificates.
--
-- Schematic.agda's facts depend on plain hypotheses. Here a hypothesis
-- may be a rule: premises, a conclusion, and variables it generalizes,
-- which an application may instantiate. This adds the forms of
-- src/schematic.rs that prove implications:
--
--   (hyp N (P...) J (X...))              a rule hypothesis
--   (apply N M (BIND...) (REF...))       apply a rule hypothesis, or an
--                                        earlier implication, as a rule
--   (induct N X (H...) J (CASE...))      induction for an implication,
--                                        with generalized induction
--                                        hypotheses
--   (invert N K (C...) J (CASE...))      case analysis on how a
--                                        hypothesis was derived
--
-- Inversion is sound because derivability is the least set closed under
-- the rules: a derivable judgment is the conclusion of some rule instance
-- with derivable premises. Each case is taken at a most general unifier of
-- the hypothesis and the rule's conclusion; this file assumes the
-- unifier's defining properties (`IsMGU`), which the checker's unification
-- has to provide.
--
-- As in Schematic.agda, this models what each step establishes, not the
-- Rust code, and imports no library.
------------------------------------------------------------------------
module Implication where

open import Schematic
open Rule
open Σ

module Implications (Sg : Signature) (R : List Rule) where
  open Signature Sg
  open Calculus Sg R

  ----------------------------------------------------------------------
  -- Rule hypotheses and their semantics

  record RHyp : Set where
    constructor rhyp
    field
      rprem  : List Tm
      rconcl : Tm
      gen    : List ℕ
  open RHyp

  plainR : Tm → RHyp
  plainR j = rhyp [] j []

  OccH : RHyp → ℕ → Set
  OccH h x = Occ x (rconcl h) ⊎ Occs x (rprem h)

  -- The variables a hypothesis fixes: all but the generalized ones.
  Fixed : RHyp → ℕ → Set
  Fixed h x = OccH h x × ¬ (x ∈ gen h)

  -- γ satisfies a rule hypothesis when every instance agreeing with γ
  -- off the generalized variables derives the conclusion from the premises.
  Sat : Subst → RHyp → Set
  Sat γ h = ∀ δ → (∀ x → ¬ (x ∈ gen h) → δ x ≡ γ x) → GW δ (OccH h)
          → All (λ p → Der (sub δ p)) (rprem h) → Der (sub δ (rconcl h))

  VarsR : List RHyp → Tm → ℕ → Set
  VarsR H J x = Occ x J ⊎ Any (λ h → Fixed h x) H

  ValidR : List RHyp → Tm → Set
  ValidR H J = ∀ γ → GW γ (VarsR H J) → All (Sat γ) H → Der (sub γ J)

  -- A plain hypothesis is satisfied when its judgment is derivable.
  sat-plain : (γ : Subst) (j : Tm) → GW γ (λ x → Occ x j) → Der (sub γ j) → Sat γ (plainR j)
  sat-plain γ j gw d δ agree gwδ [] =
    transport Der (sub-ext γ δ j (λ x _ → sym (agree x (λ ())))) d

  plain-sat : (γ : Subst) (j : Tm) → GW γ (λ x → Occ x j) → Sat γ (plainR j) → Der (sub γ j)
  plain-sat γ j gw s = s γ (λ x _ → refl) (λ { x (inl o) → gw x o ; x (inr ()) }) []

  ----------------------------------------------------------------------
  -- Ground and sort information under substitution

  ground-sub⁻ : (ρ : Subst) (t : Tm) {x : ℕ} → Ground (sub ρ t) → Occ x t → Ground (ρ x)
  ground-sub⁻ ρ t g o y oy = g y (sub-occ ρ t o oy)

  mutual
    -- Below a well-sorted pattern, an instance's subterms have the
    -- variables' sorts.
    ws-sub⁻ : (ρ : Subst) {t : Tm} {s : ℕ} → WS t s → WS (sub ρ t) s → ∀ {x} → Occ x t → WS (ρ x) (vs x)
    ws-sub⁻ ρ var w here = w
    ws-sub⁻ ρ (node e ws) (node _ w) (arg o) = wss-sub⁻ ρ ws w o

    wss-sub⁻ : (ρ : Subst) {ts : List Tm} {ss : List ℕ} → WSs ts ss → WSs (subs ρ ts) ss
             → ∀ {x} → Occs x ts → WS (ρ x) (vs x)
    wss-sub⁻ ρ (w ∷ ws) (v ∷ vs′) (hd o) = ws-sub⁻ ρ w v o
    wss-sub⁻ ρ (w ∷ ws) (v ∷ vs′) (tl o) = wss-sub⁻ ρ ws vs′ o

  ----------------------------------------------------------------------
  -- The forms

  -- (hyp N J)
  assume-valid : (j : Tm) → ValidR (plainR j ∷ []) j
  assume-valid j γ gw (s ∷ []) = plain-sat γ j (λ x o → gw x (inl o)) s

  data PremsR (θ : Subst) : List Tm → List RHyp → Set where
    []  : PremsR θ [] []
    _∷_ : {p : Tm} {ps : List Tm} {H H′ : List RHyp} → ValidR H (sub θ p) → PremsR θ ps H′
        → PremsR θ (p ∷ ps) (H ++ H′)

  -- Premises hold at γ when their variables are among the fact's.
  premisesR : {θ γ : Subst} {ps : List Tm} {H : List RHyp} {V : ℕ → Set} → PremsR θ ps H
            → (∀ x → Occs x (subs θ ps) → V x) → GW γ V → (∀ x → Any (λ h → Fixed h x) H → V x)
            → All (Sat γ) H → All (λ p → Der (sub γ (sub θ p))) ps
  premisesR [] side gw hv hs = []
  premisesR {θ} {γ} {p ∷ ps} (_∷_ {H = H} {H′} v rest) side gw hv hs with all-++ H hs
  ... | hs₁ , hs₂ =
        v γ gw₁ hs₁ ∷ premisesR rest (λ x o → side x (tl o)) gw (λ x a → hv x (any-++ʳ H a)) hs₂
    where
      gw₁ : GW γ (VarsR H (sub θ p))
      gw₁ x (inl o) = gw x (side x (hd o))
      gw₁ x (inr a) = gw x (hv x (any-++ˡ a))

  -- A rule step; the premise variable condition now counts only the
  -- variables hypotheses fix.
  step-validR : {r : Rule} → r ∈ R → (θ : Subst) → (∀ y → OccR y r → WS (θ y) (rs r y))
              → {H : List RHyp} → PremsR θ (prem r) H
              → (∀ x → Occs x (subs θ (prem r)) → VarsR H (sub θ (concl r)) x)
              → ValidR H (sub θ (concl r))
  step-validR {r} r∈R θ wθ {H} ps side γ gw hs =
    transport Der (sym (sub-comp γ θ (concl r)))
      (by r∈R (γ ∘ˢ θ) ok (all-comp (premisesR ps side gw (λ x a → inr a) hs)))
    where
      allowed : ∀ y → OccR y r → ∀ x → Occ x (θ y) → VarsR H (sub θ (concl r)) x
      allowed y (inl o) x ox = side x (subs-occ θ (prem r) o ox)
      allowed y (inr o) x ox = inl (sub-occ θ (concl r) o ox)

      ok : ∀ y → OccR y r → GroundWS ((γ ∘ˢ θ) y) (rs r y)
      ok y o = ground-sub γ (θ y) (λ x ox → fst (gw x (allowed y o x ox)))
             , ws-sub γ (wθ y o) (λ x ox → snd (gw x (allowed y o x ox)))

      all-comp : {ps : List Tm} → All (λ p → Der (sub γ (sub θ p))) ps → All (λ p → Der (sub (γ ∘ˢ θ) p)) ps
      all-comp []       = []
      all-comp {p ∷ ps} (d ∷ ds) = transport Der (sub-comp γ θ p) d ∷ all-comp ds

  -- (apply N M BIND REF...) with M a rule hypothesis h: σ instantiates
  -- only h's generalized variables.
  apply-hyp-valid : (h : RHyp) (σ : Subst) → (∀ x → ¬ (x ∈ gen h) → σ x ≡ var x)
                  → (∀ x → x ∈ gen h → OccH h x → WS (σ x) (vs x))
                  → {H : List RHyp} → PremsR σ (rprem h) H
                  → (∀ x → (Occs x (subs σ (rprem h)) ⊎ Σ ℕ (λ y → (y ∈ gen h) × OccH h y × Occ x (σ y)))
                       → VarsR (h ∷ H) (sub σ (rconcl h)) x)
                  → ValidR (h ∷ H) (sub σ (rconcl h))
  apply-hyp-valid h σ off wσ {H} ps side γ gw (sh ∷ hs) =
    transport Der (sym (sub-comp γ σ (rconcl h))) (sh (γ ∘ˢ σ) agree gwδ prems)
    where
      agree : ∀ x → ¬ (x ∈ gen h) → (γ ∘ˢ σ) x ≡ γ x
      agree x n = cong (sub γ) (off x n)

      fixed-in : ∀ x → OccH h x → ¬ (x ∈ gen h) → VarsR (h ∷ H) (sub σ (rconcl h)) x
      fixed-in x o n = inr (here (o , n))

      gwδ : GW (γ ∘ˢ σ) (OccH h)
      gwδ x o with x ∈? gen h
      ... | yes m =
            ground-sub γ (σ x) (λ y oy → fst (gw y (side y (inr (x , m , o , oy)))))
            , ws-sub γ (wσ x m o) (λ y oy → snd (gw y (side y (inr (x , m , o , oy)))))
      ... | no n = transport (λ t → GroundWS t (vs x)) (sym (agree x n)) (gw x (fixed-in x o n))

      prems : All (λ p → Der (sub (γ ∘ˢ σ) p)) (rprem h)
      prems = all-comp (premisesR ps (λ x o → side x (inl o)) gw (λ x a → hv x a) hs)
        where
          hv : ∀ x → Any (λ h′ → Fixed h′ x) H → VarsR (h ∷ H) (sub σ (rconcl h)) x
          hv x a = inr (there a)

          all-comp : {ps : List Tm} → All (λ p → Der (sub γ (sub σ p))) ps → All (λ p → Der (sub (γ ∘ˢ σ) p)) ps
          all-comp []       = []
          all-comp {p ∷ ps} (d ∷ ds) = transport Der (sub-comp γ σ p) d ∷ all-comp ds

  -- (apply N M BIND REF...) with M an implication proved earlier, whose
  -- hypotheses are plain: an instance of it, with its hypotheses proved.
  apply-fact-valid : {Ps : List Tm} {J : Tm} → ValidR (map plainR Ps) J → (σ : Subst)
                   → (∀ x → VarsR (map plainR Ps) J x → WS (σ x) (vs x))
                   → {H : List RHyp} → PremsR σ Ps H
                   → (∀ x → (Occs x (subs σ Ps) ⊎ Σ ℕ (λ y → VarsR (map plainR Ps) J y × Occ x (σ y)))
                        → VarsR H (sub σ J) x)
                   → ValidR H (sub σ J)
  apply-fact-valid {Ps} {J} v σ wσ {H} ps side γ gw hs =
    transport Der (sym (sub-comp γ σ J)) (v (γ ∘ˢ σ) gwδ (sats Ps (λ m → m) (premisesR ps (λ x o → side x (inl o)) gw (λ x a → inr a) hs)))
    where
      gwδ : GW (γ ∘ˢ σ) (VarsR (map plainR Ps) J)
      gwδ x o = ground-sub γ (σ x) (λ y oy → fst (gw y (side y (inr (x , o , oy)))))
              , ws-sub γ (wσ x o) (λ y oy → snd (gw y (side y (inr (x , o , oy)))))

      plain-in : ∀ {x} (qs : List Tm) {q : Tm} → q ∈ qs → Occ x q → Any (λ h → Fixed h x) (map plainR qs)
      plain-in (q ∷ qs) (here refl) o = here (inl o , λ ())
      plain-in (q ∷ qs) (there m)   o = there (plain-in qs m o)

      sats : (qs : List Tm) → (∀ {q} → q ∈ qs → q ∈ Ps) → All (λ p → Der (sub γ (sub σ p))) qs
           → All (Sat (γ ∘ˢ σ)) (map plainR qs)
      sats []       inc []       = []
      sats (q ∷ qs) inc (d ∷ ds) =
        sat-plain (γ ∘ˢ σ) q (λ x o → gwδ x (inr (plain-in Ps (inc (here refl)) o)))
                  (transport Der (sub-comp γ σ q) d)
        ∷ sats qs (λ m → inc (there m)) ds

  ----------------------------------------------------------------------
  -- Induction for an implication

  occs-map⁻ : (σ : Subst) (ps : List Tm) {x : ℕ} → Occs x (map (sub σ) ps) → Σ Tm (λ p → (p ∈ ps) × Occ x (sub σ p))
  occs-map⁻ σ (p ∷ ps) (hd o) = p , here refl , o
  occs-map⁻ σ (p ∷ ps) (tl o) with occs-map⁻ σ ps o
  ... | q , m , o′ = q , there m , o′

  occs-map⁺ : (σ : Subst) (ps : List Tm) {x : ℕ} {p : Tm} → p ∈ ps → Occ x (sub σ p) → Occs x (map (sub σ) ps)
  occs-map⁺ σ (q ∷ ps) (here refl) o = hd o
  occs-map⁺ σ (q ∷ ps) (there m)   o = tl (occs-map⁺ σ ps m o)

  occs-∈ : (ps : List Tm) {x : ℕ} {p : Tm} → p ∈ ps → Occ x p → Occs x ps
  occs-∈ (q ∷ ps) (here refl) o = hd o
  occs-∈ (q ∷ ps) (there m)   o = tl (occs-∈ ps m o)

  occs-plain : (ps : List Tm) {x : ℕ} → Occs x ps → Any (λ h → Fixed h x) (map plainR ps)
  occs-plain (p ∷ ps) (hd o) = here (inl o , λ ())
  occs-plain (p ∷ ps) (tl o) = there (occs-plain ps o)

  sats-plain : (γ : Subst) (ps : List Tm) → (∀ x → Occs x ps → GroundWS (γ x) (vs x))
             → All (Sat γ) (map plainR ps) → All (λ p → Der (sub γ p)) ps
  sats-plain γ []       gw []       = []
  sats-plain γ (p ∷ ps) gw (s ∷ ss) =
    plain-sat γ p (λ x o → gw x (hd o)) s ∷ sats-plain γ ps (λ x o → gw x (tl o)) ss

  -- What a case for constructor c may assume: a premise of the motive at
  -- c(ys), or the motive at some y of X's sort as a rule hypothesis that
  -- generalizes no case variable.
  data CaseHyp (X : ℕ) (Ps : List Tm) (J : Tm) (c : ℕ) (ys : List ℕ) : RHyp → Set where
    premise : {p : Tm} → p ∈ Ps → CaseHyp X Ps J c ys (plainR (sub (point X (node c (map var ys))) p))
    ih      : (y : ℕ) → y ∈ ys → vs y ≡ vs X → (G : List ℕ) → (∀ g → g ∈ G → ¬ (g ∈ ys))
            → CaseHyp X Ps J c ys (rhyp (map (sub (point X (var y))) Ps) (sub (point X (var y)) J) G)

  record SemCaseR (X : ℕ) (Ps : List Tm) (J : Tm) (c : ℕ) : Set where
    constructor semcaseR
    field
      ys       : List ℕ
      distinct : Distinct ys
      sorts    : map vs ys ≡ ins c
      fresh    : All (λ y → ¬ (Occ y J ⊎ Occs y Ps)) ys
      hs       : List RHyp
      allowed  : All (CaseHyp X Ps J c ys) hs
      valid    : ValidR hs (sub (point X (node c (map var ys))) J)

  module InductionR (X : ℕ) (Ps : List Tm) (J : Tm) (oX : Occ X J ⊎ Occs X Ps)
                    (cases : (c : ℕ) → out c ≡ vs X → SemCaseR X Ps J c) where

    Mv : ℕ → Set
    Mv x = Occ x J ⊎ Occs x Ps

    P : Tm → Set
    P t = ∀ γ → GW γ Mv → γ X ≡ t → All (λ p → Der (sub γ p)) Ps → Der (sub γ J)

    Q : ℕ → Tm → Set
    Q y t = GroundWS t (vs y) × (vs y ≡ vs X → P t)

    not-case : {ys : List ℕ} → All (λ y → ¬ Mv y) ys → ∀ {x} → Mv x → ¬ (x ∈ ys)
    not-case fresh o m with all-any fresh m
    ... | y , n , refl = n o

    -- A term u of the motive, with M put for X and the case variables bound.
    gw-point : (γ : Subst) {ys : List ℕ} {ts : List Tm} → GW γ Mv
             → All (λ y → ¬ Mv y) ys → All₂ Q ys ts
             → (M : Tm) → (∀ x → Occ x M → x ∈ ys)
             → (u : Tm) → (∀ x → Occ x u → Mv x)
             → ∀ x → Occ x (sub (point X M) u) → GroundWS (upd γ ys ts x) (vs x)
    gw-point γ {ys} {ts} gw fresh qs M inM u inc x o with occ-sub (point X M) u o
    ... | z , oz , ox with X ≟ z
    ...   | yes refl = fst (upd-in γ qs x (inM x ox))
    ...   | no _ with occ-var ox
    ...     | refl = transport (λ t → GroundWS t (vs x)) (sym (upd-out γ ys ts x (not-case fresh (inc x oz))))
                       (gw x (inc x oz))

    occs-has : {x : ℕ} {ps : List Tm} → Occs x ps → Σ Tm (λ p → (p ∈ ps) × Occ x p)
    occs-has {ps = p ∷ ps} (hd o) = p , here refl , o
    occs-has {ps = p ∷ ps} (tl o) with occs-has o
    ... | r , mr , or = r , there mr , or

    IHyp : ℕ → List ℕ → RHyp
    IHyp y G = rhyp (map (sub (point X (var y))) Ps) (sub (point X (var y)) J) G

    pt-here : (y : ℕ) → Occ y (point X (var y) X)
    pt-here y with X ≟ X
    ... | yes _ = here
    ... | no ne = ⊥-elim (ne refl)

    -- y occurs in the induction hypothesis at y, as X occurs in the motive.
    ih-occ : (y : ℕ) (G : List ℕ) → Mv X → OccH (IHyp y G) y
    ih-occ y G (inl o) = inl (sub-occ (point X (var y)) J o (pt-here y))
    ih-occ y G (inr o) with occs-has o
    ... | p , mp , op = inr (occs-map⁺ (point X (var y)) Ps mp (sub-occ (point X (var y)) p op (pt-here y)))

    -- The motive's other variables occur in it unchanged.
    ih-keep : (y : ℕ) (G : List ℕ) (x : ℕ) → ¬ (X ≡ x) → Mv x → OccH (IHyp y G) x
    ih-keep y G x ne o = go′ o
      where
        keep : Occ x (point X (var y) x)
        keep with X ≟ x
        ... | yes e = ⊥-elim (ne e)
        ... | no _  = here

        go′ : Mv x → OccH (IHyp y G) x
        go′ (inl o′) = inl (sub-occ (point X (var y)) J o′ keep)
        go′ (inr o′) with occs-has o′
        ... | p , mp , op = inr (occs-map⁺ (point X (var y)) Ps mp (sub-occ (point X (var y)) p op keep))

    mutual
      go : {t : Tm} {s : ℕ} → WS t s → s ≡ vs X → Ground t → P t
      go var eq gr = ⊥-elim (gr _ here)
      go {node c ts} (node e w) eq gr γ gw γX prems with cases c (trans e eq)
      ... | semcaseR ys distinct sorts fresh hs allowed valid =
            transport Der (same J (λ x o → inl o)) (valid γ′ gw′ (sats hs allowed))
        where
          ground-args : ∀ x → ¬ Occs x ts
          ground-args x o = gr x (arg o)

          qs : All₂ Q ys ts
          qs = build ys sorts w (gos w) ground-args
            where
              build : (ys : List ℕ) {ss : List ℕ} {ts : List Tm} → map vs ys ≡ ss → WSs ts ss
                    → All₂ (λ t s → s ≡ vs X → Ground t → P t) ts ss
                    → (∀ x → ¬ Occs x ts) → All₂ Q ys ts
              build []       refl []       []       g = []
              build (y ∷ ys) refl (w ∷ ws) (p ∷ ps) g =
                (((λ x o → g x (hd o)) , w) , λ e → p e (λ x o → g x (hd o)))
                ∷ build ys refl ws ps (λ x o → g x (tl o))

          γ′ : Subst
          γ′ = upd γ ys ts

          N : Tm
          N = node c (map var ys)

          inN : ∀ x → Occ x N → x ∈ ys
          inN x (arg o) = occs-map-var ys o

          inP : {p : Tm} → p ∈ Ps → ∀ x → Occ x p → Mv x
          inP m x o = inr (occs-∈ Ps m o)

          -- γ′ ∘ point X N agrees with γ on the motive's variables.
          same : (u : Tm) → (∀ x → Occ x u → Mv x) → sub γ′ (sub (point X N) u) ≡ sub γ u
          same u inc = trans (sub-comp γ′ (point X N) u) (sub-ext _ _ u agree)
            where
              agree : ∀ x → Occ x u → sub γ′ (point X N x) ≡ γ x
              agree x o with X ≟ x
              ... | yes refl = trans (cong (node c) (trans (subs-map-var γ′ ys) (upd-map γ distinct qs)))
                                     (sym γX)
              ... | no _ = upd-out γ ys ts x (not-case fresh (inc x o))

          gw′ : GW γ′ (VarsR hs (sub (point X N) J))
          gw′ x (inl o) = gw-point γ gw fresh qs N inN J (λ x o → inl o) x o
          gw′ x (inr a) with all-any allowed a
          ... | _ , premise m , (inl o , _) = gw-point γ gw fresh qs N inN _ (inP m) x o
          ... | _ , ih y m sy G disj , (inl o , _) =
                gw-point γ gw fresh qs (var y) (λ { x here → m }) J (λ x o → inl o) x o
          ... | _ , ih y m sy G disj , (inr o , _) with occs-map⁻ (point X (var y)) Ps o
          ...   | p , mp , o′ = gw-point γ gw fresh qs (var y) (λ { x here → m }) p (inP mp) x o′

          sats : (hs : List RHyp) → All (CaseHyp X Ps J c ys) hs → All (Sat γ′) hs
          sats []       []         = []
          sats (h ∷ hs) (a ∷ rest) = sat a ∷ sats hs rest
            where
              sat : {h : RHyp} → CaseHyp X Ps J c ys h → Sat γ′ h
              sat (premise {p} m) =
                sat-plain γ′ (sub (point X N) p) (gw-point γ gw fresh qs N inN p (inP m))
                  (transport Der (sym (same p (inP m))) (all-∈ prems m))
              sat (ih y m sy G disj) δ agree gwδ premsδ =
                transport Der (sym (sub-comp δ (point X (var y)) J)) (claim δ′ gwδ′ δ′X premsδ′)
                where
                  q : Q y (γ′ y)
                  q = upd-in γ qs y m

                  claim : P (γ′ y)
                  claim = snd q sy

                  δ′ : Subst
                  δ′ = δ ∘ˢ point X (var y)

                  y∉G : ¬ (y ∈ G)
                  y∉G g = disj y g m

                  δy : (δ ∘ˢ point X (var y)) X ≡ δ y
                  δy with X ≟ X
                  ... | yes _ = refl
                  ... | no ne = ⊥-elim (ne refl)

                  δ′X : δ′ X ≡ γ′ y
                  δ′X = trans δy (agree y y∉G)

                  gwδ′ : GW δ′ Mv
                  gwδ′ x o with X ≟ x
                  ... | yes refl = transport (GroundWS (δ y)) sy (gwδ y (ih-occ y G oX))
                  ... | no ne = gwδ x (ih-keep y G x ne o)

                  premsδ′ : All (λ p → Der (sub δ′ p)) Ps
                  premsδ′ = back Ps premsδ
                    where
                      back : (ps : List Tm) → All (λ p → Der (sub δ p)) (map (sub (point X (var y))) ps)
                           → All (λ p → Der (sub δ′ p)) ps
                      back []       []       = []
                      back (p ∷ ps) (d ∷ ds) = transport Der (sub-comp δ (point X (var y)) p) d ∷ back ps ds

      gos : {ts : List Tm} {ss : List ℕ} → WSs ts ss → All₂ (λ t s → s ≡ vs X → Ground t → P t) ts ss
      gos []       = []
      gos (w ∷ ws) = go w ∷ gos ws

    induction : ValidR (map plainR Ps) J
    induction γ gw sats = go (snd g) refl (fst g) γ gwMv refl (sats-plain γ Ps (λ x o → gwMv x (inr o)) sats)
      where
        gwMv : GW γ Mv
        gwMv x (inl o) = gw x (inl o)
        gwMv x (inr o) = gw x (inr (occs-plain Ps o))

        g : GroundWS (γ X) (vs X)
        g = gwMv X oX

  ----------------------------------------------------------------------
  -- Inversion

  -- A derivable judgment is the conclusion of a rule instance.
  der-inv : {t : Tm} → Der t
          → Σ Rule (λ r → (r ∈ R) × Σ Subst (λ σ →
              (∀ y → OccR y r → GroundWS (σ y) (rs r y)) × All (λ p → Der (sub σ p)) (prem r) × (t ≡ sub σ (concl r))))
  der-inv (by m σ ok ps) = _ , m , σ , ok , ps , refl

  -- θ is a most general unifier of s and t, and keeps sorts.
  IsMGU : Subst → Tm → Tm → Set
  IsMGU θ s t = (∀ ρ → sub ρ s ≡ sub ρ t → ∀ x → ρ x ≡ sub ρ (θ x)) × (∀ x → WS (θ x) (vs x))

  NoUnifier : Tm → Tm → Set
  NoUnifier s t = ∀ ρ → ¬ (sub ρ s ≡ sub ρ t)

  -- θ applied to a hypothesis, off its generalized variables.
  off : Subst → RHyp → Subst
  off θ c x = pick (x ∈? gen c) (var x) (θ x)

  appθ : Subst → RHyp → RHyp
  appθ θ c = rhyp (map (sub (off θ c)) (rprem c)) (sub (off θ c) (rconcl c)) (gen c)

  -- Renaming a rule's variables apart: rn, with its inverse back.
  record Renaming (r : Rule) (Used : ℕ → Set) : Set where
    constructor mkRenaming
    field
      rn      : ℕ → ℕ
      back    : ℕ → Maybe ℕ
      back-rn : ∀ y → OccR y r → back (rn y) ≡ just y
      rn-back : ∀ x y → back x ≡ just y → (x ≡ rn y) × OccR y r
      sorted  : ∀ y → OccR y r → vs (rn y) ≡ rs r y
      fresh   : ∀ y → OccR y r → ¬ Used (rn y)

  ren : (ℕ → ℕ) → Subst
  ren rn y = var (rn y)

  -- What a case for rule r may assume: θ of a premise of r, renamed, or
  -- θ of a context hypothesis.
  data InvHyp (θ : Subst) (rn : ℕ → ℕ) (r : Rule) (C : List RHyp) : RHyp → Set where
    premise : {p : Tm} → p ∈ prem r → InvHyp θ rn r C (plainR (sub θ (sub (ren rn) p)))
    context : {c : RHyp} → c ∈ C → InvHyp θ rn r C (appθ θ c)

  record InvCase (h J : Tm) (C : List RHyp) (r : Rule) (rn : ℕ → ℕ) : Set where
    constructor invcase
    field
      θ         : Subst
      mgu       : IsMGU θ h (sub (ren rn) (concl r))
      noCapture : ∀ c → c ∈ C → ∀ x → Fixed c x → ∀ g → g ∈ gen c → ¬ Occ g (θ x)
      hs        : List RHyp
      allowed   : All (InvHyp θ rn r C) hs
      valid     : ValidR hs (sub θ J)

  Used : Tm → Tm → List RHyp → ℕ → Set
  Used h J C x = Occ x h ⊎ Occ x J ⊎ Any (λ c → OccH c x) C

  -- For every rule: renamed apart, either it cannot conclude h, or a case.
  record RuleCase (h J : Tm) (C : List RHyp) (r : Rule) : Set where
    constructor rulecase
    field
      renamed : Renaming r (Used h J C)
      outcome : NoUnifier h (sub (ren (Renaming.rn renamed)) (concl r))
              ⊎ InvCase h J C r (Renaming.rn renamed)

  invert-valid : (h J : Tm) (C : List RHyp) → (∀ r → r ∈ R → RuleCase h J C r) → ValidR (plainR h ∷ C) J
  invert-valid h J C cases γ gw (sh ∷ sC) with der-inv (plain-sat γ h (λ x o → gw x (inr (here (inl o , λ ())))) sh)
  ... | r , m , σ , ok , ps , eq with cases r m
  ... | rulecase (mkRenaming rn back back-rn rn-back sorted fresh) outcome = result outcome
    where
      choose : Maybe ℕ → ℕ → Tm
      choose (just y) x = σ y
      choose nothing  x = γ x

      ρ : Subst
      ρ x = choose (back x) x

      ρ-rn : ∀ y → OccR y r → ρ (rn y) ≡ σ y
      ρ-rn y o = cong (λ b → choose b (rn y)) (back-rn y o)

      ρ-used : ∀ x → Used h J C x → ρ x ≡ γ x
      ρ-used x u with back x in e
      ... | nothing = refl
      ... | just y with rn-back x y e
      ...   | refl , o = ⊥-elim (fresh y o u)

      ren-ρ : (u : Tm) → (∀ y → Occ y u → OccR y r) → sub ρ (sub (ren rn) u) ≡ sub σ u
      ren-ρ u inR = trans (sub-comp ρ (ren rn) u) (sub-ext _ _ u (λ y o → ρ-rn y (inR y o)))

      ρ-h : sub ρ h ≡ sub γ h
      ρ-h = sub-ext _ _ h (λ x o → ρ-used x (inl o))

      unifies : sub ρ h ≡ sub ρ (sub (ren rn) (concl r))
      unifies = trans ρ-h (trans eq (sym (ren-ρ (concl r) (λ y o → inr o))))

      gw-h : ∀ x → Fixed (plainR h) x → GroundWS (γ x) (vs x)
      gw-h x f = gw x (inr (here f))

      result : NoUnifier h (sub (ren rn) (concl r)) ⊎ InvCase h J C r rn → Der (sub γ J)
      result (inl nu) = ⊥-elim (nu ρ unifies)
      result (inr (invcase θ (factor , wθ) noCapture hs allowed valid)) =
        transport Der (trans (sub-comp ρ θ J) (trans (sym (sub-ext _ _ J (λ x _ → fact x))) (sub-ext _ _ J (λ x o → ρ-used x (inr (inl o))))))
          (valid ρ gwρ (sats hs allowed))
        where
          fact : ∀ x → ρ x ≡ sub ρ (θ x)
          fact = factor ρ unifies

          -- Where ρ is known to be ground and well-sorted.
          Dom : ℕ → Set
          Dom z = Occ z h ⊎ Occ z J ⊎ Any (λ c → Fixed c z) C ⊎ Σ ℕ (λ y → OccR y r × (z ≡ rn y))

          dom-ok : ∀ z → Dom z → GroundWS (ρ z) (vs z)
          dom-ok z (inl o) = transport (λ t → GroundWS t (vs z)) (sym (ρ-used z (inl o))) (gw-h z (inl o , λ ()))
          dom-ok z (inr (inl o)) = transport (λ t → GroundWS t (vs z)) (sym (ρ-used z (inr (inl o)))) (gw z (inl o))
          dom-ok z (inr (inr (inl a))) =
            transport (λ t → GroundWS t (vs z)) (sym (ρ-used z (inr (inr (any-mono a))))) (gw z (inr (there a)))
            where
              any-mono : {cs : List RHyp} → Any (λ c → Fixed c z) cs → Any (λ c → OccH c z) cs
              any-mono (here f)  = here (fst f)
              any-mono (there a) = there (any-mono a)
          dom-ok z (inr (inr (inr (y , o , refl)))) =
            transport (λ t → GroundWS t (vs (rn y))) (sym (ρ-rn y o))
              (transport (GroundWS (σ y)) (sym (sorted y o)) (ok y o))

          -- A variable of θ z, for z in the domain, is ground and sorted.
          through : ∀ x z → Dom z → Occ x (θ z) → GroundWS (ρ x) (vs x)
          through x z d o =
            ground-sub⁻ ρ (θ z) (transport Ground (fact z) (fst g)) o
            , ws-sub⁻ ρ (wθ z) (transport (λ t → WS t (vs z)) (fact z) (snd g)) o
            where
              g : GroundWS (ρ z) (vs z)
              g = dom-ok z d

          in-sub : ∀ x (u : Tm) → (∀ z → Occ z u → Dom z) → Occ x (sub θ u) → GroundWS (ρ x) (vs x)
          in-sub x u inD o with occ-sub θ u o
          ... | z , oz , ox = through x z (inD z oz) ox

          prem-dom : {p : Tm} → p ∈ prem r → ∀ z → Occ z (sub (ren rn) p) → Dom z
          prem-dom m z o with occ-sub (ren rn) _ o
          ... | y , oy , here = inr (inr (inr (y , inl (occs-∈ (prem r) m oy) , refl)))

          -- θ off a context hypothesis's generalized variables.
          ctx-var : {c : RHyp} → c ∈ C → ∀ x → ¬ (x ∈ gen c) → (u : Tm) → (∀ z → Occ z u → OccH c z)
                  → Occ x (sub (off θ c) u) → GroundWS (ρ x) (vs x)
          ctx-var {c} mc x ng u inC o with occ-sub (off θ c) u o
          ... | z , oz , ox with z ∈? gen c
          ...   | yes gz with ox
          ...     | here = ⊥-elim (ng gz)
          ctx-var {c} mc x ng u inC o | z , oz , ox | no nz =
                  through x z (inr (inr (inl (in-C mc (inC z oz , nz))))) ox
            where
              in-C : {c : RHyp} {cs : List RHyp} → c ∈ cs → Fixed c z → Any (λ c′ → Fixed c′ z) cs
              in-C (here refl) f = here f
              in-C (there m)   f = there (in-C m f)

          gwρ : GW ρ (VarsR hs (sub θ J))
          gwρ x (inl o) = in-sub x J (λ z oz → inr (inl oz)) o
          gwρ x (inr a) with all-any allowed a
          ... | _ , premise m , (inl o , _) = in-sub x _ (prem-dom m) o
          ... | _ , premise m , (inr () , _)
          ... | _ , context {c} mc , (inl o , ng) = ctx-var mc x ng (rconcl c) (λ z oz → inl oz) o
          ... | _ , context {c} mc , (inr o , ng) with occs-map⁻ (off θ c) (rprem c) o
          ...   | p , mp , op = ctx-var mc x ng p (λ z oz → inr (occs-∈ (rprem c) mp oz)) op

          sats : (hs : List RHyp) → All (InvHyp θ rn r C) hs → All (Sat ρ) hs
          sats []       []         = []
          sats (k ∷ hs) (a ∷ rest) = sat a ∷ sats hs rest
            where
              sat : {k : RHyp} → InvHyp θ rn r C k → Sat ρ k
              sat (premise {p} m) =
                sat-plain ρ _ (λ x o → in-sub x _ (prem-dom m) o)
                  (transport Der (trans (sym (ren-ρ p (λ y o → inl (occs-∈ (prem r) m o))))
                                        (trans (sub-ext _ _ (sub (ren rn) p) (λ x _ → fact x)) (sym (sub-comp ρ θ (sub (ren rn) p)))))
                             (all-∈ ps m))
              sat (context {c} mc) δ agree gwδ premsδ =
                transport Der (sym (same (rconcl c) (λ z oz → inl oz))) (all-∈ sC mc δ′ agree′ gwδ′ prems′)
                where
                  δ′ : Subst
                  δ′ x = pick (x ∈? gen c) (δ x) (γ x)

                  agree′ : ∀ x → ¬ (x ∈ gen c) → δ′ x ≡ γ x
                  agree′ x n with x ∈? gen c
                  ... | yes g = ⊥-elim (n g)
                  ... | no _  = refl

                  fixed-in : ∀ z → OccH c z → ¬ (z ∈ gen c) → Any (λ c′ → Fixed c′ z) C
                  fixed-in z o n = in-C mc (o , n)
                    where
                      in-C : {cs : List RHyp} → c ∈ cs → Fixed c z → Any (λ c′ → Fixed c′ z) cs
                      in-C (here refl) f = here f
                      in-C (there m)   f = there (in-C m f)

                  -- δ through θ off c agrees with δ′ on c's variables.
                  pointwise : ∀ z → OccH c z → sub δ (off θ c z) ≡ δ′ z
                  pointwise z o with z ∈? gen c
                  ... | yes _ = refl
                  ... | no n =
                        trans (sub-ext δ ρ (θ z) (λ x ox → agree x (no-gen x ox)))
                              (trans (sym (fact z)) (ρ-used z (inr (inr (in-occ mc o)))))
                    where
                      no-gen : ∀ x → Occ x (θ z) → ¬ (x ∈ gen c)
                      no-gen x ox g = noCapture c mc z (o , n) x g ox

                      in-occ : {cs : List RHyp} → c ∈ cs → OccH c z → Any (λ c′ → OccH c′ z) cs
                      in-occ (here refl) f = here f
                      in-occ (there m)   f = there (in-occ m f)

                  same : (u : Tm) → (∀ z → Occ z u → OccH c z) → sub δ (sub (off θ c) u) ≡ sub δ′ u
                  same u inC = trans (sub-comp δ (off θ c) u) (sub-ext _ _ u (λ z oz → pointwise z (inC z oz)))

                  gwδ′ : GW δ′ (OccH c)
                  gwδ′ z o with z ∈? gen c
                  ... | yes g = gwδ z (occ-off o)
                    where
                      keep : Occ z (off θ c z)
                      keep with z ∈? gen c
                      ... | yes _ = here
                      ... | no n  = ⊥-elim (n g)

                      occ-off : OccH c z → OccH (appθ θ c) z
                      occ-off (inl o′) = inl (sub-occ (off θ c) (rconcl c) o′ keep)
                      occ-off (inr o′) with occs-has′ o′
                        where
                          occs-has′ : {ps : List Tm} → Occs z ps → Σ Tm (λ p → (p ∈ ps) × Occ z p)
                          occs-has′ {p ∷ ps} (hd o) = p , here refl , o
                          occs-has′ {p ∷ ps} (tl o) with occs-has′ o
                          ... | q , mq , oq = q , there mq , oq
                      ... | p , mp , op = inr (occs-map⁺ (off θ c) (rprem c) mp (sub-occ (off θ c) p op keep))
                  ... | no n = gw z (inr (there (fixed-in z o n)))

                  prems′ : All (λ p → Der (sub δ′ p)) (rprem c)
                  prems′ = back′ (rprem c) (λ m → m) premsδ
                    where
                      back′ : (qs : List Tm) → (∀ {q} → q ∈ qs → q ∈ rprem c)
                            → All (λ p → Der (sub δ p)) (map (sub (off θ c)) qs) → All (λ p → Der (sub δ′ p)) qs
                      back′ []       inc []       = []
                      back′ (q ∷ qs) inc (d ∷ ds) =
                        transport Der (same q (λ z oz → inr (occs-∈ (rprem c) (inc (here refl)) oz))) d
                        ∷ back′ qs (λ m → inc (there m)) ds
