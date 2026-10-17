{-# OPTIONS --safe --without-K #-}
------------------------------------------------------------------------
-- Soundness of schematic certificates (src/schematic.rs).
--
-- Terms are open: `var x` is an eigenvariable of sort `vs x`. A fact is a
-- list of hypotheses H and a judgment J. It is *valid* when every
-- well-sorted ground instance of J is derivable whenever the same instance
-- of every hypothesis is. Derivations use well-sorted ground instances of
-- the rules, so a sort without ground terms is modelled faithfully.
--
-- The calculus `_⊢_` has one constructor per form the checker accepts:
-- hypotheses, instances of hypothesis-free facts, rule steps (with the
-- condition that premise variables occur in the conclusion or the
-- hypotheses), and structural induction. The main theorem is
--
--   sound : H ⊢ J → Valid H J
--
-- so a hypothesis-free accepted judgment has every well-sorted ground
-- instance derivable. The file also shows that dropping the premise
-- variable condition would be unsound, using a sort without ground terms.
--
-- Like Soundness.agda, this models what each accepted step establishes,
-- not the Rust code: parsing, names, hash-consing, the matching algorithm
-- that finds a rule step's bindings, and hypothesis bookkeeping by step
-- index are outside the model. No library is imported.
------------------------------------------------------------------------
module Schematic where

------------------------------------------------------------------------
-- Prelude

data ⊥ : Set where

⊥-elim : {A : Set} → ⊥ → A
⊥-elim ()

¬_ : Set → Set
¬ A = A → ⊥

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x
infix 4 _≡_

sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl q = q

cong : {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

cong₂ : {A B C : Set} (f : A → B → C) {x y : A} {u v : B}
      → x ≡ y → u ≡ v → f x u ≡ f y v
cong₂ f refl refl = refl

transport : {A : Set} (P : A → Set) {x y : A} → x ≡ y → P x → P y
transport P refl p = p

record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B fst
open Σ
infixr 4 _,_

_×_ : Set → Set → Set
A × B = Σ A (λ _ → B)
infixr 2 _×_

data _⊎_ (A B : Set) : Set where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}

data Dec (P : Set) : Set where
  yes : P → Dec P
  no  : ¬ P → Dec P

_≟_ : (m n : ℕ) → Dec (m ≡ n)
zero  ≟ zero  = yes refl
zero  ≟ suc n = no (λ ())
suc m ≟ zero  = no (λ ())
suc m ≟ suc n with m ≟ n
... | yes refl = yes refl
... | no ne    = no (λ { refl → ne refl })

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A
infixr 5 _∷_

_++_ : {A : Set} → List A → List A → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

map : {A B : Set} → (A → B) → List A → List B
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs

data All {A : Set} (P : A → Set) : List A → Set where
  []  : All P []
  _∷_ : {x : A} {xs : List A} → P x → All P xs → All P (x ∷ xs)

data Any {A : Set} (P : A → Set) : List A → Set where
  here  : {x : A} {xs : List A} → P x → Any P (x ∷ xs)
  there : {x : A} {xs : List A} → Any P xs → Any P (x ∷ xs)

_∈_ : {A : Set} → A → List A → Set
x ∈ xs = Any (λ y → x ≡ y) xs

all-++ : {A : Set} {P : A → Set} (xs : List A) {ys : List A}
       → All P (xs ++ ys) → All P xs × All P ys
all-++ []       ps       = [] , ps
all-++ (x ∷ xs) (p ∷ ps) with all-++ xs ps
... | l , r = (p ∷ l) , r

any-++ˡ : {A : Set} {P : A → Set} {xs ys : List A} → Any P xs → Any P (xs ++ ys)
any-++ˡ (here p)  = here p
any-++ˡ (there a) = there (any-++ˡ a)

any-++ʳ : {A : Set} {P : A → Set} (xs : List A) {ys : List A} → Any P ys → Any P (xs ++ ys)
any-++ʳ []       a = a
any-++ʳ (x ∷ xs) a = there (any-++ʳ xs a)

all-any : {A : Set} {P Q : A → Set} {xs : List A}
        → All P xs → Any Q xs → Σ A (λ x → P x × Q x)
all-any (p ∷ ps) (here q)  = _ , p , q
all-any (p ∷ ps) (there a) = all-any ps a

-- Pointwise relation between two lists.
data All₂ {A B : Set} (R : A → B → Set) : List A → List B → Set where
  []  : All₂ R [] []
  _∷_ : {x : A} {y : B} {xs : List A} {ys : List B}
      → R x y → All₂ R xs ys → All₂ R (x ∷ xs) (y ∷ ys)

-- Pairwise distinct.
data Distinct : List ℕ → Set where
  []  : Distinct []
  _∷_ : {x : ℕ} {xs : List ℕ} → ¬ (x ∈ xs) → Distinct xs → Distinct (x ∷ xs)

------------------------------------------------------------------------
-- Open terms, occurrence, substitution

data Tm : Set where
  var  : ℕ → Tm
  node : ℕ → List Tm → Tm

mutual
  data Occ (x : ℕ) : Tm → Set where
    here : Occ x (var x)
    arg  : {f : ℕ} {ts : List Tm} → Occs x ts → Occ x (node f ts)

  data Occs (x : ℕ) : List Tm → Set where
    hd : {t : Tm} {ts : List Tm} → Occ x t → Occs x (t ∷ ts)
    tl : {t : Tm} {ts : List Tm} → Occs x ts → Occs x (t ∷ ts)

Subst : Set
Subst = ℕ → Tm

mutual
  sub : Subst → Tm → Tm
  sub σ (var x)     = σ x
  sub σ (node f ts) = node f (subs σ ts)

  subs : Subst → List Tm → List Tm
  subs σ []       = []
  subs σ (t ∷ ts) = sub σ t ∷ subs σ ts

-- Substitutions that agree on the variables of a term agree on the term.
mutual
  sub-ext : (σ τ : Subst) (t : Tm) → (∀ x → Occ x t → σ x ≡ τ x) → sub σ t ≡ sub τ t
  sub-ext σ τ (var x)     e = e x here
  sub-ext σ τ (node f ts) e = cong (node f) (subs-ext σ τ ts (λ x o → e x (arg o)))

  subs-ext : (σ τ : Subst) (ts : List Tm) → (∀ x → Occs x ts → σ x ≡ τ x)
           → subs σ ts ≡ subs τ ts
  subs-ext σ τ []       e = refl
  subs-ext σ τ (t ∷ ts) e =
    cong₂ _∷_ (sub-ext σ τ t (λ x o → e x (hd o))) (subs-ext σ τ ts (λ x o → e x (tl o)))

_∘ˢ_ : Subst → Subst → Subst
(γ ∘ˢ τ) x = sub γ (τ x)

mutual
  sub-comp : (γ τ : Subst) (t : Tm) → sub γ (sub τ t) ≡ sub (γ ∘ˢ τ) t
  sub-comp γ τ (var x)     = refl
  sub-comp γ τ (node f ts) = cong (node f) (subs-comp γ τ ts)

  subs-comp : (γ τ : Subst) (ts : List Tm) → subs γ (subs τ ts) ≡ subs (γ ∘ˢ τ) ts
  subs-comp γ τ []       = refl
  subs-comp γ τ (t ∷ ts) = cong₂ _∷_ (sub-comp γ τ t) (subs-comp γ τ ts)

-- Variables of an instance come from the substituted terms.
mutual
  occ-sub : (τ : Subst) (t : Tm) {y : ℕ} → Occ y (sub τ t) → Σ ℕ (λ x → Occ x t × Occ y (τ x))
  occ-sub τ (var x)     o       = x , here , o
  occ-sub τ (node f ts) (arg o) with occs-sub τ ts o
  ... | x , ox , oy = x , arg ox , oy

  occs-sub : (τ : Subst) (ts : List Tm) {y : ℕ} → Occs y (subs τ ts)
           → Σ ℕ (λ x → Occs x ts × Occ y (τ x))
  occs-sub τ (t ∷ ts) (hd o) with occ-sub τ t o
  ... | x , ox , oy = x , hd ox , oy
  occs-sub τ (t ∷ ts) (tl o) with occs-sub τ ts o
  ... | x , ox , oy = x , tl ox , oy

mutual
  sub-occ : (τ : Subst) (t : Tm) {x y : ℕ} → Occ x t → Occ y (τ x) → Occ y (sub τ t)
  sub-occ τ (var x)     here    oy = oy
  sub-occ τ (node f ts) (arg o) oy = arg (subs-occ τ ts o oy)

  subs-occ : (τ : Subst) (ts : List Tm) {x y : ℕ} → Occs x ts → Occ y (τ x) → Occs y (subs τ ts)
  subs-occ τ (t ∷ ts) (hd o) oy = hd (sub-occ τ t o oy)
  subs-occ τ (t ∷ ts) (tl o) oy = tl (subs-occ τ ts o oy)

Ground : Tm → Set
Ground t = ∀ x → ¬ Occ x t

ground-sub : (γ : Subst) (t : Tm) → (∀ x → Occ x t → Ground (γ x)) → Ground (sub γ t)
ground-sub γ t g y o with occ-sub γ t o
... | x , ox , oy = g x ox y oy

occ-var : {x z : ℕ} → Occ x (var z) → x ≡ z
occ-var here = refl

occs-map-var : {x : ℕ} (ys : List ℕ) → Occs x (map var ys) → x ∈ ys
occs-map-var (y ∷ ys) (hd here) = here refl
occs-map-var (y ∷ ys) (tl o)    = there (occs-map-var ys o)

subs-map-var : (γ : Subst) (ys : List ℕ) → subs γ (map var ys) ≡ map γ ys
subs-map-var γ []       = refl
subs-map-var γ (y ∷ ys) = cong (γ y ∷_) (subs-map-var γ ys)

map-ext : {A B : Set} (f g : A → B) (xs : List A) → (∀ x → x ∈ xs → f x ≡ g x)
        → map f xs ≡ map g xs
map-ext f g []       e = refl
map-ext f g (x ∷ xs) e = cong₂ _∷_ (e x (here refl)) (map-ext f g xs (λ y m → e y (there m)))

------------------------------------------------------------------------
-- Point and simultaneous updates

pick : {P A : Set} → Dec P → A → A → A
pick (yes _) a b = a
pick (no _)  a b = b

-- Replace the variable X by M.
point : ℕ → Tm → Subst
point X M z = pick (X ≟ z) M (var z)

-- Bind ys to ts; an earlier binding of a repeated variable wins.
upd : Subst → List ℕ → List Tm → Subst
upd γ []       ts       z = γ z
upd γ (y ∷ ys) []       z = γ z
upd γ (y ∷ ys) (t ∷ ts) z = pick (y ≟ z) t (upd γ ys ts z)

upd-out : (γ : Subst) (ys : List ℕ) (ts : List Tm) (z : ℕ) → ¬ (z ∈ ys) → upd γ ys ts z ≡ γ z
upd-out γ []       ts       z n = refl
upd-out γ (y ∷ ys) []       z n = refl
upd-out γ (y ∷ ys) (t ∷ ts) z n with y ≟ z
... | yes refl = ⊥-elim (n (here refl))
... | no _     = upd-out γ ys ts z (λ m → n (there m))

upd-in : (γ : Subst) {Q : ℕ → Tm → Set} {ys : List ℕ} {ts : List Tm}
       → All₂ Q ys ts → (z : ℕ) → z ∈ ys → Q z (upd γ ys ts z)
upd-in γ {ys = y ∷ ys} {ts = t ∷ ts} (q ∷ qs) z m with y ≟ z
... | yes refl = q
... | no ne    = upd-in γ qs z (tail m)
  where
    tail : z ∈ (y ∷ ys) → z ∈ ys
    tail (here e)  = ⊥-elim (ne (sym e))
    tail (there m) = m

upd-map : (γ : Subst) {Q : ℕ → Tm → Set} {ys : List ℕ} {ts : List Tm}
        → Distinct ys → All₂ Q ys ts → map (upd γ ys ts) ys ≡ ts
upd-map γ [] [] = refl
upd-map γ {ys = y ∷ ys} {ts = t ∷ ts} (n ∷ d) (q ∷ qs) = cong₂ _∷_ head tail
  where
    head : upd γ (y ∷ ys) (t ∷ ts) y ≡ t
    head with y ≟ y
    ... | yes _ = refl
    ... | no ne = ⊥-elim (ne refl)

    skip : ∀ z → z ∈ ys → upd γ (y ∷ ys) (t ∷ ts) z ≡ upd γ ys ts z
    skip z m with y ≟ z
    ... | yes refl = ⊥-elim (n m)
    ... | no _     = refl

    tail : map (upd γ (y ∷ ys) (t ∷ ts)) ys ≡ ts
    tail = trans (map-ext _ _ ys skip) (upd-map γ d qs)

------------------------------------------------------------------------
-- Signatures, rules, derivations

record Signature : Set where
  field
    out : ℕ → ℕ        -- result sort of each symbol
    ins : ℕ → List ℕ   -- argument sorts of each symbol
    vs  : ℕ → ℕ        -- sort of each eigenvariable

-- Rule schemas reuse `Tm`: in a rule, `var y` is a schema variable of
-- sort `rs y`.
record Rule : Set where
  constructor rule
  field
    prem  : List Tm
    concl : Tm
    rs    : ℕ → ℕ
open Rule

module Calculus (Sg : Signature) (R : List Rule) where
  open Signature Sg

  mutual
    data WS : Tm → ℕ → Set where
      var  : {x : ℕ} → WS (var x) (vs x)
      node : {f s : ℕ} {ts : List Tm} → out f ≡ s → WSs ts (ins f) → WS (node f ts) s

    data WSs : List Tm → List ℕ → Set where
      []  : WSs [] []
      _∷_ : {t : Tm} {s : ℕ} {ts : List Tm} {ss : List ℕ}
          → WS t s → WSs ts ss → WSs (t ∷ ts) (s ∷ ss)

  mutual
    ws-sub : (γ : Subst) {t : Tm} {s : ℕ} → WS t s
           → (∀ x → Occ x t → WS (γ x) (vs x)) → WS (sub γ t) s
    ws-sub γ var        g = g _ here
    ws-sub γ (node e w) g = node e (wss-sub γ w (λ x o → g x (arg o)))

    wss-sub : (γ : Subst) {ts : List Tm} {ss : List ℕ} → WSs ts ss
            → (∀ x → Occs x ts → WS (γ x) (vs x)) → WSs (subs γ ts) ss
    wss-sub γ []       g = []
    wss-sub γ (w ∷ ws) g = ws-sub γ w (λ x o → g x (hd o)) ∷ wss-sub γ ws (λ x o → g x (tl o))

  GroundWS : Tm → ℕ → Set
  GroundWS t s = Ground t × WS t s

  OccR : ℕ → Rule → Set
  OccR y r = Occs y (prem r) ⊎ Occ y (concl r)

  -- Derivations from well-sorted ground instances of the rules.
  data Der : Tm → Set where
    by : {r : Rule} → r ∈ R → (σ : Subst) → (∀ y → OccR y r → GroundWS (σ y) (rs r y))
       → All (λ p → Der (sub σ p)) (prem r) → Der (sub σ (concl r))

  -- The variables of a fact.
  Vars : List Tm → Tm → ℕ → Set
  Vars H J x = Occ x J ⊎ Any (Occ x) H

  -- A well-sorted ground substitution on the variables V.
  GW : Subst → (ℕ → Set) → Set
  GW γ V = ∀ x → V x → GroundWS (γ x) (vs x)

  Valid : List Tm → Tm → Set
  Valid H J = ∀ γ → GW γ (Vars H J) → All (λ h → Der (sub γ h)) H → Der (sub γ J)

  -- An induction hypothesis for case variables ys: J at one of them.
  IH : ℕ → Tm → List ℕ → Tm → Set
  IH X J ys h = Σ ℕ (λ y → (y ∈ ys) × (vs y ≡ vs X) × (h ≡ sub (point X (var y)) J))

  ----------------------------------------------------------------------
  -- The calculus: one constructor per accepted step form.

  mutual
    data _⊢_ : List Tm → Tm → Set where
      -- (hyp N J)
      hyp    : (h : Tm) → (h ∷ []) ⊢ h
      -- A premise reference (N (VAR TERM)...): only hypothesis-free facts.
      inst   : {J : Tm} → [] ⊢ J → (τ : Subst) → (∀ x → Occ x J → WS (τ x) (vs x))
             → [] ⊢ sub τ J
      -- A rule step. Bindings θ are well-sorted (the kernel's sort checks);
      -- premise variables occur in the conclusion or the hypotheses.
      step   : {r : Rule} → r ∈ R → (θ : Subst) → (∀ y → OccR y r → WS (θ y) (rs r y))
             → {H : List Tm} → Prems θ (prem r) H
             → (∀ x → Occs x (subs θ (prem r)) → Vars H (sub θ (concl r)) x)
             → H ⊢ sub θ (concl r)
      -- (induct N X J (CASE...)): one case per constructor of X's sort.
      induct : (X : ℕ) (J : Tm) → Occ X J → ((c : ℕ) → out c ≡ vs X → Case X J c) → [] ⊢ J

    data Prems (θ : Subst) : List Tm → List Tm → Set where
      []  : Prems θ [] []
      _∷_ : {p : Tm} {ps H H′ : List Tm} → H ⊢ sub θ p → Prems θ ps H′
          → Prems θ (p ∷ ps) (H ++ H′)

    -- Case c proves J[X := c(ys)] for distinct fresh ys of c's argument
    -- sorts, assuming only induction hypotheses.
    data Case (X : ℕ) (J : Tm) (c : ℕ) : Set where
      case : (ys : List ℕ) → Distinct ys → map vs ys ≡ ins c → All (λ y → ¬ Occ y J) ys
           → (hs : List Tm) → All (IH X J ys) hs
           → hs ⊢ sub (point X (node c (map var ys))) J → Case X J c

  ----------------------------------------------------------------------
  -- Semantic induction: cases that are valid give every instance.

  record SemCase (X : ℕ) (J : Tm) (c : ℕ) : Set where
    constructor semcase
    field
      ys       : List ℕ
      distinct : Distinct ys
      sorts    : map vs ys ≡ ins c
      fresh    : All (λ y → ¬ Occ y J) ys
      hs       : List Tm
      ihs      : All (IH X J ys) hs
      valid    : Valid hs (sub (point X (node c (map var ys))) J)

  module Induction (X : ℕ) (J : Tm) (oX : Occ X J)
                   (cases : (c : ℕ) → out c ≡ vs X → SemCase X J c) where

    P : Tm → Set
    P t = ∀ γ → GW γ (λ x → Occ x J) → γ X ≡ t → Der (sub γ J)

    -- What the case variables are bound to: well-sorted ground terms, with
    -- the induction claim for those of X's sort.
    Q : ℕ → Tm → Set
    Q y t = GroundWS t (vs y) × (vs y ≡ vs X → P t)

    not-case : {ys : List ℕ} → All (λ y → ¬ Occ y J) ys → ∀ {x} → Occ x J → ¬ (x ∈ ys)
    not-case fresh o m with all-any fresh m
    ... | y , n , refl = n o

    -- Substituting for X a term whose variables are case variables, then
    -- binding those, gives a well-sorted ground instance.
    gw-point : (γ : Subst) {ys : List ℕ} {ts : List Tm} → GW γ (λ x → Occ x J)
             → All (λ y → ¬ Occ y J) ys → All₂ Q ys ts
             → (M : Tm) → (∀ x → Occ x M → x ∈ ys)
             → ∀ x → Occ x (sub (point X M) J) → GroundWS (upd γ ys ts x) (vs x)
    gw-point γ {ys} {ts} gw fresh qs M inM x o with occ-sub (point X M) J o
    ... | z , oz , ox with X ≟ z
    ...   | yes refl = fst (upd-in γ qs x (inM x ox))
    ...   | no _ with occ-var ox
    ...     | refl = transport (λ t → GroundWS t (vs x)) (sym (upd-out γ ys ts x (not-case fresh oz)))
                       (gw x oz)

    mutual
      go : {t : Tm} {s : ℕ} → WS t s → s ≡ vs X → Ground t → P t
      go var eq gr = ⊥-elim (gr _ here)
      go {node c ts} (node e w) eq gr γ gw γX with cases c (trans e eq)
      ... | semcase ys distinct sorts fresh hs ihs valid =
            transport Der same (valid γ′ gw′ (hyps hs ihs))
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

          gw′ : GW γ′ (Vars hs (sub (point X N) J))
          gw′ x (inl o) = gw-point γ gw fresh qs N inN x o
          gw′ x (inr a) with all-any ihs a
          ... | h , (y , m , _ , refl) , o =
                gw-point γ gw fresh qs (var y) (λ { x here → m }) x o

          -- γ′ ∘ point X N agrees with γ on the variables of J.
          same : sub γ′ (sub (point X N) J) ≡ sub γ J
          same = trans (sub-comp γ′ (point X N) J) (sub-ext _ _ J agree)
            where
              agree : ∀ x → Occ x J → sub γ′ (point X N x) ≡ γ x
              agree x o with X ≟ x
              ... | yes refl = trans (cong (node c) (trans (subs-map-var γ′ ys) (upd-map γ distinct qs)))
                                     (sym γX)
              ... | no _ = upd-out γ ys ts x (not-case fresh o)

          -- Each induction hypothesis holds at the smaller argument.
          hyps : (hs : List Tm) → All (IH X J ys) hs → All (λ h → Der (sub γ′ h)) hs
          hyps []       []                               = []
          hyps (h ∷ hs) ((y , m , sy , refl) ∷ rest) =
            transport Der (sym (sub-comp γ′ (point X (var y)) J)) (claim δ gwδ δX)
            ∷ hyps hs rest
            where
              q : Q y (γ′ y)
              q = upd-in γ qs y m

              claim : P (γ′ y)
              claim = snd q sy

              δ : Subst
              δ = γ′ ∘ˢ point X (var y)

              δX : δ X ≡ γ′ y
              δX with X ≟ X
              ... | yes _ = refl
              ... | no ne = ⊥-elim (ne refl)

              gwδ : GW δ (λ x → Occ x J)
              gwδ x o with X ≟ x
              ... | yes refl = transport (GroundWS (γ′ y)) sy (fst q)
              ... | no _ = transport (λ t → GroundWS t (vs x)) (sym (upd-out γ ys ts x (not-case fresh o)))
                             (gw x o)

      gos : {ts : List Tm} {ss : List ℕ} → WSs ts ss → All₂ (λ t s → s ≡ vs X → Ground t → P t) ts ss
      gos []       = []
      gos (w ∷ ws) = go w ∷ gos ws

    induction : Valid [] J
    induction γ gw [] = go (snd g) refl (fst g) γ (λ x o → gw x (inl o)) refl
      where g = gw X (inl oX)

  ----------------------------------------------------------------------
  -- Soundness

  mutual
    sound : {H : List Tm} {J : Tm} → H ⊢ J → Valid H J
    sound (hyp h) γ gw (d ∷ []) = d
    sound (inst {J} d τ wτ) γ gw [] =
      transport Der (sym (sub-comp γ τ J)) (sound d (γ ∘ˢ τ) gw′ [])
      where
        gw′ : GW (γ ∘ˢ τ) (Vars [] J)
        gw′ x (inl o) =
          ground-sub γ (τ x) (λ y oy → fst (gw y (inl (sub-occ τ J o oy))))
          , ws-sub γ (wτ x o) (λ y oy → snd (gw y (inl (sub-occ τ J o oy))))
        gw′ x (inr ())
    sound (step {r} r∈R θ wθ {H} ps side) γ gw hs =
      transport Der (sym (sub-comp γ θ (concl r))) (by r∈R (γ ∘ˢ θ) ok (premises ps side′ gw H⊆ hs))
      where
        J : Tm
        J = sub θ (concl r)

        side′ : ∀ x → Occs x (subs θ (prem r)) → Vars H J x
        side′ = side

        H⊆ : ∀ x → Any (Occ x) H → Vars H J x
        H⊆ x a = inr a

        -- Every variable of a rule variable's binding is a variable of the fact.
        allowed : ∀ y → OccR y r → ∀ x → Occ x (θ y) → Vars H J x
        allowed y (inl o) x ox = side x (subs-occ θ (prem r) o ox)
        allowed y (inr o) x ox = inl (sub-occ θ (concl r) o ox)

        ok : ∀ y → OccR y r → GroundWS ((γ ∘ˢ θ) y) (rs r y)
        ok y o = ground-sub γ (θ y) (λ x ox → fst (gw x (allowed y o x ox)))
               , ws-sub γ (wθ y o) (λ x ox → snd (gw x (allowed y o x ox)))
    sound (induct X J oX cases) = Induction.induction X J oX (λ c e → semantic (cases c e))

    semantic : {X : ℕ} {J : Tm} {c : ℕ} → Case X J c → SemCase X J c
    semantic (case ys d s f hs ihs p) = semcase ys d s f hs ihs (sound p)

    -- Each premise holds at the composed instance, given that its variables
    -- and hypotheses are among the fact's (the predicate V).
    premises : {θ γ : Subst} {ps H : List Tm} {V : ℕ → Set} → Prems θ ps H
             → (∀ x → Occs x (subs θ ps) → V x) → GW γ V → (∀ x → Any (Occ x) H → V x)
             → All (λ h → Der (sub γ h)) H → All (λ p → Der (sub (γ ∘ˢ θ) p)) ps
    premises [] side gw hv hs = []
    premises {θ} {γ} {p ∷ ps} (_∷_ {H = H} {H′} d rest) side gw hv hs with all-++ H hs
    ... | hs₁ , hs₂ =
          transport Der (sub-comp γ θ p) (sound d γ gw₁ hs₁)
          ∷ premises rest (λ x o → side x (tl o)) gw (λ x a → hv x (any-++ʳ H a)) hs₂
      where
        gw₁ : GW γ (Vars H (sub θ p))
        gw₁ x (inl o) = gw x (side x (hd o))
        gw₁ x (inr a) = gw x (hv x (any-++ˡ a))

  -- Main theorem: every well-sorted ground instance of an accepted
  -- hypothesis-free judgment is derivable.
  soundness : {J : Tm} → [] ⊢ J → (γ : Subst) → GW γ (λ x → Occ x J) → Der (sub γ J)
  soundness d γ gw = sound d γ (λ { x (inl o) → gw x o ; x (inr ()) }) []

------------------------------------------------------------------------
-- Example: max l l l, admissible but not derivable, by induction on l.
-- Symbols: z = 0, s = 1 (sort N = 0), max = 2 (a predicate; its "sort" 1
-- is not N). Eigenvariables all have sort N: L = 0, P = 1.

private
  module MaxExample where
    Z : Tm
    Z = node 0 []

    S : Tm → Tm
    S t = node 1 (t ∷ [])

    max : Tm → Tm → Tm → Tm
    max a b c = node 2 (a ∷ b ∷ c ∷ [])

    out : ℕ → ℕ
    out 0 = 0
    out 1 = 0
    out _ = 1

    ins : ℕ → List ℕ
    ins 0 = []
    ins 1 = 0 ∷ []
    ins _ = 0 ∷ 0 ∷ 0 ∷ []

    sig : Signature
    sig = record { out = out ; ins = ins ; vs = λ _ → 0 }

    max-z max-ss : Rule
    max-z  = rule [] (max Z (var 0) (var 0)) (λ _ → 0)
    max-ss = rule (max (var 0) (var 1) (var 2) ∷ []) (max (S (var 0)) (S (var 1)) (S (var 2))) (λ _ → 0)

    rules : List Rule
    rules = max-z ∷ max-ss ∷ []

    open Calculus sig rules

    L P : Tm
    L = var 0
    P = var 1

    idem : Tm
    idem = max L L L

    fresh-P : ¬ Occ 1 idem
    fresh-P (arg (hd ()))
    fresh-P (arg (tl (hd ())))
    fresh-P (arg (tl (tl (hd ()))))
    fresh-P (arg (tl (tl (tl ()))))

    nat : (n : ℕ) → WS (var n) 0
    nat n = var

    -- Base case: max z z z by max.z.
    base : [] ⊢ max Z Z Z
    base = step (here refl) (λ _ → Z) (λ _ _ → node refl []) [] (λ x ())

    -- Step case: from the hypothesis max P P P by max.ss.
    succ : (max P P P ∷ []) ⊢ max (S P) (S P) (S P)
    succ = step (there (here refl)) (λ _ → P) (λ _ _ → var) (hyp (max P P P) ∷ [])
                (λ x o → inr (here (occ o)))
      where
        occ : ∀ {x} → Occs x (max P P P ∷ []) → Occ x (max P P P)
        occ (hd o) = o

    cases : (c : ℕ) → out c ≡ 0 → Case 0 idem c
    cases 0 refl = case [] [] refl [] [] [] base
    cases 1 refl = case (1 ∷ []) ((λ ()) ∷ []) refl (fresh-P ∷ []) (max P P P ∷ [])
                        ((1 , here refl , refl , refl) ∷ []) succ
    cases (suc (suc c)) ()

    idem-proof : [] ⊢ idem
    idem-proof = induct 0 idem (arg (hd here)) cases

    two : Tm
    two = S (S Z)

    two-ok : GroundWS two 0
    two-ok = (λ { x (arg (hd (arg (hd (arg ()))))) ; x (arg (hd (arg (tl ())))) ; x (arg (tl ())) })
           , node refl (node refl (node refl [] ∷ []) ∷ [])

    -- The schematic proof yields the ground fact max 2 2 2.
    max-two : Der (max two two two)
    max-two = soundness idem-proof (λ _ → two) (λ _ _ → two-ok)

------------------------------------------------------------------------
-- Without the premise variable condition a rule step would be unsound.
-- Sort E = 0 has no constructors. Rules: intro: p ?x; elim: p ?x ⊢ q.

private
  module EmptySort where
    p : Tm → Tm
    p t = node 0 (t ∷ [])

    q : Tm
    q = node 1 []

    sig : Signature
    sig = record { out = λ _ → 1 ; ins = λ { 0 → 0 ∷ [] ; _ → [] } ; vs = λ _ → 0 }

    intro elim : Rule
    intro = rule [] (p (var 0)) (λ _ → 0)
    elim  = rule (p (var 0) ∷ []) q (λ _ → 0)

    open Calculus sig (intro ∷ elim ∷ [])

    no-E : (t : Tm) → ¬ GroundWS t 0
    no-E (var x)     (g , _)          = g x here
    no-E (node f ts) (_ , node () _)

    no-der : {t : Tm} → Der t → t ≡ q → ⊥
    no-der (by (here refl) σ ok _) ()
    no-der (by (there (here refl)) σ ok _) _ = no-E (σ 0) (ok 0 (inl (hd (arg (hd here)))))
    no-der (by (there (there ())) σ ok _) _

    no-q : ¬ Der q
    no-q d = no-der d refl

    -- p X is accepted for an eigenvariable X of the empty sort.
    p-X : [] ⊢ p (var 0)
    p-X = step (here refl) var (λ _ _ → var) [] (λ x ())

    -- The elim step from it fails the condition: X occurs in its premise
    -- but in neither the conclusion q nor any hypothesis.
    elim-rejected : ¬ (∀ x → Occs x (subs var (prem elim)) → Vars [] q x)
    elim-rejected side with side 0 (hd (arg (hd here)))
    ... | inl (arg ())
    ... | inr ()

    -- And its conclusion would not be valid.
    q-invalid : ¬ Valid [] q
    q-invalid v = no-q (v var (λ { x (inl (arg ())) ; x (inr ()) }) [])
