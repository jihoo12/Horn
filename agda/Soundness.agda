{-# OPTIONS --safe --without-K #-}
------------------------------------------------------------------------
-- Machine-checked soundness of Horn's certificate acceptance algorithm.
--
-- This file models the checking algorithm of src/kernel.rs on plain trees
-- (the Rust kernel stores the same trees hash-consed) and proves:
--
--   accepts R goals c ≡ just tt  →  every goal has a derivation from
--                                    ground instances of the rules R.
--
-- The model covers stated and inferred conclusions, explicit variable
-- bindings, schema matching with one consistent assignment, earlier-only
-- premise references, and exact goal results. Names, sorts, abbreviations
-- (`def`), parsing, and the hash-consing refinement are outside the model;
-- see docs/TRUST.md. No library is imported: everything used is below.
------------------------------------------------------------------------
module Soundness where

------------------------------------------------------------------------
-- Prelude

data ⊥ : Set where

⊥-elim : {A : Set} → ⊥ → A
⊥-elim ()

record ⊤ : Set where
  constructor tt

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x
infix 4 _≡_
{-# BUILTIN EQUALITY _≡_ #-}

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
infixr 4 _,_

_×_ : Set → Set → Set
A × B = Σ A (λ _ → B)
infixr 2 _×_

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A
infixr 5 _∷_

_++_ : {A : Set} → List A → List A → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just    : A → Maybe A

nothing≢just : {A : Set} {x : A} → nothing ≡ just x → ⊥
nothing≢just ()

just-inj : {A : Set} {x y : A} → just x ≡ just y → x ≡ y
just-inj refl = refl

_>>=_ : {A B : Set} → Maybe A → (A → Maybe B) → Maybe B
nothing >>= f = nothing
just x  >>= f = f x
infixl 1 _>>=_

bind-inv : {A B : Set} (m : Maybe A) (f : A → Maybe B) {y : B}
         → (m >>= f) ≡ just y → Σ A (λ x → (m ≡ just x) × (f x ≡ just y))
bind-inv nothing  f ()
bind-inv (just x) f eq = x , refl , eq

data Dec (P : Set) : Set where
  yes : P → Dec P
  no  : (P → ⊥) → Dec P

when : {P A : Set} → Dec P → A → Maybe A
when (yes _) a = just a
when (no _)  a = nothing

when-inv : {P A : Set} (d : Dec P) {a b : A} → when d a ≡ just b → P × (a ≡ b)
when-inv (yes p) refl = p , refl
when-inv (no _)  ()

data All {A : Set} (P : A → Set) : List A → Set where
  []  : All P []
  _∷_ : {x : A} {xs : List A} → P x → All P xs → All P (x ∷ xs)

lookup : {A : Set} → List A → ℕ → Maybe A
lookup []       n       = nothing
lookup (x ∷ xs) zero    = just x
lookup (x ∷ xs) (suc n) = lookup xs n

all-lookup : {A : Set} {P : A → Set} {xs : List A} (n : ℕ) {x : A}
           → All P xs → lookup xs n ≡ just x → P x
all-lookup n       []       ()
all-lookup zero    (p ∷ ps) refl = p
all-lookup (suc n) (p ∷ ps) eq   = all-lookup n ps eq

all-snoc : {A : Set} {P : A → Set} {xs : List A} {x : A}
         → All P xs → P x → All P (xs ++ (x ∷ []))
all-snoc []       px = px ∷ []
all-snoc (p ∷ ps) px = p ∷ all-snoc ps px

------------------------------------------------------------------------
-- Ground terms (judgments are terms headed by a predicate) and schemas

data Term : Set where
  node : ℕ → List Term → Term

data Pat : Set where
  var : ℕ → Pat
  app : ℕ → List Pat → Pat

_≟ℕ_ : (m n : ℕ) → Dec (m ≡ n)
zero  ≟ℕ zero  = yes refl
zero  ≟ℕ suc n = no (λ ())
suc m ≟ℕ zero  = no (λ ())
suc m ≟ℕ suc n with m ≟ℕ n
... | yes refl = yes refl
... | no ne    = no (λ { refl → ne refl })

mutual
  _≟_ : (s t : Term) → Dec (s ≡ t)
  node f ss ≟ node g ts with f ≟ℕ g | ss ≟* ts
  ... | yes refl | yes refl = yes refl
  ... | no ne    | _        = no (λ { refl → ne refl })
  ... | yes _    | no ne    = no (λ { refl → ne refl })

  _≟*_ : (ss ts : List Term) → Dec (ss ≡ ts)
  []       ≟* []       = yes refl
  []       ≟* (t ∷ ts) = no (λ ())
  (s ∷ ss) ≟* []       = no (λ ())
  (s ∷ ss) ≟* (t ∷ ts) with s ≟ t | ss ≟* ts
  ... | yes refl | yes refl = yes refl
  ... | no ne    | _        = no (λ { refl → ne refl })
  ... | yes _    | no ne    = no (λ { refl → ne refl })

------------------------------------------------------------------------
-- Partial assignments of schema variables

Env : Set
Env = ℕ → Maybe Term

empty : Env
empty _ = nothing

sel : {P A : Set} → Dec P → A → A → A
sel (yes _) a b = a
sel (no _)  a b = b

_[_↦_] : Env → ℕ → Term → Env
(b [ x ↦ t ]) y = sel (x ≟ℕ y) (just t) (b y)

-- `c` extends `b`: every binding of `b` is kept.
record _⊑_ (b c : Env) : Set where
  constructor keeps
  field
    kept : ∀ {x t} → b x ≡ just t → c x ≡ just t
open _⊑_

⊑-refl : {b : Env} → b ⊑ b
⊑-refl = keeps (λ e → e)

⊑-trans : {a b c : Env} → a ⊑ b → b ⊑ c → a ⊑ c
⊑-trans p q = keeps (λ e → kept q (kept p e))

upd-same : (b : Env) (x : ℕ) (t : Term) → (b [ x ↦ t ]) x ≡ just t
upd-same b x t with x ≟ℕ x
... | yes _ = refl
... | no ne = ⊥-elim (ne refl)

upd-ext : (b : Env) (x : ℕ) (t : Term) → b x ≡ nothing → b ⊑ (b [ x ↦ t ])
upd-ext b x t free = keeps lemma
  where
    lemma : ∀ {y s} → b y ≡ just s → (b [ x ↦ t ]) y ≡ just s
    lemma {y} e with x ≟ℕ y
    ... | yes refl = ⊥-elim (nothing≢just (trans (sym free) e))
    ... | no _     = e

------------------------------------------------------------------------
-- Instantiation: partial (as in the kernel) and total (as in derivations)

mutual
  inst : Env → Pat → Maybe Term
  inst b (var x)    = b x
  inst b (app f ps) = insts b ps >>= λ ts → just (node f ts)

  insts : Env → List Pat → Maybe (List Term)
  insts b []       = just []
  insts b (p ∷ ps) = inst b p >>= λ t → insts b ps >>= λ ts → just (t ∷ ts)

cons-ok : {c : Env} (p : Pat) (ps : List Pat) {t : Term} {ts : List Term}
        → inst c p ≡ just t → insts c ps ≡ just ts → insts c (p ∷ ps) ≡ just (t ∷ ts)
cons-ok p ps e₁ e₂ rewrite e₁ | e₂ = refl

app-ok : {c : Env} (f : ℕ) (ps : List Pat) {ts : List Term}
       → insts c ps ≡ just ts → inst c (app f ps) ≡ just (node f ts)
app-ok f ps e rewrite e = refl

mutual
  inst-mono : {b c : Env} → b ⊑ c → (p : Pat) {t : Term}
            → inst b p ≡ just t → inst c p ≡ just t
  inst-mono ext (var x) e = kept ext e
  inst-mono {b} ext (app f ps) e with bind-inv (insts b ps) (λ ts → just (node f ts)) e
  ... | ts , e₁ , refl = app-ok f ps (insts-mono ext ps e₁)

  insts-mono : {b c : Env} → b ⊑ c → (ps : List Pat) {ts : List Term}
             → insts b ps ≡ just ts → insts c ps ≡ just ts
  insts-mono ext [] e = e
  insts-mono {b} ext (p ∷ ps) e
    with bind-inv (inst b p) (λ t → insts b ps >>= λ ts → just (t ∷ ts)) e
  ... | t , e₁ , e₂ with bind-inv (insts b ps) (λ ts → just (t ∷ ts)) e₂
  ...   | ts , e₃ , refl = cons-ok p ps (inst-mono ext p e₁) (insts-mono ext ps e₃)

mutual
  subst : (ℕ → Term) → Pat → Term
  subst σ (var x)    = σ x
  subst σ (app f ps) = node f (substs σ ps)

  substs : (ℕ → Term) → List Pat → List Term
  substs σ []       = []
  substs σ (p ∷ ps) = subst σ p ∷ substs σ ps

fromMaybe : Maybe Term → Term
fromMaybe nothing  = node zero []
fromMaybe (just t) = t

total : Env → ℕ → Term
total b x = fromMaybe (b x)

mutual
  inst-subst : (b : Env) (p : Pat) {t : Term} → inst b p ≡ just t → subst (total b) p ≡ t
  inst-subst b (var x) e = cong fromMaybe e
  inst-subst b (app f ps) e with bind-inv (insts b ps) (λ ts → just (node f ts)) e
  ... | ts , e₁ , refl = cong (node f) (insts-subst b ps e₁)

  insts-subst : (b : Env) (ps : List Pat) {ts : List Term}
              → insts b ps ≡ just ts → substs (total b) ps ≡ ts
  insts-subst b [] refl = refl
  insts-subst b (p ∷ ps) e
    with bind-inv (inst b p) (λ t → insts b ps >>= λ ts → just (t ∷ ts)) e
  ... | t , e₁ , e₂ with bind-inv (insts b ps) (λ ts → just (t ∷ ts)) e₂
  ...   | ts , e₃ , refl = cong₂ _∷_ (inst-subst b p e₁) (insts-subst b ps e₃)

------------------------------------------------------------------------
-- Matching against one consistent assignment

bindVar : ℕ → Term → Env → Maybe Term → Maybe Env
bindVar x t b nothing  = just (b [ x ↦ t ])
bindVar x t b (just u) = when (u ≟ t) b

mutual
  match : Pat → Term → Env → Maybe Env
  match (var x)    t           b = bindVar x t b (b x)
  match (app f ps) (node g ts) b = when (f ≟ℕ g) b >>= matchs ps ts

  matchs : List Pat → List Term → Env → Maybe Env
  matchs []       []       b = just b
  matchs (p ∷ ps) (t ∷ ts) b = match p t b >>= matchs ps ts
  matchs []       (t ∷ ts) b = nothing
  matchs (p ∷ ps) []       b = nothing

bindVar-ok : (x : ℕ) (t : Term) (b : Env) (m : Maybe Term) {c : Env}
           → b x ≡ m → bindVar x t b m ≡ just c → (b ⊑ c) × (c x ≡ just t)
bindVar-ok x t b nothing  bx refl = upd-ext b x t bx , upd-same b x t
bindVar-ok x t b (just u) bx eq with when-inv (u ≟ t) eq
... | u≡t , refl = ⊑-refl , trans bx (cong just u≡t)

mutual
  -- A successful match extends the assignment and instantiates the pattern
  -- to exactly the matched term.
  match-ok : (p : Pat) (t : Term) (b : Env) {c : Env}
           → match p t b ≡ just c → (b ⊑ c) × (inst c p ≡ just t)
  match-ok (var x) t b eq with bindVar-ok x t b (b x) refl eq
  ... | ext , e = ext , e
  match-ok (app f ps) (node g ts) b eq with bind-inv (when (f ≟ℕ g) b) (matchs ps ts) eq
  ... | b′ , e₁ , e₂ with when-inv (f ≟ℕ g) e₁
  ...   | refl , refl with matchs-ok ps ts b e₂
  ...     | ext , e = ext , app-ok f ps e

  matchs-ok : (ps : List Pat) (ts : List Term) (b : Env) {c : Env}
            → matchs ps ts b ≡ just c → (b ⊑ c) × (insts c ps ≡ just ts)
  matchs-ok [] [] b refl = ⊑-refl , refl
  matchs-ok (p ∷ ps) (t ∷ ts) b eq with bind-inv (match p t b) (matchs ps ts) eq
  ... | c₁ , e₁ , e₂ with match-ok p t b e₁ | matchs-ok ps ts c₁ e₂
  ...   | ext₁ , ok₁ | ext₂ , ok₂ =
          ⊑-trans ext₁ ext₂ , cons-ok p ps (inst-mono ext₂ p ok₁) ok₂
  matchs-ok []       (t ∷ ts) b ()
  matchs-ok (p ∷ ps) []       b ()

------------------------------------------------------------------------
-- Theories and derivations

record Rule : Set where
  constructor rule
  field
    premises   : List Pat
    conclusion : Pat
open Rule

-- Derivations from ground instances of the rules of R.
data Derivable (R : List Rule) : Term → Set where
  by : (n : ℕ) {r : Rule} → lookup R n ≡ just r → (σ : ℕ → Term)
     → All (λ p → Derivable R (subst σ p)) (premises r)
     → Derivable R (subst σ (conclusion r))

------------------------------------------------------------------------
-- The checking algorithm

record Step : Set where
  constructor step
  field
    ruleIx : ℕ
    refs   : List ℕ
    binds  : List (ℕ × Term)   -- explicit `(?var TERM)` bindings
    stated : Maybe Term        -- stated conclusion, or inferred if nothing
open Step

bindFresh : ℕ → Term → Env → Maybe Term → Maybe Env
bindFresh x t b nothing  = just (b [ x ↦ t ])
bindFresh x t b (just _) = nothing

bindAll : List (ℕ × Term) → Env → Maybe Env
bindAll []             b = just b
bindAll ((x , t) ∷ bs) b = bindFresh x t b (b x) >>= bindAll bs

premisesMatch : List Pat → List ℕ → List Term → Env → Maybe Env
premisesMatch []       []       fs b = just b
premisesMatch (p ∷ ps) (n ∷ ns) fs b =
  lookup fs n >>= λ f → match p f b >>= premisesMatch ps ns fs
premisesMatch []       (n ∷ ns) fs b = nothing
premisesMatch (p ∷ ps) []       fs b = nothing

conclude : Pat → Maybe Term → Env → Maybe Env
conclude p nothing  b = just b
conclude p (just j) b = match p j b

answer : Maybe Term → Maybe Term → Maybe Term
answer (just j) m = just j
answer nothing  m = m

stage₄ : Step → Rule → Env → Maybe Term
stage₄ s r b₂ = answer (stated s) (inst b₂ (conclusion r))

stage₃ : List Term → Step → Rule → Env → Maybe Term
stage₃ fs s r b₁ = premisesMatch (premises r) (refs s) fs b₁ >>= stage₄ s r

stage₂ : List Term → Step → Rule → Env → Maybe Term
stage₂ fs s r b₀ = conclude (conclusion r) (stated s) b₀ >>= stage₃ fs s r

stage₁ : List Term → Step → Rule → Maybe Term
stage₁ fs s r = bindAll (binds s) empty >>= stage₂ fs s r

-- `fs` are the conclusions of earlier steps; references can reach only them.
checkStep : List Rule → List Term → Step → Maybe Term
checkStep R fs s = lookup R (ruleIx s) >>= stage₁ fs s

checkSteps : List Rule → List Term → List Step → Maybe (List Term)
checkSteps R fs []       = just fs
checkSteps R fs (s ∷ ss) = checkStep R fs s >>= λ t → checkSteps R (fs ++ (t ∷ [])) ss

-- The i-th result names the step proving the i-th goal.
checkGoals : List Term → List Term → List ℕ → Maybe ⊤
checkGoals fs []       []       = just tt
checkGoals fs (g ∷ gs) (n ∷ ns) =
  lookup fs n >>= λ f → when (f ≟ g) tt >>= λ _ → checkGoals fs gs ns
checkGoals fs []       (n ∷ ns) = nothing
checkGoals fs (g ∷ gs) []       = nothing

record Certificate : Set where
  constructor certificate
  field
    steps   : List Step
    results : List ℕ
open Certificate

accepts : List Rule → List Term → Certificate → Maybe ⊤
accepts R goals c = checkSteps R [] (steps c) >>= λ fs → checkGoals fs goals (results c)

------------------------------------------------------------------------
-- Soundness

premises-ok : (R : List Rule) (ps : List Pat) (ns : List ℕ) (fs : List Term) (b : Env)
              {c : Env} → All (Derivable R) fs → premisesMatch ps ns fs b ≡ just c
            → (b ⊑ c) × All (λ p → Σ Term (λ f → (inst c p ≡ just f) × Derivable R f)) ps
premises-ok R [] [] fs b D refl = ⊑-refl , []
premises-ok R (p ∷ ps) (n ∷ ns) fs b D eq
  with bind-inv (lookup fs n) (λ f → match p f b >>= premisesMatch ps ns fs) eq
... | f , e₁ , e₂ with bind-inv (match p f b) (premisesMatch ps ns fs) e₂
...   | c₁ , e₃ , e₄ with match-ok p f b e₃ | premises-ok R ps ns fs c₁ D e₄
...     | ext₁ , ok₁ | ext₂ , rest =
          ⊑-trans ext₁ ext₂ , ((f , inst-mono ext₂ p ok₁ , all-lookup n D e₁) ∷ rest)
premises-ok R []       (n ∷ ns) fs b D ()
premises-ok R (p ∷ ps) []       fs b D ()

derivations : (R : List Rule) (c : Env) (ps : List Pat)
            → All (λ p → Σ Term (λ f → (inst c p ≡ just f) × Derivable R f)) ps
            → All (λ p → Derivable R (subst (total c) p)) ps
derivations R c []       []                   = []
derivations R c (p ∷ ps) ((f , e , d) ∷ rest) =
  transport (Derivable R) (sym (inst-subst c p e)) d ∷ derivations R c ps rest

conclusion-ok : (p : Pat) (st : Maybe Term) (b₀ b₁ b₂ : Env) {t : Term}
              → conclude p st b₀ ≡ just b₁ → b₁ ⊑ b₂
              → answer st (inst b₂ p) ≡ just t → inst b₂ p ≡ just t
conclusion-ok p nothing  b₀ b₁ b₂ e ext a = a
conclusion-ok p (just j) b₀ b₁ b₂ e ext refl with match-ok p j b₀ e
... | _ , ok = inst-mono ext p ok

step-sound : (R : List Rule) (fs : List Term) (s : Step) {t : Term}
           → All (Derivable R) fs → checkStep R fs s ≡ just t → Derivable R t
step-sound R fs s D eq with bind-inv (lookup R (ruleIx s)) (stage₁ fs s) eq
... | r , er , e₁ with bind-inv (bindAll (binds s) empty) (stage₂ fs s r) e₁
...   | b₀ , _ , e₂ with bind-inv (conclude (conclusion r) (stated s) b₀) (stage₃ fs s r) e₂
...     | b₁ , ec , e₃ with bind-inv (premisesMatch (premises r) (refs s) fs b₁) (stage₄ s r) e₃
...       | b₂ , ep , ea with premises-ok R (premises r) (refs s) fs b₁ D ep
...         | ext , prem =
              transport (Derivable R)
                (inst-subst b₂ (conclusion r) (conclusion-ok (conclusion r) (stated s) b₀ b₁ b₂ ec ext ea))
                (by (ruleIx s) er (total b₂) (derivations R b₂ (premises r) prem))

steps-sound : (R : List Rule) (fs : List Term) (ss : List Step) {gs : List Term}
            → All (Derivable R) fs → checkSteps R fs ss ≡ just gs → All (Derivable R) gs
steps-sound R fs [] D refl = D
steps-sound R fs (s ∷ ss) D eq
  with bind-inv (checkStep R fs s) (λ t → checkSteps R (fs ++ (t ∷ [])) ss) eq
... | t , e₁ , e₂ = steps-sound R (fs ++ (t ∷ [])) ss (all-snoc D (step-sound R fs s D e₁)) e₂

goals-sound : (R : List Rule) (fs gs : List Term) (ns : List ℕ)
            → All (Derivable R) fs → checkGoals fs gs ns ≡ just tt → All (Derivable R) gs
goals-sound R fs [] [] D refl = []
goals-sound R fs (g ∷ gs) (n ∷ ns) D eq
  with bind-inv (lookup fs n) (λ f → when (f ≟ g) tt >>= λ _ → checkGoals fs gs ns) eq
... | f , e₁ , e₂ with bind-inv (when (f ≟ g) tt) (λ _ → checkGoals fs gs ns) e₂
...   | _ , e₃ , e₄ with when-inv (f ≟ g) e₃
...     | refl , _ = all-lookup n D e₁ ∷ goals-sound R fs gs ns D e₄
goals-sound R fs []       (n ∷ ns) D ()
goals-sound R fs (g ∷ gs) []       D ()

-- Main theorem: an accepted certificate derives every requested goal.
soundness : (R : List Rule) (goals : List Term) (c : Certificate)
          → accepts R goals c ≡ just tt → All (Derivable R) goals
soundness R goals c eq
  with bind-inv (checkSteps R [] (steps c)) (λ fs → checkGoals fs goals (results c)) eq
... | fs , e₁ , e₂ = goals-sound R fs goals (results c) (steps-sound R [] (steps c) [] e₁) e₂

------------------------------------------------------------------------
-- The examples/nat.horn theory, checked by evaluation.
-- Symbols: z = 0, s = 1, even = 2. Variables: ?n = 0.

private
  Z : Term
  Z = node 0 []

  S : Term → Term
  S t = node 1 (t ∷ [])

  even : Term → Term
  even t = node 2 (t ∷ [])

  nat : List Rule
  nat = rule [] (app 2 (app 0 [] ∷ []))
      ∷ rule (app 2 (var 0 ∷ []) ∷ []) (app 2 (app 1 (app 1 (var 0 ∷ []) ∷ []) ∷ []))
      ∷ []

  four : Term
  four = even (S (S (S (S Z))))

  -- Stated conclusions, as in examples/nat.proof.
  ordinary : Certificate
  ordinary = certificate
    ( step 0 [] [] (just (even Z))
    ∷ step 1 (0 ∷ []) [] (just (even (S (S Z))))
    ∷ step 1 (1 ∷ []) [] (just four)
    ∷ []) (2 ∷ [])

  -- Compact form: every conclusion is inferred.
  compact : Certificate
  compact = certificate
    (step 0 [] [] nothing ∷ step 1 (0 ∷ []) [] nothing ∷ step 1 (1 ∷ []) [] nothing ∷ [])
    (2 ∷ [])

  -- An inferred chain that proves a different judgment than requested.
  short : Certificate
  short = certificate (step 0 [] [] nothing ∷ step 1 (0 ∷ []) [] nothing ∷ []) (1 ∷ [])

  ordinary-accepted : accepts nat (four ∷ []) ordinary ≡ just tt
  ordinary-accepted = refl

  compact-accepted : accepts nat (four ∷ []) compact ≡ just tt
  compact-accepted = refl

  short-rejected : accepts nat (four ∷ []) short ≡ nothing
  short-rejected = refl

  four-is-even : All (Derivable nat) (four ∷ [])
  four-is-even = soundness nat (four ∷ []) compact compact-accepted
