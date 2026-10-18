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
-- Module `Calculus.Algorithm` then models the checking algorithm itself, as
-- Soundness.agda does for ground certificates: steps are checked in order,
-- references are step indices, rule bindings are found by matching,
-- instance substitutions are sort-checked, and induction cases are matched
-- against a list of each sort's constructors. `accepts-sound` proves that an
-- accepted certificate makes every well-sorted ground instance of every
-- goal derivable. It makes the same checks as src/schematic.rs and no
-- others: that rule bindings are well-sorted is proved from the theory's
-- well-formedness (`RuleWF`, which the kernel's theory parser checks) and
-- the invariant that every fact is well-sorted. Differences: hypotheses are
-- kept as judgments rather than step indices, and parsing, names, `def` and
-- hash-consing are not modelled.
-- No library is imported.
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
open Σ
infixr 4 _,_

_×_ : Set → Set → Set
A × B = Σ A (λ _ → B)
infixr 2 _×_

data _⊎_ (A B : Set) : Set where
  inl : A → A ⊎ B
  inr : B → A ⊎ B
infixr 1 _⊎_

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}

data Dec (P : Set) : Set where
  yes : P → Dec P
  no  : ¬ P → Dec P

data Bool : Set where
  false true : Bool
{-# BUILTIN BOOL  Bool  #-}
{-# BUILTIN FALSE false #-}
{-# BUILTIN TRUE  true  #-}

-- Equality of naturals. Agda evaluates it in one step on its binary
-- representation of numerals; the proofs below are ordinary inductions.
_==_ : ℕ → ℕ → Bool
zero  == zero  = true
suc m == suc n = m == n
_     == _     = false
{-# BUILTIN NATEQUALS _==_ #-}

==-sound : (m n : ℕ) → (m == n) ≡ true → m ≡ n
==-sound zero    zero    e = refl
==-sound (suc m) (suc n) e = cong suc (==-sound m n e)
==-sound zero    (suc n) ()
==-sound (suc m) zero    ()

==-refl : (m : ℕ) → (m == m) ≡ true
==-refl zero    = refl
==-refl (suc m) = ==-refl m

-- Deciding with `_==_` makes the yes/no answer cheap to compute; checking a
-- certificate by evaluation never needs the proofs inside.
_≟_ : (m n : ℕ) → Dec (m ≡ n)
m ≟ n = decide (m == n) refl
  where
    decide : (b : Bool) → (m == n) ≡ b → Dec (m ≡ n)
    decide true  e = yes (==-sound m n e)
    decide false e = no (λ { refl → false≢true (trans (sym e) (==-refl m)) })
      where
        false≢true : false ≡ true → ⊥
        false≢true ()

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

concat : {A : Set} → List (List A) → List A
concat []         = []
concat (xs ∷ xss) = xs ++ concat xss

-- A stream of naturals, the compact form of an exported certificate. It
-- has no implicit arguments, so Agda elaborates long literals quickly.
data Code : Set where
  ε    : Code
  _▸_  : ℕ → Code → Code
  -- `pack k w`: k numbers, least significant first, as base-2³² digits
  -- of w. One literal holds many numbers, which Agda elaborates as one.
  pack : ℕ → ℕ → Code → Code
infixr 5 _▸_

_⊕_ : Code → Code → Code
ε          ⊕ d = d
(n ▸ c)    ⊕ d = n ▸ (c ⊕ d)
(pack k w c) ⊕ d = pack k w (c ⊕ d)
infixr 4 _⊕_

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
-- Partiality and decisions used by the algorithmic model

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just    : A → Maybe A

_>>=_ : {A B : Set} → Maybe A → (A → Maybe B) → Maybe B
nothing >>= f = nothing
just x  >>= f = f x
infixl 1 _>>=_

bind-inv : {A B : Set} (m : Maybe A) (f : A → Maybe B) {y : B}
         → (m >>= f) ≡ just y → Σ A (λ x → (m ≡ just x) × (f x ≡ just y))
bind-inv nothing  f ()
bind-inv (just x) f eq = x , refl , eq

when : {P A : Set} → Dec P → A → Maybe A
when (yes _) a = just a
when (no _)  a = nothing

when-inv : {P A : Set} (d : Dec P) {a b : A} → when d a ≡ just b → P × (a ≡ b)
when-inv (yes p) refl = p , refl
when-inv (no _)  ()

record ⊤ : Set where
  constructor tt

nothing≢just : {A : Set} {x : A} → nothing ≡ just x → ⊥
nothing≢just ()

_×?_ : {A B : Set} → Dec A → Dec B → Dec (A × B)
yes a ×? yes b = yes (a , b)
no na ×? _     = no (λ p → na (fst p))
yes _ ×? no nb = no (λ p → nb (snd p))
infixr 2 _×?_

lookup : {A : Set} → List A → ℕ → Maybe A
lookup []       n       = nothing
lookup (x ∷ xs) zero    = just x
lookup (x ∷ xs) (suc n) = lookup xs n

all-lookup : {A : Set} {P : A → Set} {xs : List A} (n : ℕ) {x : A}
           → All P xs → lookup xs n ≡ just x → P x
all-lookup n       []       ()
all-lookup zero    (p ∷ ps) refl = p
all-lookup (suc n) (p ∷ ps) eq   = all-lookup n ps eq

lookup-∈ : {A : Set} (xs : List A) (n : ℕ) {x : A} → lookup xs n ≡ just x → x ∈ xs
lookup-∈ []       n       ()
lookup-∈ (y ∷ xs) zero    refl = here refl
lookup-∈ (y ∷ xs) (suc n) e    = there (lookup-∈ xs n e)

all-snoc : {A : Set} {P : A → Set} {xs : List A} {x : A}
         → All P xs → P x → All P (xs ++ (x ∷ []))
all-snoc []       px = px ∷ []
all-snoc (p ∷ ps) px = p ∷ all-snoc ps px

-- Halving and parity of naturals; Agda evaluates these builtins in one
-- step on its binary representation of numerals.
div-helper : (k m n j : ℕ) → ℕ
div-helper k m zero    j       = k
div-helper k m (suc n) zero    = div-helper (suc k) m n m
div-helper k m (suc n) (suc j) = div-helper k m n j
{-# BUILTIN NATDIVSUCAUX div-helper #-}

mod-helper : (k m n j : ℕ) → ℕ
mod-helper k m zero    j       = k
mod-helper k m (suc n) zero    = mod-helper 0 m n m
mod-helper k m (suc n) (suc j) = mod-helper (suc k) m n j
{-# BUILTIN NATMODSUCAUX mod-helper #-}

half : ℕ → ℕ
half n = div-helper 0 1 n 1

even : ℕ → Bool
even n = mod-helper 0 1 n 1 == 0

if_then_else_ : {A : Set} → Bool → A → A → A
if true  then a else b = a
if false then a else b = b

-- Braun trees: element 0 at the root, odd positions on the left and even
-- ones on the right, so access and insertion at the end take logarithmic
-- time. Soundness only uses that every element satisfies the invariant;
-- that position i holds the i-th inserted element is what makes the model
-- accept the certificates the Rust code accepts.
data Tree (A : Set) : Set where
  leaf : Tree A
  bin  : A → Tree A → Tree A → Tree A

lookupT : {A : Set} → Tree A → ℕ → Maybe A
lookupT leaf        i       = nothing
lookupT (bin x l r) zero    = just x
lookupT (bin x l r) (suc i) = if even i then lookupT l (half i) else lookupT r (half i)

insertT : {A : Set} → Tree A → ℕ → A → Tree A
insertT leaf        i       a = bin a leaf leaf
insertT (bin x l r) zero    a = bin x l r
insertT (bin x l r) (suc i) a =
  if even i then bin x (insertT l (half i) a) r else bin x l (insertT r (half i) a)

data AllT {A : Set} (P : A → Set) : Tree A → Set where
  leaf : AllT P leaf
  bin  : {x : A} {l r : Tree A} → P x → AllT P l → AllT P r → AllT P (bin x l r)

allT-lookup : {A : Set} {P : A → Set} {t : Tree A} → AllT P t → (i : ℕ) {x : A}
            → lookupT t i ≡ just x → P x
allT-lookup leaf          i       ()
allT-lookup (bin p al ar) zero    refl = p
allT-lookup (bin p al ar) (suc i) e with even i
... | true  = allT-lookup al (half i) e
... | false = allT-lookup ar (half i) e

allT-insert : {A : Set} {P : A → Set} {t : Tree A} {a : A} → AllT P t → P a → (i : ℕ)
            → AllT P (insertT t i a)
allT-insert leaf          pa i       = bin pa leaf leaf
allT-insert (bin p al ar) pa zero    = bin p al ar
allT-insert (bin p al ar) pa (suc i) with even i
... | true  = bin p (allT-insert al pa (half i)) ar
... | false = bin p al (allT-insert ar pa (half i))

allT-map : {A : Set} {P Q : A → Set} → (∀ {x} → P x → Q x) → {t : Tree A} → AllT P t → AllT Q t
allT-map f leaf          = leaf
allT-map f (bin p l r)   = bin (f p) (allT-map f l) (allT-map f r)

private
  -- Position i holds the i-th inserted element.
  tree-of : ℕ → Tree ℕ
  tree-of zero    = leaf
  tree-of (suc n) = insertT (tree-of n) n n

  positions : lookupT (tree-of 10) 0 ≡ just 0 × lookupT (tree-of 10) 5 ≡ just 5
            × lookupT (tree-of 10) 9 ≡ just 9 × lookupT (tree-of 10) 10 ≡ nothing
  positions = refl , refl , refl , refl

all-∈ : {A : Set} {P : A → Set} {xs : List A} {x : A} → All P xs → x ∈ xs → P x
all-∈ (p ∷ ps) (here refl) = p
all-∈ (p ∷ ps) (there m)   = all-∈ ps m

all? : {A : Set} {P : A → Set} → (∀ x → Dec (P x)) → (xs : List A) → Dec (All P xs)
all? p? []       = yes []
all? p? (x ∷ xs) with p? x | all? p? xs
... | yes p | yes ps = yes (p ∷ ps)
... | no np | _      = no (λ { (p ∷ _) → np p })
... | yes _ | no nps = no (λ { (_ ∷ ps) → nps ps })

any? : {A : Set} {P : A → Set} → (∀ x → Dec (P x)) → (xs : List A) → Dec (Any P xs)
any? p? []       = no (λ ())
any? p? (x ∷ xs) with p? x | any? p? xs
... | yes p | _      = yes (here p)
... | no _  | yes a  = yes (there a)
... | no np | no na  = no (λ { (here p) → np p ; (there a) → na a })

_∈?_ : (x : ℕ) (xs : List ℕ) → Dec (x ∈ xs)
x ∈? xs = any? (λ y → x ≟ y) xs

not? : {P : Set} → Dec P → Dec (¬ P)
not? (yes p) = no (λ n → n p)
not? (no n)  = yes n

_≟ℓ_ : (xs ys : List ℕ) → Dec (xs ≡ ys)
[]       ≟ℓ []       = yes refl
[]       ≟ℓ (y ∷ ys) = no (λ ())
(x ∷ xs) ≟ℓ []       = no (λ ())
(x ∷ xs) ≟ℓ (y ∷ ys) with x ≟ y | xs ≟ℓ ys
... | yes refl | yes refl = yes refl
... | no ne    | _        = no (λ { refl → ne refl })
... | yes _    | no ne    = no (λ { refl → ne refl })

distinct? : (xs : List ℕ) → Dec (Distinct xs)
distinct? []       = yes []
distinct? (x ∷ xs) with x ∈? xs | distinct? xs
... | no n  | yes d = yes (n ∷ d)
... | yes m | _     = no (λ { (n ∷ _) → n m })
... | no _  | no nd = no (λ { (_ ∷ d) → nd d })

∈-++⁻ : {A : Set} {x : A} (xs : List A) {ys : List A} → x ∈ (xs ++ ys) → (x ∈ xs) ⊎ (x ∈ ys)
∈-++⁻ []       m         = inr m
∈-++⁻ (y ∷ xs) (here e)  = inl (here e)
∈-++⁻ (y ∷ xs) (there m) with ∈-++⁻ xs m
... | inl m′ = inl (there m′)
... | inr m′ = inr m′

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
-- Deciding term equality and occurrence
mutual
  _≟ₜ_ : (s t : Tm) → Dec (s ≡ t)
  var x     ≟ₜ var y with x ≟ y
  ... | yes refl = yes refl
  ... | no ne    = no (λ { refl → ne refl })
  var x     ≟ₜ node g ts = no (λ ())
  node f ss ≟ₜ var y     = no (λ ())
  node f ss ≟ₜ node g ts with f ≟ g | ss ≟ₜs ts
  ... | yes refl | yes refl = yes refl
  ... | no ne    | _        = no (λ { refl → ne refl })
  ... | yes _    | no ne    = no (λ { refl → ne refl })

  _≟ₜs_ : (ss ts : List Tm) → Dec (ss ≡ ts)
  []       ≟ₜs []       = yes refl
  []       ≟ₜs (t ∷ ts) = no (λ ())
  (s ∷ ss) ≟ₜs []       = no (λ ())
  (s ∷ ss) ≟ₜs (t ∷ ts) with s ≟ₜ t | ss ≟ₜs ts
  ... | yes refl | yes refl = yes refl
  ... | no ne    | _        = no (λ { refl → ne refl })
  ... | yes _    | no ne    = no (λ { refl → ne refl })

-- The variables of a term, as a list.
mutual
  vars : Tm → List ℕ
  vars (var x)     = x ∷ []
  vars (node f ts) = varss ts

  varss : List Tm → List ℕ
  varss []       = []
  varss (t ∷ ts) = vars t ++ varss ts

mutual
  occ-vars : {x : ℕ} (t : Tm) → Occ x t → x ∈ vars t
  occ-vars (var x)     here    = here refl
  occ-vars (node f ts) (arg o) = occs-varss ts o

  occs-varss : {x : ℕ} (ts : List Tm) → Occs x ts → x ∈ varss ts
  occs-varss (t ∷ ts) (hd o) = any-++ˡ (occ-vars t o)
  occs-varss (t ∷ ts) (tl o) = any-++ʳ (vars t) (occs-varss ts o)

mutual
  vars-occ : {x : ℕ} (t : Tm) → x ∈ vars t → Occ x t
  vars-occ (var x)     (here refl) = here
  vars-occ (var x)     (there ())
  vars-occ (node f ts) m           = arg (varss-occs ts m)

  varss-occs : {x : ℕ} (ts : List Tm) → x ∈ varss ts → Occs x ts
  varss-occs (t ∷ ts) m with ∈-++⁻ (vars t) m
  ... | inl m′ = hd (vars-occ t m′)
  ... | inr m′ = tl (varss-occs ts m′)

occs-any : {x : ℕ} {ts : List Tm} → Occs x ts → Any (Occ x) ts
occs-any (hd o) = here o
occs-any (tl o) = there (occs-any o)

any-occs : {x : ℕ} {ts : List Tm} → Any (Occ x) ts → Occs x ts
any-occs (here o)  = hd o
any-occs (there a) = tl (any-occs a)

vars-ground : (t : Tm) → vars t ≡ [] → Ground t
vars-ground t e x o with transport (λ xs → x ∈ xs) e (occ-vars t o)
... | ()

------------------------------------------------------------------------
-- Hash-consed terms

-- An entry of a term table: a variable, or a symbol applied to the terms
-- at other positions. It caches its term, a tree that checking does not
-- build, and its variables.
data Shape : Set where
  svar  : ℕ → Shape
  snode : ℕ → List ℕ → Shape

record Entry : Set where
  constructor entry
  field
    shape : Shape
    tm    : Tm
    vrs   : List ℕ
    -- The term's sort, when the decoder could establish one.
    srt   : Maybe ℕ
open Entry public

Table : Set
Table = Tree Entry

-- Every lookup that succeeds in t gives the same element in t′.
Ext : {A : Set} → Tree A → Tree A → Set
Ext {A} t t′ = ∀ i {x : A} → lookupT t i ≡ just x → lookupT t′ i ≡ just x

-- Changing one subtree in an extending way extends the tree.
ext-left : {A : Set} (x : A) (l l′ r : Tree A) (i : ℕ) {y : A} → Ext l l′
         → lookupT (bin x l r) (suc i) ≡ just y → lookupT (bin x l′ r) (suc i) ≡ just y
ext-left x l l′ r i ext e with even i
... | true  = ext (half i) e
... | false = e

ext-right : {A : Set} (x : A) (l r r′ : Tree A) (i : ℕ) {y : A} → Ext r r′
          → lookupT (bin x l r) (suc i) ≡ just y → lookupT (bin x l r′) (suc i) ≡ just y
ext-right x l r r′ i ext e with even i
... | true  = e
... | false = ext (half i) e

-- Insertion never overwrites, so it extends.
insert-ext : {A : Set} (t : Tree A) (n : ℕ) (a : A) → Ext t (insertT t n a)
insert-ext leaf        n       a i       ()
insert-ext (bin x l r) zero    a i       e = e
insert-ext (bin x l r) (suc n) a zero    e with even n
... | true  = e
... | false = e
insert-ext (bin x l r) (suc n) a (suc i) e with even n
... | true  = ext-left x l (insertT l (half n) a) r i (insert-ext l (half n) a) e
... | false = ext-right x l r (insertT r (half n) a) i (insert-ext r (half n) a) e

ext-trans : {A : Set} {t t′ t″ : Tree A} → Ext t t′ → Ext t′ t″ → Ext t t″
ext-trans p q i e = q i (p i e)

-- Elements of xs not in ys.
without : List ℕ → List ℕ → List ℕ
without []       ys = []
without (x ∷ xs) ys = pick (x ∈? ys) (without xs ys) (x ∷ without xs ys)

union : List ℕ → List ℕ → List ℕ
union xs ys = xs ++ without ys xs

unions : List (List ℕ) → List ℕ
unions []         = []
unions (v ∷ vss) = union v (unions vss)

without-∈ : {x : ℕ} (xs ys : List ℕ) → x ∈ without xs ys → x ∈ xs
without-∈ (z ∷ xs) ys m with z ∈? ys
... | yes _ = there (without-∈ xs ys m)
without-∈ (z ∷ xs) ys (here e)  | no _ = here e
without-∈ (z ∷ xs) ys (there m) | no _ = there (without-∈ xs ys m)

∈-without : {x : ℕ} (xs ys : List ℕ) → x ∈ xs → ¬ (x ∈ ys) → x ∈ without xs ys
∈-without (z ∷ xs) ys (here refl) n with z ∈? ys
... | yes m = ⊥-elim (n m)
... | no _  = here refl
∈-without (z ∷ xs) ys (there m) n with z ∈? ys
... | yes _ = ∈-without xs ys m n
... | no _  = there (∈-without xs ys m n)

∈-union⁻ : {x : ℕ} (xs ys : List ℕ) → x ∈ union xs ys → (x ∈ xs) ⊎ (x ∈ ys)
∈-union⁻ xs ys m with ∈-++⁻ xs m
... | inl m′ = inl m′
... | inr m′ = inr (without-∈ ys xs m′)

∈-unionʳ : {x : ℕ} (xs ys : List ℕ) → x ∈ ys → x ∈ union xs ys
∈-unionʳ xs ys m with _ ∈? xs
... | yes m′ = any-++ˡ m′
... | no n   = any-++ʳ xs (∈-without ys xs m n)

∈-unions⁻ : {x : ℕ} (vss : List (List ℕ)) → x ∈ unions vss → Any (λ v → x ∈ v) vss
∈-unions⁻ (v ∷ vss) m with ∈-union⁻ v (unions vss) m
... | inl m′ = here m′
... | inr m′ = there (∈-unions⁻ vss m′)

∈-unions⁺ : {x : ℕ} (vss : List (List ℕ)) → Any (λ v → x ∈ v) vss → x ∈ unions vss
∈-unions⁺ (v ∷ vss) (here m)  = any-++ˡ m
∈-unions⁺ (v ∷ vss) (there a) = ∈-unionʳ v (unions vss) (∈-unions⁺ vss a)

-- `ks` name the entries `es` in T.
data Kids (T : Table) : List ℕ → List Entry → Set where
  []  : Kids T [] []
  _∷_ : {k : ℕ} {e : Entry} {ks : List ℕ} {es : List Entry}
      → lookupT T k ≡ just e → Kids T ks es → Kids T (k ∷ ks) (e ∷ es)

-- An entry agrees with T: its term and variables are built from those of
-- the entries it names.
data EntryOk (T : Table) : Entry → Set where
  okvar  : (x : ℕ) {s : Maybe ℕ} → EntryOk T (entry (svar x) (var x) (x ∷ []) s)
  oknode : (f : ℕ) {ks : List ℕ} {es : List Entry} {s : Maybe ℕ} → Kids T ks es
         → EntryOk T (entry (snode f ks) (node f (map tm es)) (unions (map vrs es)) s)

kids-ext : {T T′ : Table} → Ext T T′ → {ks : List ℕ} {es : List Entry} → Kids T ks es → Kids T′ ks es
kids-ext x []       = []
kids-ext x (e ∷ ks) = x _ e ∷ kids-ext x ks

entryOk-ext : {T T′ : Table} → Ext T T′ → {e : Entry} → EntryOk T e → EntryOk T′ e
entryOk-ext x (okvar v)       = okvar v
entryOk-ext x (oknode f kids) = oknode f (kids-ext x kids)

-- A table whose entries all agree with it.
Wf : Table → Set
Wf T = AllT (EntryOk T) T

∷-head : {A : Set} {x y : A} {xs ys : List A} → (x ∷ xs) ≡ (y ∷ ys) → x ≡ y
∷-head refl = refl

∷-tail : {A : Set} {x y : A} {xs ys : List A} → (x ∷ xs) ≡ (y ∷ ys) → xs ≡ ys
∷-tail refl = refl

-- The cached variables are exactly the variables of the cached term.
module _ {T : Table} (wf : Wf T) where
  mutual
    vrs-occ : (t : Tm) {e : Entry} → EntryOk T e → tm e ≡ t → {x : ℕ} → x ∈ vrs e → Occ x t
    vrs-occ t (okvar v) e (here refl) = transport (Occ v) e here
    vrs-occ t (oknode f {es = es} kids) refl m = arg (vrs-occs (map tm es) kids refl (∈-unions⁻ (map vrs es) m))

    vrs-occs : (ts : List Tm) {ks : List ℕ} {es : List Entry} → Kids T ks es → map tm es ≡ ts
             → {x : ℕ} → Any (λ v → x ∈ v) (map vrs es) → Occs x ts
    vrs-occs (t ∷ ts) {es = e′ ∷ es} (k ∷ kids) eq (here m) =
      hd (vrs-occ t (allT-lookup wf _ k) (∷-head eq) m)
    vrs-occs (t ∷ ts) {es = e′ ∷ es} (k ∷ kids) eq (there a) =
      tl (vrs-occs ts kids (∷-tail eq) a)

  mutual
    occ-vrs : (t : Tm) {e : Entry} → EntryOk T e → tm e ≡ t → {x : ℕ} → Occ x t → x ∈ vrs e
    occ-vrs t (okvar v) e o with transport (Occ _) (sym e) o
    ... | here = here refl
    occ-vrs t (oknode f {es = es} kids) refl (arg o) =
      ∈-unions⁺ (map vrs es) (occs-vrs (map tm es) kids refl o)

    occs-vrs : (ts : List Tm) {ks : List ℕ} {es : List Entry} → Kids T ks es → map tm es ≡ ts
             → {x : ℕ} → Occs x ts → Any (λ v → x ∈ v) (map vrs es)
    occs-vrs (t ∷ ts) {es = e′ ∷ es} (k ∷ kids) eq (hd o) =
      here (occ-vrs t (allT-lookup wf _ k) (∷-head eq) o)
    occs-vrs (t ∷ ts) {es = e′ ∷ es} (k ∷ kids) eq (tl o) =
      there (occs-vrs ts kids (∷-tail eq) o)

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

  -- Well-sorted terms, given the sorts `srt` of their variables: eigen-
  -- variables (`WS`) or the variables of a rule.
  mutual
    data WSv (srt : ℕ → ℕ) : Tm → ℕ → Set where
      var  : {x : ℕ} → WSv srt (var x) (srt x)
      node : {f s : ℕ} {ts : List Tm} → out f ≡ s → WSsv srt ts (ins f) → WSv srt (node f ts) s

    data WSsv (srt : ℕ → ℕ) : List Tm → List ℕ → Set where
      []  : WSsv srt [] []
      _∷_ : {t : Tm} {s : ℕ} {ts : List Tm} {ss : List ℕ}
          → WSv srt t s → WSsv srt ts ss → WSsv srt (t ∷ ts) (s ∷ ss)

  WS : Tm → ℕ → Set
  WS = WSv vs

  WSs : List Tm → List ℕ → Set
  WSs = WSsv vs

  -- Substituting well-sorted terms for variables of the same sorts.
  mutual
    ws-sub′ : {srt : ℕ → ℕ} (γ : Subst) {t : Tm} {s : ℕ} → WSv srt t s
            → (∀ x → Occ x t → WS (γ x) (srt x)) → WS (sub γ t) s
    ws-sub′ γ var        g = g _ here
    ws-sub′ γ (node e w) g = node e (wss-sub′ γ w (λ x o → g x (arg o)))

    wss-sub′ : {srt : ℕ → ℕ} (γ : Subst) {ts : List Tm} {ss : List ℕ} → WSsv srt ts ss
             → (∀ x → Occs x ts → WS (γ x) (srt x)) → WSs (subs γ ts) ss
    wss-sub′ γ []       g = []
    wss-sub′ γ (w ∷ ws) g = ws-sub′ γ w (λ x o → g x (hd o)) ∷ wss-sub′ γ ws (λ x o → g x (tl o))

  ws-sub : (γ : Subst) {t : Tm} {s : ℕ} → WS t s
         → (∀ x → Occ x t → WS (γ x) (vs x)) → WS (sub γ t) s
  ws-sub = ws-sub′

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
  -- Soundness of each form, stated semantically so that the algorithmic
  -- model below can use the same lemmas.

  hyp-valid : (h : Tm) → Valid (h ∷ []) h
  hyp-valid h γ gw (d ∷ []) = d

  inst-valid : {J : Tm} → Valid [] J → (τ : Subst) → (∀ x → Occ x J → WS (τ x) (vs x))
             → Valid [] (sub τ J)
  inst-valid {J} v τ wτ γ gw [] = transport Der (sym (sub-comp γ τ J)) (v (γ ∘ˢ τ) gw′ [])
    where
      gw′ : GW (γ ∘ˢ τ) (Vars [] J)
      gw′ x (inl o) =
        ground-sub γ (τ x) (λ y oy → fst (gw y (inl (sub-occ τ J o oy))))
        , ws-sub γ (wτ x o) (λ y oy → snd (gw y (inl (sub-occ τ J o oy))))
      gw′ x (inr ())

  data SemPrems (θ : Subst) : List Tm → List Tm → Set where
    []  : SemPrems θ [] []
    _∷_ : {p : Tm} {ps H H′ : List Tm} → Valid H (sub θ p) → SemPrems θ ps H′
        → SemPrems θ (p ∷ ps) (H ++ H′)

  -- Each premise holds at the composed instance, given that its variables
  -- and hypotheses are among the fact's (the predicate V).
  premises : {θ γ : Subst} {ps H : List Tm} {V : ℕ → Set} → SemPrems θ ps H
           → (∀ x → Occs x (subs θ ps) → V x) → GW γ V → (∀ x → Any (Occ x) H → V x)
           → All (λ h → Der (sub γ h)) H → All (λ p → Der (sub (γ ∘ˢ θ) p)) ps
  premises [] side gw hv hs = []
  premises {θ} {γ} {p ∷ ps} (_∷_ {H = H} {H′} v rest) side gw hv hs with all-++ H hs
  ... | hs₁ , hs₂ =
        transport Der (sub-comp γ θ p) (v γ gw₁ hs₁)
        ∷ premises rest (λ x o → side x (tl o)) gw (λ x a → hv x (any-++ʳ H a)) hs₂
    where
      gw₁ : GW γ (Vars H (sub θ p))
      gw₁ x (inl o) = gw x (side x (hd o))
      gw₁ x (inr a) = gw x (hv x (any-++ˡ a))

  step-valid : {r : Rule} → r ∈ R → (θ : Subst) → (∀ y → OccR y r → WS (θ y) (rs r y))
             → {H : List Tm} → SemPrems θ (prem r) H
             → (∀ x → Occs x (subs θ (prem r)) → Vars H (sub θ (concl r)) x)
             → Valid H (sub θ (concl r))
  step-valid {r} r∈R θ wθ {H} ps side γ gw hs =
    transport Der (sym (sub-comp γ θ (concl r))) (by r∈R (γ ∘ˢ θ) ok (premises ps side gw (λ x a → inr a) hs))
    where
      -- Every variable of a rule variable's binding is a variable of the fact.
      allowed : ∀ y → OccR y r → ∀ x → Occ x (θ y) → Vars H (sub θ (concl r)) x
      allowed y (inl o) x ox = side x (subs-occ θ (prem r) o ox)
      allowed y (inr o) x ox = inl (sub-occ θ (concl r) o ox)

      ok : ∀ y → OccR y r → GroundWS ((γ ∘ˢ θ) y) (rs r y)
      ok y o = ground-sub γ (θ y) (λ x ox → fst (gw x (allowed y o x ox)))
             , ws-sub γ (wθ y o) (λ x ox → snd (gw x (allowed y o x ox)))

  mutual
    sound : {H : List Tm} {J : Tm} → H ⊢ J → Valid H J
    sound (hyp h)                   = hyp-valid h
    sound (inst d τ wτ)             = inst-valid (sound d) τ wτ
    sound (step r∈R θ wθ ps side)   = step-valid r∈R θ wθ (semPrems ps) side
    sound (induct X J oX cases)     = Induction.induction X J oX (λ c e → semantic (cases c e))

    semPrems : {θ : Subst} {ps H : List Tm} → Prems θ ps H → SemPrems θ ps H
    semPrems []       = []
    semPrems (d ∷ ds) = sound d ∷ semPrems ds

    semantic : {X : ℕ} {J : Tm} {c : ℕ} → Case X J c → SemCase X J c
    semantic (case ys d s f hs ihs p) = semcase ys d s f hs ihs (sound p)

  -- Main theorem: every well-sorted ground instance of an accepted
  -- hypothesis-free judgment is derivable.
  closed : {J : Tm} → Valid [] J → (γ : Subst) → GW γ (λ x → Occ x J) → Der (sub γ J)
  closed v γ gw = v γ (λ { x (inl o) → gw x o ; x (inr ()) }) []

  soundness : {J : Tm} → [] ⊢ J → (γ : Subst) → GW γ (λ x → Occ x J) → Der (sub γ J)
  soundness d = closed (sound d)


  ----------------------------------------------------------------------
  -- The checking algorithm. Rule bindings are found by matching, as in
  -- Soundness.agda; references are step indices; hypotheses are carried as
  -- judgments.

  mutual
    wsv? : (srt : ℕ → ℕ) (t : Tm) (s : ℕ) → Dec (WSv srt t s)
    wsv? srt (var x) s with srt x ≟ s
    ... | yes refl = yes var
    ... | no ne    = no (λ { var → ne refl })
    wsv? srt (node f ts) s with out f ≟ s | wssv? srt ts (ins f)
    ... | yes e | yes w = yes (node e w)
    ... | no ne | _     = no (λ { (node e _) → ne e })
    ... | yes _ | no nw = no (λ { (node _ w) → nw w })

    wssv? : (srt : ℕ → ℕ) (ts : List Tm) (ss : List ℕ) → Dec (WSsv srt ts ss)
    wssv? srt []       []       = yes []
    wssv? srt []       (s ∷ ss) = no (λ ())
    wssv? srt (t ∷ ts) []       = no (λ ())
    wssv? srt (t ∷ ts) (s ∷ ss) with wsv? srt t s | wssv? srt ts ss
    ... | yes w | yes ws = yes (w ∷ ws)
    ... | no nw | _      = no (λ { (w ∷ _) → nw w })
    ... | yes _ | no nws = no (λ { (_ ∷ ws) → nws ws })

  ws? : (t : Tm) (s : ℕ) → Dec (WS t s)
  ws? = wsv? vs

  -- Partial assignments of rule variables.
  Env : Set
  Env = ℕ → Maybe Tm

  empty : Env
  empty _ = nothing

  _[_↦_] : Env → ℕ → Tm → Env
  (b [ x ↦ t ]) y = pick (x ≟ y) (just t) (b y)

  record _⊑_ (b c : Env) : Set where
    constructor keeps
    field
      kept : ∀ {x t} → b x ≡ just t → c x ≡ just t
  open _⊑_

  ⊑-refl : {b : Env} → b ⊑ b
  ⊑-refl = keeps (λ e → e)

  ⊑-trans : {a b c : Env} → a ⊑ b → b ⊑ c → a ⊑ c
  ⊑-trans p q = keeps (λ e → kept q (kept p e))

  upd-same : (b : Env) (x : ℕ) (t : Tm) → (b [ x ↦ t ]) x ≡ just t
  upd-same b x t with x ≟ x
  ... | yes _ = refl
  ... | no ne = ⊥-elim (ne refl)

  upd-ext : (b : Env) (x : ℕ) (t : Tm) → b x ≡ nothing → b ⊑ (b [ x ↦ t ])
  upd-ext b x t free = keeps lemma
    where
      lemma : ∀ {y s} → b y ≡ just s → (b [ x ↦ t ]) y ≡ just s
      lemma {y} e with x ≟ y
      ... | yes refl = ⊥-elim (nothing≢just (trans (sym free) e))
      ... | no _     = e

  mutual
    instE : Env → Tm → Maybe Tm
    instE b (var x)     = b x
    instE b (node f ps) = instsE b ps >>= λ ts → just (node f ts)

    instsE : Env → List Tm → Maybe (List Tm)
    instsE b []       = just []
    instsE b (p ∷ ps) = instE b p >>= λ t → instsE b ps >>= λ ts → just (t ∷ ts)

  cons-ok : {c : Env} (p : Tm) (ps : List Tm) {t : Tm} {ts : List Tm}
          → instE c p ≡ just t → instsE c ps ≡ just ts → instsE c (p ∷ ps) ≡ just (t ∷ ts)
  cons-ok p ps e₁ e₂ rewrite e₁ | e₂ = refl

  node-ok : {c : Env} (f : ℕ) (ps : List Tm) {ts : List Tm}
          → instsE c ps ≡ just ts → instE c (node f ps) ≡ just (node f ts)
  node-ok f ps e rewrite e = refl

  mutual
    inst-mono : {b c : Env} → b ⊑ c → (p : Tm) {t : Tm} → instE b p ≡ just t → instE c p ≡ just t
    inst-mono ext (var x) e = kept ext e
    inst-mono {b} ext (node f ps) e with bind-inv (instsE b ps) (λ ts → just (node f ts)) e
    ... | ts , e₁ , refl = node-ok f ps (insts-mono ext ps e₁)

    insts-mono : {b c : Env} → b ⊑ c → (ps : List Tm) {ts : List Tm}
               → instsE b ps ≡ just ts → instsE c ps ≡ just ts
    insts-mono ext [] e = e
    insts-mono {b} ext (p ∷ ps) e
      with bind-inv (instE b p) (λ t → instsE b ps >>= λ ts → just (t ∷ ts)) e
    ... | t , e₁ , e₂ with bind-inv (instsE b ps) (λ ts → just (t ∷ ts)) e₂
    ...   | ts , e₃ , refl = cons-ok p ps (inst-mono ext p e₁) (insts-mono ext ps e₃)

  fromMaybe : Maybe Tm → Tm
  fromMaybe nothing  = var 0
  fromMaybe (just t) = t

  total : Env → Subst
  total b x = fromMaybe (b x)

  mutual
    inst-subst : (b : Env) (p : Tm) {t : Tm} → instE b p ≡ just t → sub (total b) p ≡ t
    inst-subst b (var x) e = cong fromMaybe e
    inst-subst b (node f ps) e with bind-inv (instsE b ps) (λ ts → just (node f ts)) e
    ... | ts , e₁ , refl = cong (node f) (insts-subst b ps e₁)

    insts-subst : (b : Env) (ps : List Tm) {ts : List Tm} → instsE b ps ≡ just ts → subs (total b) ps ≡ ts
    insts-subst b [] refl = refl
    insts-subst b (p ∷ ps) e
      with bind-inv (instE b p) (λ t → instsE b ps >>= λ ts → just (t ∷ ts)) e
    ... | t , e₁ , e₂ with bind-inv (instsE b ps) (λ ts → just (t ∷ ts)) e₂
    ...   | ts , e₃ , refl = cong₂ _∷_ (inst-subst b p e₁) (insts-subst b ps e₃)

  bindVar : ℕ → Tm → Env → Maybe Tm → Maybe Env
  bindVar x t b nothing  = just (b [ x ↦ t ])
  bindVar x t b (just u) = when (u ≟ₜ t) b

  -- Rule patterns against open terms: an eigenvariable is matched only by
  -- a rule variable.
  mutual
    match : Tm → Tm → Env → Maybe Env
    match (var x)     t           b = bindVar x t b (b x)
    match (node f ps) (var e)     b = nothing
    match (node f ps) (node g ts) b = when (f ≟ g) b >>= matchs ps ts

    matchs : List Tm → List Tm → Env → Maybe Env
    matchs []       []       b = just b
    matchs (p ∷ ps) (t ∷ ts) b = match p t b >>= matchs ps ts
    matchs []       (t ∷ ts) b = nothing
    matchs (p ∷ ps) []       b = nothing

  bindVar-ok : (x : ℕ) (t : Tm) (b : Env) (m : Maybe Tm) {c : Env}
             → b x ≡ m → bindVar x t b m ≡ just c → (b ⊑ c) × (c x ≡ just t)
  bindVar-ok x t b nothing  bx refl = upd-ext b x t bx , upd-same b x t
  bindVar-ok x t b (just u) bx eq with when-inv (u ≟ₜ t) eq
  ... | u≡t , refl = ⊑-refl , trans bx (cong just u≡t)

  mutual
    match-ok : (p t : Tm) (b : Env) {c : Env} → match p t b ≡ just c → (b ⊑ c) × (instE c p ≡ just t)
    match-ok (var x) t b eq with bindVar-ok x t b (b x) refl eq
    ... | ext , e = ext , e
    match-ok (node f ps) (var e) b ()
    match-ok (node f ps) (node g ts) b eq with bind-inv (when (f ≟ g) b) (matchs ps ts) eq
    ... | b′ , e₁ , e₂ with when-inv (f ≟ g) e₁
    ...   | refl , refl with matchs-ok ps ts b e₂
    ...     | ext , e = ext , node-ok f ps e

    matchs-ok : (ps ts : List Tm) (b : Env) {c : Env} → matchs ps ts b ≡ just c
              → (b ⊑ c) × (instsE c ps ≡ just ts)
    matchs-ok [] [] b refl = ⊑-refl , refl
    matchs-ok (p ∷ ps) (t ∷ ts) b eq with bind-inv (match p t b) (matchs ps ts) eq
    ... | c₁ , e₁ , e₂ with match-ok p t b e₁ | matchs-ok ps ts c₁ e₂
    ...   | ext₁ , ok₁ | ext₂ , ok₂ = ⊑-trans ext₁ ext₂ , cons-ok p ps (inst-mono ext₂ p ok₁) ok₂
    matchs-ok []       (t ∷ ts) b ()
    matchs-ok (p ∷ ps) []       b ()



  IsNode : Tm → Set
  IsNode (var _)    = ⊥
  IsNode (node _ _) = ⊤

  headSort : Tm → ℕ
  headSort (var x)    = vs x
  headSort (node f _) = out f

  -- A rule is well-formed when its premises and conclusion are judgments,
  -- well-sorted for the sorts of its variables. The kernel's theory parser
  -- checks this.
  PatWF : Rule → Tm → Set
  PatWF r p = IsNode p × WSv (rs r) p (headSort p)

  RuleWF : Rule → Set
  RuleWF r = All (PatWF r) (prem r) × PatWF r (concl r)

  isNode? : (p : Tm) → Dec (IsNode p)
  isNode? (var _)    = no (λ ())
  isNode? (node _ _) = yes tt

  patWF? : (r : Rule) (p : Tm) → Dec (PatWF r p)
  patWF? r p = isNode? p ×? wsv? (rs r) p (headSort p)

  ruleWF? : (r : Rule) → Dec (RuleWF r)
  ruleWF? r = all? (patWF? r) (prem r) ×? patWF? r (concl r)

  -- `ctors s` lists the constructors of sort s; the checker relies on it
  -- naming every one for the sorts of eigenvariables (in Rust it is built
  -- from the declarations).
  module Algorithm (wf : All RuleWF R) (ctors : ℕ → List ℕ) (complete : ∀ c x → out c ≡ vs x → c ∈ ctors (vs x)) where

    Fact : Set
    Fact = List Tm × Tm

    ValidF : Fact → Set
    ValidF f = Valid (fst f) (snd f)

    Facts : Set
    Facts = Tree Fact

    -- A premise or result reference: `N`, or `(N (VAR TERM)...)`.
    data Ref : Set where
      ref : ℕ → Ref
      at  : ℕ → List (ℕ × Tm) → Ref

    data Form : Set where
      hypF    : Tm → Form
      -- rule index, premise references, explicit bindings, stated conclusion
      ruleF   : ℕ → List Ref → List (ℕ × Tm) → Maybe Tm → Form
      -- X, J, and per constructor of X's sort: the case step and variables
      inductF : ℕ → Tm → List (ℕ × List ℕ) → Form

    substOf : List (ℕ × Tm) → Subst
    substOf []             x = var x
    substOf ((y , t) ∷ bs) x = pick (y ≟ x) t (substOf bs x)

    substOf-ws : (bs : List (ℕ × Tm)) → All (λ b → WS (snd b) (vs (fst b))) bs
               → ∀ x → WS (substOf bs x) (vs x)
    substOf-ws []             []       x = var
    substOf-ws ((y , t) ∷ bs) (w ∷ ws) x with y ≟ x
    ... | yes refl = w
    ... | no _     = substOf-ws bs ws x

    -- Only hypothesis-free facts are instantiated.
    instFact : List (ℕ × Tm) → Fact → Maybe Fact
    instFact bs ([] , J)      = when (all? (λ b → ws? (snd b) (vs (fst b))) bs) ([] , sub (substOf bs) J)
    instFact bs ((h ∷ H) , J) = nothing

    resolve : Facts → Ref → Maybe Fact
    resolve fs (ref n)   = lookupT fs n
    resolve fs (at n bs) = lookupT fs n >>= instFact bs

    resolve-ok : (fs : Facts) → AllT ValidF fs → (r : Ref) {f : Fact}
               → resolve fs r ≡ just f → ValidF f
    resolve-ok fs vf (ref n) e = allT-lookup vf n e
    resolve-ok fs vf (at n bs) e with bind-inv (lookupT fs n) (instFact bs) e
    ... | ([] , J) , e₁ , e₂ with when-inv (all? (λ b → ws? (snd b) (vs (fst b))) bs) e₂
    ...   | ws , refl = inst-valid (allT-lookup vf n e₁) (substOf bs) (λ x _ → substOf-ws bs ws x)
    resolve-ok fs vf (at n bs) e | ((h ∷ H) , J) , e₁ , ()

    resolveAll : Facts → List Ref → Maybe (List Fact)
    resolveAll fs []       = just []
    resolveAll fs (r ∷ rs) = resolve fs r >>= λ f → resolveAll fs rs >>= λ qs → just (f ∷ qs)

    resolveAll-ok : (fs : Facts) → AllT ValidF fs → (rs : List Ref) {qs : List Fact}
                  → resolveAll fs rs ≡ just qs → All ValidF qs
    resolveAll-ok fs vf []       refl = []
    resolveAll-ok fs vf (r ∷ rs) e
      with bind-inv (resolve fs r) (λ f → resolveAll fs rs >>= λ qs → just (f ∷ qs)) e
    ... | f , e₁ , e₂ with bind-inv (resolveAll fs rs) (λ qs → just (f ∷ qs)) e₂
    ...   | qs , e₃ , refl = resolve-ok fs vf r e₁ ∷ resolveAll-ok fs vf rs e₃

    -- An explicit binding must be fresh and of the variable's sort.
    bindFresh : Rule → ℕ → Tm → Env → Maybe Tm → Maybe Env
    bindFresh r x t b nothing  = when (ws? t (rs r x)) (b [ x ↦ t ])
    bindFresh r x t b (just _) = nothing

    bindAll : Rule → List (ℕ × Tm) → Env → Maybe Env
    bindAll r []             b = just b
    bindAll r ((x , t) ∷ bs) b = bindFresh r x t b (b x) >>= bindAll r bs

    premisesMatch : List Tm → List Fact → Env → Maybe Env
    premisesMatch []       []       b = just b
    premisesMatch (p ∷ ps) (f ∷ qs) b = match p (snd f) b >>= premisesMatch ps qs
    premisesMatch []       (f ∷ qs) b = nothing
    premisesMatch (p ∷ ps) []       b = nothing

    conclude : Tm → Maybe Tm → Env → Maybe Env
    conclude p nothing  b = just b
    conclude p (just j) b = match p j b

    answer : Maybe Tm → Maybe Tm → Maybe Tm
    answer (just j) m = just j
    answer nothing  m = m

    hypsOf : List Fact → List Tm
    hypsOf []       = []
    hypsOf (f ∷ qs) = fst f ++ hypsOf qs

    -- Elements of xs not in ys.
    filterOut : List ℕ → List ℕ → List ℕ
    filterOut []       ys = []
    filterOut (x ∷ xs) ys = pick (x ∈? ys) (filterOut xs ys) (x ∷ filterOut xs ys)

    concatMap : (ℕ → List ℕ) → List ℕ → List ℕ
    concatMap f []       = []
    concatMap f (y ∷ ys) = f y ++ concatMap f ys

    -- Rule variables only in the conclusion, and only in the premises.
    conclOnly premOnly : Rule → List ℕ
    conclOnly r = filterOut (vars (concl r)) (varss (prem r))
    premOnly  r = filterOut (varss (prem r)) (vars (concl r))

    -- Bindings of variables that only the conclusion has are well-sorted;
    -- the others are parts of well-sorted facts. The variables of a premise
    -- occur in the conclusion or the hypotheses; for a rule variable in the
    -- conclusion this holds already, so only the others' bindings are
    -- examined, and when those are ground the conclusion's variables are
    -- never listed.
    finish : Rule → List Fact → Env → Tm → Maybe Fact
    finish r qs b J =
      when (all? (λ y → ws? (total b y) (rs r y)) (conclOnly r)) tt >>= λ _ →
      when (all? (λ x → x ∈? (vars J ++ varss (hypsOf qs))) (concatMap (λ y → vars (total b y)) (premOnly r)))
           (hypsOf qs , J)

    checkRule : Facts → ℕ → List Ref → List (ℕ × Tm) → Maybe Tm → Maybe Fact
    checkRule fs n refs binds stated =
      lookup R n >>= λ r →
      resolveAll fs refs >>= λ qs →
      bindAll r binds empty >>= λ b₀ →
      conclude (concl r) stated b₀ >>= λ b₁ →
      premisesMatch (prem r) qs b₁ >>= λ b₂ →
      answer stated (instE b₂ (concl r)) >>= finish r qs b₂

    -- What case (m, ys) for constructor c must satisfy, given fact m.
    CaseOk : ℕ → Tm → ℕ → List ℕ → Fact → Set
    CaseOk X J c ys f =
      (map vs ys ≡ ins c) × Distinct ys × All (λ y → ¬ (y ∈ vars J)) ys
      × (snd f ≡ sub (point X (node c (map var ys))) J)
      × All (λ h → Any (λ y → (vs y ≡ vs X) × (h ≡ sub (point X (var y)) J)) ys) (fst f)

    caseOk? : (X : ℕ) (J : Tm) (c : ℕ) (ys : List ℕ) (f : Fact) → Dec (CaseOk X J c ys f)
    caseOk? X J c ys f =
      (map vs ys ≟ℓ ins c) ×? distinct? ys ×? all? (λ y → not? (y ∈? vars J)) ys
      ×? (snd f ≟ₜ sub (point X (node c (map var ys))) J)
      ×? all? (λ h → any? (λ y → (vs y ≟ vs X) ×? (h ≟ₜ sub (point X (var y)) J)) ys) (fst f)

    checkCases : Facts → ℕ → Tm → List ℕ → List (ℕ × List ℕ) → Maybe ⊤
    checkCases fs X J []       []              = just tt
    checkCases fs X J (c ∷ cs) ((m , ys) ∷ ks) =
      lookupT fs m >>= λ f → when (caseOk? X J c ys f) tt >>= λ _ → checkCases fs X J cs ks
    checkCases fs X J []       (k ∷ ks)        = nothing
    checkCases fs X J (c ∷ cs) []              = nothing

    checkInduct : Facts → ℕ → Tm → List (ℕ × List ℕ) → Maybe Fact
    checkInduct fs X J ks =
      when (ws? J (headSort J)) tt >>= λ _ →
      when (X ∈? vars J) tt >>= λ _ → checkCases fs X J (ctors (vs X)) ks >>= λ _ → just ([] , J)

    checkStep : Facts → Form → Maybe Fact
    checkStep fs (hypF J)                   = when (ws? J (headSort J)) ((J ∷ []) , J)
    checkStep fs (ruleF n refs binds stated) = checkRule fs n refs binds stated
    checkStep fs (inductF X J ks)           = checkInduct fs X J ks

    -- `fs` holds the facts of the `n` earlier steps; references reach only
    -- them.
    checkSteps : Facts → ℕ → List Form → Maybe Facts
    checkSteps fs n []       = just fs
    checkSteps fs n (s ∷ ss) = checkStep fs s >>= λ f → checkSteps (insertT fs n f) (suc n) ss

    closed? : (f : Fact) (g : Tm) → Dec ((fst f ≡ []) × (snd f ≡ g))
    closed? ([] , J)      g = yes refl ×? (J ≟ₜ g)
    closed? ((h ∷ H) , J) g = no (λ { (() , _) })

    -- The i-th result names the step proving the i-th goal; goals may
    -- contain variables.
    checkGoals : Facts → List Tm → List Ref → Maybe ⊤
    checkGoals fs []       []       = just tt
    checkGoals fs (g ∷ gs) (r ∷ rs) =
      resolve fs r >>= λ f → when (closed? f g) tt >>= λ _ → checkGoals fs gs rs
    checkGoals fs []       (r ∷ rs) = nothing
    checkGoals fs (g ∷ gs) []       = nothing

    accepts : List Tm → List Form → List Ref → Maybe ⊤
    accepts goals forms results = checkSteps leaf 0 forms >>= λ fs → checkGoals fs goals results

    --------------------------------------------------------------------
    -- Soundness of the algorithm.
    --
    -- Invariant: every fact is valid and its judgment is well-sorted. With
    -- well-formed rules, matching then yields well-sorted bindings, so the
    -- algorithm needs no sort check beyond those the Rust code makes.

    FactWS : Fact → Set
    FactWS f = Σ ℕ (WS (snd f))

    Good : Fact → Set
    Good f = ValidF f × FactWS f

    all-map : {A : Set} {P Q : A → Set} → (∀ {x} → P x → Q x) → {xs : List A} → All P xs → All Q xs
    all-map f []       = []
    all-map f (p ∷ ps) = f p ∷ all-map f ps

    just-inj : {A : Set} {x y : A} → just x ≡ just y → x ≡ y
    just-inj refl = refl

    filterOut-∈ : {x : ℕ} {xs : List ℕ} (ys : List ℕ) → x ∈ xs → ¬ (x ∈ ys) → x ∈ filterOut xs ys
    filterOut-∈ {xs = z ∷ xs} ys (here refl) n with z ∈? ys
    ... | yes m = ⊥-elim (n m)
    ... | no _  = here refl
    filterOut-∈ {xs = z ∷ xs} ys (there m) n with z ∈? ys
    ... | yes _ = filterOut-∈ ys m n
    ... | no _  = there (filterOut-∈ ys m n)

    concatMap-∈ : (f : ℕ → List ℕ) {x y : ℕ} {ys : List ℕ} → y ∈ ys → x ∈ f y → x ∈ concatMap f ys
    concatMap-∈ f {ys = z ∷ ys} (here refl) m = any-++ˡ m
    concatMap-∈ f {ys = z ∷ ys} (there n)   m = any-++ʳ (f z) (concatMap-∈ f n m)

    -- A well-sorted instance of a well-sorted pattern binds every variable
    -- to a term of the variable's sort.
    mutual
      inst-ws : (r : Rule) (c : Env) (p : Tm) {t : Tm} {s : ℕ} → instE c p ≡ just t
              → WSv (rs r) p s → WS t s → ∀ y → Occ y p → WS (total c y) (rs r y)
      inst-ws r c (var x) e var w y here = transport (λ m → WS (fromMaybe m) (rs r x)) (sym e) w
      inst-ws r c (node f ps) e (node _ wps) w y (arg o) = node-ws r c f ps e wps w y o

      node-ws : (r : Rule) (c : Env) (f : ℕ) (ps : List Tm) {t : Tm} {s : ℕ}
              → instE c (node f ps) ≡ just t → WSsv (rs r) ps (ins f) → WS t s
              → ∀ y → Occs y ps → WS (total c y) (rs r y)
      node-ws r c f ps e wps w y o with bind-inv (instsE c ps) (λ ts → just (node f ts)) e
      ... | ts , e₁ , refl with w
      ...   | node _ wts = insts-ws r c ps e₁ wps wts y o

      insts-ws : (r : Rule) (c : Env) (ps : List Tm) {ts : List Tm} {ss : List ℕ}
               → instsE c ps ≡ just ts → WSsv (rs r) ps ss → WSs ts ss
               → ∀ y → Occs y ps → WS (total c y) (rs r y)
      insts-ws r c (p ∷ ps) e (wp ∷ wps) w y o
        with bind-inv (instE c p) (λ t → instsE c ps >>= λ ts → just (t ∷ ts)) e
      ... | t , e₁ , e₂ with bind-inv (instsE c ps) (λ ts → just (t ∷ ts)) e₂
      ...   | ts , e₃ , refl with w | o
      ...     | wt ∷ wts | hd o′ = inst-ws r c p e₁ wp wt y o′
      ...     | wt ∷ wts | tl o′ = insts-ws r c ps e₃ wps wts y o′

    -- At the top a judgment pattern and its instance share their head, so
    -- the sorts stated for them need not be compared.
    top-ws : (r : Rule) (c : Env) (p : Tm) {t : Tm} {s₁ s₂ : ℕ} → IsNode p → instE c p ≡ just t
           → WSv (rs r) p s₁ → WS t s₂ → ∀ y → Occ y p → WS (total c y) (rs r y)
    top-ws r c (node f ps) n e (node _ wps) w y (arg o) = node-ws r c f ps e wps w y o

    -- Every variable of a pattern that instantiates is bound.
    mutual
      inst-bound : (c : Env) (p : Tm) {t : Tm} {y : ℕ} → instE c p ≡ just t → Occ y p
                 → Σ Tm (λ u → c y ≡ just u)
      inst-bound c (var x) e here = _ , e
      inst-bound c (node f ps) e (arg o) with bind-inv (instsE c ps) (λ ts → just (node f ts)) e
      ... | ts , e₁ , _ = insts-bound c ps e₁ o

      insts-bound : (c : Env) (ps : List Tm) {ts : List Tm} {y : ℕ} → instsE c ps ≡ just ts → Occs y ps
                  → Σ Tm (λ u → c y ≡ just u)
      insts-bound c (p ∷ ps) e o
        with bind-inv (instE c p) (λ t → instsE c ps >>= λ ts → just (t ∷ ts)) e
      ... | t , e₁ , e₂ with bind-inv (instsE c ps) (λ ts → just (t ∷ ts)) e₂
      ...   | ts , e₃ , _ with o
      ...     | hd o′ = inst-bound c p e₁ o′
      ...     | tl o′ = insts-bound c ps e₃ o′

    data PremsAt (c : Env) : List Tm → List Fact → Set where
      []   : PremsAt c [] []
      cons : {p : Tm} {ps : List Tm} {f : Fact} {qs : List Fact}
           → instE c p ≡ just (snd f) → ValidF f → PremsAt c ps qs → PremsAt c (p ∷ ps) (f ∷ qs)

    premsAt-bound : (c : Env) {ps : List Tm} {qs : List Fact} {y : ℕ} → PremsAt c ps qs → Occs y ps
                  → Σ Tm (λ u → c y ≡ just u)
    premsAt-bound c {p ∷ ps} (cons e v rest) (hd o) = inst-bound c p e o
    premsAt-bound c          (cons e v rest) (tl o) = premsAt-bound c rest o

    premisesMatch-ok : (ps : List Tm) (qs : List Fact) (b : Env) {c : Env} → All ValidF qs
                     → premisesMatch ps qs b ≡ just c → (b ⊑ c) × PremsAt c ps qs
    premisesMatch-ok []       []       b vq       refl = ⊑-refl , []
    premisesMatch-ok (p ∷ ps) (f ∷ qs) b (v ∷ vq) e
      with bind-inv (match p (snd f) b) (premisesMatch ps qs) e
    ... | c₁ , e₁ , e₂ with match-ok p (snd f) b e₁ | premisesMatch-ok ps qs c₁ vq e₂
    ...   | ext₁ , ok₁ | ext₂ , rest = ⊑-trans ext₁ ext₂ , cons (inst-mono ext₂ p ok₁) v rest
    premisesMatch-ok []       (f ∷ qs) b vq ()
    premisesMatch-ok (p ∷ ps) []       b vq ()

    premsAt-sem : (c : Env) {ps : List Tm} {qs : List Fact} → PremsAt c ps qs
                → SemPrems (total c) ps (hypsOf qs)
    premsAt-sem c []                                  = []
    premsAt-sem c {p ∷ ps} {f ∷ qs} (cons e v rest) =
      transport (Valid (fst f)) (sym (inst-subst c p e)) v ∷ premsAt-sem c rest

    conclusion-ok : (p : Tm) (st : Maybe Tm) (b₀ b₁ b₂ : Env) {t : Tm}
                  → conclude p st b₀ ≡ just b₁ → b₁ ⊑ b₂
                  → answer st (instE b₂ p) ≡ just t → instE b₂ p ≡ just t
    conclusion-ok p nothing  b₀ b₁ b₂ e ext a = a
    conclusion-ok p (just j) b₀ b₁ b₂ e ext refl with match-ok p j b₀ e
    ... | _ , ok = inst-mono ext p ok

    resolve-ws : (fs : Facts) → AllT FactWS fs → (r : Ref) {f : Fact}
               → resolve fs r ≡ just f → FactWS f
    resolve-ws fs wf′ (ref n) e = allT-lookup wf′ n e
    resolve-ws fs wf′ (at n bs) e with bind-inv (lookupT fs n) (instFact bs) e
    ... | ([] , J) , e₁ , e₂ with when-inv (all? (λ b → ws? (snd b) (vs (fst b))) bs) e₂
    ...   | ws , refl with allT-lookup wf′ n e₁
    ...     | s , w = s , ws-sub (substOf bs) w (λ x _ → substOf-ws bs ws x)
    resolve-ws fs wf′ (at n bs) e | ((h ∷ H) , J) , e₁ , ()

    resolveAll-ws : (fs : Facts) → AllT FactWS fs → (rs : List Ref) {qs : List Fact}
                  → resolveAll fs rs ≡ just qs → All FactWS qs
    resolveAll-ws fs wf′ []       refl = []
    resolveAll-ws fs wf′ (r ∷ rs) e
      with bind-inv (resolve fs r) (λ f → resolveAll fs rs >>= λ qs → just (f ∷ qs)) e
    ... | f , e₁ , e₂ with bind-inv (resolveAll fs rs) (λ qs → just (f ∷ qs)) e₂
    ...   | qs , e₃ , refl = resolve-ws fs wf′ r e₁ ∷ resolveAll-ws fs wf′ rs e₃

    prem-ws : (r : Rule) (c : Env) {ps : List Tm} {qs : List Fact} → PremsAt c ps qs → All FactWS qs
            → All (PatWF r) ps → ∀ y → Occs y ps → WS (total c y) (rs r y)
    prem-ws r c {p ∷ ps} (cons e v rest) ((s , w) ∷ wq) ((n , wp) ∷ wps) y (hd o) = top-ws r c p n e wp w y o
    prem-ws r c          (cons e v rest) (_ ∷ wq)       (_ ∷ wps)        y (tl o) = prem-ws r c rest wq wps y o

    rule-ok : (fs : Facts) → AllT Good fs → (n : ℕ) (refs : List Ref)
              (binds : List (ℕ × Tm)) (stated : Maybe Tm) {f : Fact}
            → checkRule fs n refs binds stated ≡ just f → Good f
    rule-ok fs gf n refs binds stated e
      with bind-inv (lookup R n) _ e
    ... | r , er , e₁ with bind-inv (resolveAll fs refs) _ e₁
    ... | qs , eq , e₂ with bind-inv (bindAll r binds empty) _ e₂
    ... | b₀ , eb , e₃ with bind-inv (conclude (concl r) stated b₀) _ e₃
    ... | b₁ , ec , e₄ with bind-inv (premisesMatch (prem r) qs b₁) _ e₄
    ... | b₂ , ep , e₅ with bind-inv (answer stated (instE b₂ (concl r))) (finish r qs b₂) e₅
    ... | J , ea , e₆ with bind-inv (when (all? (λ y → ws? (total b₂ y) (rs r y)) (conclOnly r)) tt) _ e₆
    ... | _ , ew , e₇ with when-inv (all? (λ y → ws? (total b₂ y) (rs r y)) (conclOnly r)) ew
    ... | conclWS , _ with when-inv (all? (λ x → x ∈? (vars J ++ varss (hypsOf qs)))
                                          (concatMap (λ y → vars (total b₂ y)) (premOnly r))) e₇
    ... | sideAll , refl = valid , (headSort (concl r) , transport (λ t → WS t _) concl-eq wsJ)
      where
        vf : AllT ValidF fs
        vf = allT-map fst gf

        wfs : AllT FactWS fs
        wfs = allT-map snd gf

        wfr : RuleWF r
        wfr = all-lookup n wf er

        θ : Subst
        θ = total b₂

        pm : (b₁ ⊑ b₂) × PremsAt b₂ (prem r) qs
        pm = premisesMatch-ok (prem r) qs b₁ (resolveAll-ok fs vf refs eq) ep

        concl-inst : instE b₂ (concl r) ≡ just J
        concl-inst = conclusion-ok (concl r) stated b₀ b₁ b₂ ec (fst pm) ea

        concl-eq : sub θ (concl r) ≡ J
        concl-eq = inst-subst b₂ (concl r) concl-inst

        -- Premise variables are bound to parts of well-sorted facts; the
        -- conclusion's other variables were checked.
        premWS : ∀ y → Occs y (prem r) → WS (θ y) (rs r y)
        premWS = prem-ws r b₂ (snd pm) (resolveAll-ws fs wfs refs eq) (fst wfr)

        wθ : ∀ y → OccR y r → WS (θ y) (rs r y)
        wθ y (inl o) = premWS y o
        wθ y (inr o) with y ∈? varss (prem r)
        ... | yes m = premWS y (varss-occs (prem r) m)
        ... | no nm = all-∈ conclWS (filterOut-∈ (varss (prem r)) (occ-vars (concl r) o) nm)

        wsJ : WS (sub θ (concl r)) (headSort (concl r))
        wsJ = ws-sub′ θ (snd (snd wfr)) (λ y o → wθ y (inr o))

        side : ∀ x → Occs x (subs θ (prem r)) → Vars (hypsOf qs) (sub θ (concl r)) x
        side x o with occs-sub θ (prem r) o
        ... | y , oy , ox with y ∈? vars (concl r)
        ...   | yes m = inl (sub-occ θ (concl r) (vars-occ (concl r) m) ox)
        ...   | no nm with ∈-++⁻ (vars J) (all-∈ sideAll (concatMap-∈ (λ z → vars (θ z))
                             (filterOut-∈ (vars (concl r)) (occs-varss (prem r) oy) nm) (occ-vars (θ y) ox)))
        ...     | inl m = inl (transport (Occ x) (sym concl-eq) (vars-occ J m))
        ...     | inr m = inr (occs-any (varss-occs (hypsOf qs) m))

        valid : Valid (hypsOf qs) J
        valid = transport (Valid (hypsOf qs)) concl-eq
                  (step-valid (lookup-∈ R n er) θ wθ (premsAt-sem b₂ (snd pm)) side)

    any-witness : {P : ℕ → Set} {ys : List ℕ} → Any P ys → Σ ℕ (λ y → (y ∈ ys) × P y)
    any-witness (here p)  = _ , here refl , p
    any-witness (there a) with any-witness a
    ... | y , m , p = y , there m , p

    case-sem : (X : ℕ) (J : Tm) (c : ℕ) (ys : List ℕ) (f : Fact) → ValidF f → CaseOk X J c ys f
             → SemCase X J c
    case-sem X J c ys (hs , Jm) v (sorts , dist , fresh , jeq , ihs) =
      semcase ys dist sorts (all-map (λ n o → n (occ-vars J o)) fresh) hs
              (all-map ih ihs) (transport (Valid hs) jeq v)
      where
        ih : ∀ {h} → Any (λ y → (vs y ≡ vs X) × (h ≡ sub (point X (var y)) J)) ys → IH X J ys h
        ih a with any-witness a
        ... | y , m , (sy , he) = y , m , sy , he

    cases-ok : (fs : Facts) → AllT ValidF fs → (X : ℕ) (J : Tm) (cs : List ℕ) (ks : List (ℕ × List ℕ))
             → checkCases fs X J cs ks ≡ just tt → All (SemCase X J) cs
    cases-ok fs vf X J []       []              refl = []
    cases-ok fs vf X J (c ∷ cs) ((m , ys) ∷ ks) e with bind-inv (lookupT fs m) _ e
    ... | f , ef , e₁ with bind-inv (when (caseOk? X J c ys f) tt) _ e₁
    ...   | _ , ew , e₂ with when-inv (caseOk? X J c ys f) ew
    ...     | ok , _ = case-sem X J c ys f (allT-lookup vf m ef) ok ∷ cases-ok fs vf X J cs ks e₂
    cases-ok fs vf X J []       (k ∷ ks) ()
    cases-ok fs vf X J (c ∷ cs) []       ()

    induct-ok : (fs : Facts) → AllT Good fs → (X : ℕ) (J : Tm) (ks : List (ℕ × List ℕ)) {f : Fact}
              → checkInduct fs X J ks ≡ just f → Good f
    induct-ok fs gf X J ks e with bind-inv (when (ws? J (headSort J)) tt) _ e
    ... | _ , ewj , e₀ with when-inv (ws? J (headSort J)) ewj
    ... | wJ , _ with bind-inv (when (X ∈? vars J) tt) _ e₀
    ... | _ , em , e₁ with when-inv (X ∈? vars J) em
    ... | mX , _ with bind-inv (checkCases fs X J (ctors (vs X)) ks) _ e₁
    ... | _ , ec , refl =
          Induction.induction X J (vars-occ J mX)
            (λ c ce → all-∈ (cases-ok fs (allT-map fst gf) X J (ctors (vs X)) ks ec)
                            (complete c X ce))
          , (headSort J , wJ)

    step-ok : (fs : Facts) → AllT Good fs → (s : Form) {f : Fact} → checkStep fs s ≡ just f → Good f
    step-ok fs gf (hypF J) e with when-inv (ws? J (headSort J)) e
    ... | w , refl = hyp-valid J , (headSort J , w)
    step-ok fs gf (ruleF n refs binds stated) e = rule-ok fs gf n refs binds stated e
    step-ok fs gf (inductF X J ks)            e = induct-ok fs gf X J ks e

    steps-ok : (fs : Facts) → AllT Good fs → (n : ℕ) (ss : List Form) {gs : Facts}
             → checkSteps fs n ss ≡ just gs → AllT Good gs
    steps-ok fs gf n []       refl = gf
    steps-ok fs gf n (s ∷ ss) e with bind-inv (checkStep fs s) _ e
    ... | f , e₁ , e₂ = steps-ok (insertT fs n f) (allT-insert gf (step-ok fs gf s e₁) n) (suc n) ss e₂

    closed-fact : (f : Fact) {g : Tm} → fst f ≡ [] → snd f ≡ g → ValidF f → Valid [] g
    closed-fact ([] , J) refl refl v = v

    goals-ok : (fs : Facts) → AllT ValidF fs → (gs : List Tm) (rs : List Ref)
             → checkGoals fs gs rs ≡ just tt → All (Valid []) gs
    goals-ok fs vf []       []       refl = []
    goals-ok fs vf (g ∷ gs) (r ∷ rs) e with bind-inv (resolve fs r) _ e
    ... | f , ef , e₁ with bind-inv (when (closed? f g) tt) _ e₁
    ...   | _ , ew , e₂ with when-inv (closed? f g) ew
    ...     | (h , j) , _ = closed-fact f h j (resolve-ok fs vf r ef) ∷ goals-ok fs vf gs rs e₂
    goals-ok fs vf []       (r ∷ rs) ()
    goals-ok fs vf (g ∷ gs) []       ()

    -- Main theorem for the algorithm: if the checker accepts, every
    -- well-sorted ground instance of every goal is derivable.
    accepts-sound : (goals : List Tm) (forms : List Form) (results : List Ref)
                  → accepts goals forms results ≡ just tt
                  → All (λ g → ∀ γ → GW γ (λ x → Occ x g) → Der (sub γ g)) goals
    accepts-sound goals forms results e with bind-inv (checkSteps leaf 0 forms) _ e
    ... | fs , e₁ , e₂ =
          all-map closed (goals-ok fs (allT-map fst (steps-ok leaf leaf 0 forms e₁)) goals results e₂)

    --------------------------------------------------------------------
    -- Decoding compact certificates. Nothing here needs to be trusted:
    -- whatever certificate decoding yields, `accepts` still has to accept
    -- it for the stated goals.
    --
    --   CODE  = N ENTRY^N  M FORM^M  K REF^K
    --   ENTRY = 0 x | 1 f k TERM^k        (TERM: index of an earlier entry)
    --   FORM  = 0 TERM | 1 r n REF^n b (y TERM)^b STATED | 2 X TERM k CASE^k
    --   REF   = 0 n | 1 n b (x TERM)^b ;  STATED = 0 | 1 TERM ;  CASE = m k y^k

    Parser : Set → Set
    Parser A = Code → Maybe (A × Code)

    pureₚ : {A : Set} → A → Parser A
    pureₚ a c = just (a , c)

    _>>=ₚ_ : {A B : Set} → Parser A → (A → Parser B) → Parser B
    (p >>=ₚ f) c = p c >>= λ r → f (fst r) (snd r)
    infixl 1 _>>=ₚ_

    liftₚ : {A : Set} → Maybe A → Parser A
    liftₚ nothing  c = nothing
    liftₚ (just a) c = just (a , c)

    num : Parser ℕ
    num ε                  = nothing
    num (n ▸ c)            = just (n , c)
    num (pack zero w c)    = num c
    num (pack (suc k) w c) =
      just (mod-helper 0 4294967295 w 4294967295 , pack k (div-helper 0 4294967295 w 4294967295) c)

    many : {A : Set} → ℕ → Parser A → Parser (List A)
    many zero    p = pureₚ []
    many (suc k) p = p >>=ₚ λ a → many k p >>=ₚ λ as → pureₚ (a ∷ as)

    TmTable : Set
    TmTable = Tree Tm

    tmP : TmTable → Parser Tm
    tmP T = num >>=ₚ λ i → liftₚ (lookupT T i)

    entryP : TmTable → ℕ → Parser Tm
    entryP T zero    = num >>=ₚ λ x → pureₚ (var x)
    entryP T (suc _) = num >>=ₚ λ f → num >>=ₚ λ k → many k (tmP T) >>=ₚ λ ts → pureₚ (node f ts)

    table : ℕ → ℕ → TmTable → Parser TmTable
    table zero    i T = pureₚ T
    table (suc n) i T = num >>=ₚ entryP T >>=ₚ λ t → table n (suc i) (insertT T i t)

    binding : TmTable → Parser (ℕ × Tm)
    binding T = num >>=ₚ λ x → tmP T >>=ₚ λ t → pureₚ (x , t)

    refTag : TmTable → ℕ → Parser Ref
    refTag T zero    = num >>=ₚ λ n → pureₚ (ref n)
    refTag T (suc _) = num >>=ₚ λ n → num >>=ₚ λ b → many b (binding T) >>=ₚ λ bs → pureₚ (at n bs)

    refP : TmTable → Parser Ref
    refP T = num >>=ₚ refTag T

    statedTag : TmTable → ℕ → Parser (Maybe Tm)
    statedTag T zero    = pureₚ nothing
    statedTag T (suc _) = tmP T >>=ₚ λ j → pureₚ (just j)

    caseP : Parser (ℕ × List ℕ)
    caseP = num >>=ₚ λ m → num >>=ₚ λ k → many k num >>=ₚ λ ys → pureₚ (m , ys)

    formTag : TmTable → ℕ → Parser Form
    formTag T zero          = tmP T >>=ₚ λ j → pureₚ (hypF j)
    formTag T (suc zero)    =
      num >>=ₚ λ r → num >>=ₚ λ n → many n (refP T) >>=ₚ λ refs →
      num >>=ₚ λ b → many b (binding T) >>=ₚ λ bs →
      num >>=ₚ statedTag T >>=ₚ λ st → pureₚ (ruleF r refs bs st)
    formTag T (suc (suc _)) =
      num >>=ₚ λ X → tmP T >>=ₚ λ J → num >>=ₚ λ k → many k caseP >>=ₚ λ cs → pureₚ (inductF X J cs)

    certificateP : Parser (List Form × List Ref)
    certificateP =
      num >>=ₚ λ n → table n 0 leaf >>=ₚ λ T →
      num >>=ₚ λ m → many m (num >>=ₚ formTag T) >>=ₚ λ forms →
      num >>=ₚ λ k → many k (refP T) >>=ₚ λ results → pureₚ (forms , results)

    acceptsCode : List Tm → Code → Maybe ⊤
    acceptsCode goals c = certificateP c >>= λ r → accepts goals (fst (fst r)) (snd (fst r))

    acceptsCode-sound : (goals : List Tm) (c : Code) → acceptsCode goals c ≡ just tt
                      → All (λ g → ∀ γ → GW γ (λ x → Occ x g) → Der (sub γ g)) goals
    acceptsCode-sound goals c e with bind-inv (certificateP c) _ e
    ... | ((forms , results) , _) , _ , e₁ = accepts-sound goals forms results e₁

    --------------------------------------------------------------------
    -- The checker on hash-consed terms. Facts and bindings hold indices
    -- into a table T, so matching and comparing terms costs one comparison
    -- of naturals per node of the rule's patterns. The rare checks on
    -- hypotheses, inductions, instances and goals use the cached trees.
    -- Soundness needs only that the table is well-formed (`Wf T`).


    _≟ₘ_ : (a b : Maybe ℕ) → Dec (a ≡ b)
    nothing ≟ₘ nothing = yes refl
    nothing ≟ₘ just _  = no (λ ())
    just _  ≟ₘ nothing = no (λ ())
    just a  ≟ₘ just b with a ≟ b
    ... | yes refl = yes refl
    ... | no ne    = no (λ { refl → ne refl })

    -- An entry whose cached sort is the sort of its term.
    SortOk : Entry → Set
    SortOk e = ∀ s → srt e ≡ just s → WS (tm e) s

    srts? : (es : List Entry) (ss : List ℕ) → Dec (All₂ (λ e s → srt e ≡ just s) es ss)
    srts? []       []       = yes []
    srts? []       (s ∷ ss) = no (λ ())
    srts? (e ∷ es) []       = no (λ ())
    srts? (e ∷ es) (s ∷ ss) with srt e ≟ₘ just s | srts? es ss
    ... | yes p | yes ps = yes (p ∷ ps)
    ... | no np | _      = no (λ { (p ∷ _) → np p })
    ... | yes _ | no nps = no (λ { (_ ∷ ps) → nps ps })

    -- A symbol applied to entries of its argument sorts has its sort.
    nodeSort : ℕ → List Entry → Maybe ℕ
    nodeSort f es = pick (srts? es (ins f)) (just (out f)) nothing

    kids-sortOk : {T : Table} → AllT SortOk T → {ks : List ℕ} {es : List Entry} → Kids T ks es → All SortOk es
    kids-sortOk sw []         = []
    kids-sortOk sw (k ∷ kids) = allT-lookup sw _ k ∷ kids-sortOk sw kids

    srts-ws : {es : List Entry} {ss : List ℕ} → All SortOk es → All₂ (λ e s → srt e ≡ just s) es ss
            → WSs (map tm es) ss
    srts-ws []         []       = []
    srts-ws (ok ∷ oks) (p ∷ ps) = ok _ p ∷ srts-ws oks ps

    nodeSort-ok : (f : ℕ) (es : List Entry) → All SortOk es → ∀ s → nodeSort f es ≡ just s
                → WS (node f (map tm es)) s
    nodeSort-ok f es oks s e with srts? es (ins f)
    ... | yes p with e
    ...   | refl = node refl (srts-ws oks p)
    nodeSort-ok f es oks s () | no _
    -- References and steps for the hashed checker: terms are table indices.
    data RefH : Set where
      refH : ℕ → RefH
      -- An instance (N (VAR TERM)...), with the index of its judgment.
      atH  : ℕ → List (ℕ × ℕ) → ℕ → RefH

    data FormH : Set where
      hypH    : ℕ → FormH
      -- Rule index, premise references, explicit bindings, conclusion.
      ruleH   : ℕ → List RefH → List (ℕ × ℕ) → ℕ → FormH
      inductH : ℕ → ℕ → List (ℕ × List ℕ) → FormH

    module Hashed (T : Table) where

      -- An index outside the table denotes the variable 0, an entry that
      -- agrees with any table.
      default : Entry
      default = entry (svar 0) (var 0) (0 ∷ []) nothing

      entryOf : Maybe Entry → Entry
      entryOf nothing  = default
      entryOf (just e) = e

      entryAt : ℕ → Entry
      entryAt i = entryOf (lookupT T i)

      ⟦_⟧ : ℕ → Tm
      ⟦ i ⟧ = tm (entryAt i)

      at-ok : Wf T → (i : ℕ) → EntryOk T (entryAt i)
      at-ok wf i with lookupT T i in e
      ... | nothing = okvar 0
      ... | just x  = allT-lookup wf i e

      at-lookup : {i : ℕ} {e : Entry} → lookupT T i ≡ just e → entryAt i ≡ e
      at-lookup {i} e = cong entryOf e

      FactH : Set
      FactH = List ℕ × ℕ

      conv : FactH → Fact
      conv f = map ⟦_⟧ (fst f) , ⟦ snd f ⟧

      GoodH : FactH → Set
      GoodH f = ValidF (conv f) × FactWS (conv f)

      convBs : List (ℕ × ℕ) → List (ℕ × Tm)
      convBs []             = []
      convBs ((x , k) ∷ bs) = (x , ⟦ k ⟧) ∷ convBs bs

      instFactH : List (ℕ × ℕ) → ℕ → FactH → Maybe FactH
      instFactH bs i ([] , j) =
        when (all? (λ b → ws? (snd b) (vs (fst b))) (convBs bs)) tt >>= λ _ →
        when (⟦ i ⟧ ≟ₜ sub (substOf (convBs bs)) ⟦ j ⟧) ([] , i)
      instFactH bs i ((h ∷ H) , j) = nothing

      resolveH : Tree FactH → RefH → Maybe FactH
      resolveH fs (refH n)      = lookupT fs n
      resolveH fs (atH n bs i)  = lookupT fs n >>= instFactH bs i

      resolveAllH : Tree FactH → List RefH → Maybe (List FactH)
      resolveAllH fs []       = just []
      resolveAllH fs (r ∷ rs) = resolveH fs r >>= λ f → resolveAllH fs rs >>= λ qs → just (f ∷ qs)

      -- Assignments of rule variables to indices.
      EnvH : Set
      EnvH = ℕ → Maybe ℕ

      emptyH : EnvH
      emptyH _ = nothing

      _[_↦_]ʰ : EnvH → ℕ → ℕ → EnvH
      (b [ x ↦ i ]ʰ) y = pick (x ≟ y) (just i) (b y)

      bindVarH : ℕ → ℕ → EnvH → Maybe ℕ → Maybe EnvH
      bindVarH y i b nothing  = just (b [ y ↦ i ]ʰ)
      bindVarH y i b (just j) = when (j ≟ i) b

      mutual
        matchH : Tm → ℕ → EnvH → Maybe EnvH
        matchH (var y)     i b = bindVarH y i b (b y)
        matchH (node f ps) i b = matchShape f ps (shape (entryAt i)) b

        matchShape : ℕ → List Tm → Shape → EnvH → Maybe EnvH
        matchShape f ps (svar _)     b = nothing
        matchShape f ps (snode g ks) b = when (f ≟ g) b >>= matchsH ps ks

        matchsH : List Tm → List ℕ → EnvH → Maybe EnvH
        matchsH []       []       b = just b
        matchsH (p ∷ ps) (k ∷ ks) b = matchH p k b >>= matchsH ps ks
        matchsH []       (k ∷ ks) b = nothing
        matchsH (p ∷ ps) []       b = nothing

      bindFreshH : Rule → ℕ → ℕ → EnvH → Maybe ℕ → Maybe EnvH
      bindFreshH r x i b nothing  = when (ws? ⟦ i ⟧ (rs r x)) (b [ x ↦ i ]ʰ)
      bindFreshH r x i b (just _) = nothing

      bindAllH : Rule → List (ℕ × ℕ) → EnvH → Maybe EnvH
      bindAllH r []             b = just b
      bindAllH r ((x , i) ∷ bs) b = bindFreshH r x i b (b x) >>= bindAllH r bs

      premisesMatchH : List Tm → List FactH → EnvH → Maybe EnvH
      premisesMatchH []       []       b = just b
      premisesMatchH (p ∷ ps) (f ∷ qs) b = matchH p (snd f) b >>= premisesMatchH ps qs
      premisesMatchH []       (f ∷ qs) b = nothing
      premisesMatchH (p ∷ ps) []       b = nothing

      hypsOfH : List FactH → List ℕ
      hypsOfH []       = []
      hypsOfH (f ∷ qs) = fst f ++ hypsOfH qs

      fromMaybeℕ : Maybe ℕ → ℕ
      fromMaybeℕ nothing  = 0
      fromMaybeℕ (just i) = i

      vrsAt : ℕ → List ℕ
      vrsAt i = vrs (entryAt i)

      sortAt : ℕ → Maybe ℕ
      sortAt i = srt (entryAt i)

      finishH : Rule → List FactH → EnvH → ℕ → Maybe FactH
      finishH r qs b s =
        when (all? (λ y → sortAt (fromMaybeℕ (b y)) ≟ₘ just (rs r y)) (conclOnly r)) tt >>= λ _ →
        when (all? (λ x → x ∈? (vrsAt s ++ concatMap vrsAt (hypsOfH qs)))
                   (concatMap (λ y → vrsAt (fromMaybeℕ (b y))) (premOnly r)))
             (hypsOfH qs , s)

      checkRuleH : Tree FactH → ℕ → List RefH → List (ℕ × ℕ) → ℕ → Maybe FactH
      checkRuleH fs n refs binds s =
        lookup R n >>= λ r →
        resolveAllH fs refs >>= λ qs →
        bindAllH r binds emptyH >>= λ b₀ →
        matchH (concl r) s b₀ >>= λ b₁ →
        premisesMatchH (prem r) qs b₁ >>= λ b₂ →
        finishH r qs b₂ s

      checkCasesH : Tree FactH → ℕ → Tm → List ℕ → List (ℕ × List ℕ) → Maybe ⊤
      checkCasesH fs X J []       []              = just tt
      checkCasesH fs X J (c ∷ cs) ((m , ys) ∷ ks) =
        lookupT fs m >>= λ f → when (caseOk? X J c ys (conv f)) tt >>= λ _ → checkCasesH fs X J cs ks
      checkCasesH fs X J []       (k ∷ ks)        = nothing
      checkCasesH fs X J (c ∷ cs) []              = nothing

      checkInductH : Tree FactH → ℕ → ℕ → List (ℕ × List ℕ) → Maybe FactH
      checkInductH fs X j ks =
        when (ws? ⟦ j ⟧ (headSort ⟦ j ⟧)) tt >>= λ _ →
        when (X ∈? vars ⟦ j ⟧) tt >>= λ _ →
        checkCasesH fs X ⟦ j ⟧ (ctors (vs X)) ks >>= λ _ → just ([] , j)

      checkStepH : Tree FactH → FormH → Maybe FactH
      checkStepH fs (hypH j)                = when (ws? ⟦ j ⟧ (headSort ⟦ j ⟧)) ((j ∷ []) , j)
      checkStepH fs (ruleH n refs binds s)  = checkRuleH fs n refs binds s
      checkStepH fs (inductH X j ks)        = checkInductH fs X j ks

      -- Evaluate a fact before storing it. Agda evaluates lazily, and an
      -- unevaluated fact would keep everything its step computed alive.
      forceN : {B : Set} → ℕ → (ℕ → B) → B
      forceN zero    k = k zero
      forceN (suc n) k = k (suc n)

      forceL : {B : Set} → List ℕ → (List ℕ → B) → B
      forceL []       k = k []
      forceL (x ∷ xs) k = forceN x (λ x′ → forceL xs (λ xs′ → k (x′ ∷ xs′)))

      forceF : {B : Set} → FactH → (FactH → B) → B
      forceF (hs , j) k = forceL hs (λ hs′ → forceN j (λ j′ → k (hs′ , j′)))

      checkStepsH : Tree FactH → ℕ → List FormH → Maybe (Tree FactH)
      checkStepsH fs n []       = just fs
      checkStepsH fs n (s ∷ ss) =
        checkStepH fs s >>= λ f → forceF f (λ f′ → checkStepsH (insertT fs n f′) (suc n) ss)

      checkGoalsH : Tree FactH → List Tm → List RefH → Maybe ⊤
      checkGoalsH fs []       []       = just tt
      checkGoalsH fs (g ∷ gs) (r ∷ rs) =
        resolveH fs r >>= λ f → when (closed? (conv f) g) tt >>= λ _ → checkGoalsH fs gs rs
      checkGoalsH fs []       (r ∷ rs) = nothing
      checkGoalsH fs (g ∷ gs) []       = nothing

      acceptsH : List Tm → List FormH → List RefH → Maybe ⊤
      acceptsH goals forms results = checkStepsH leaf 0 forms >>= λ fs → checkGoalsH fs goals results

      ------------------------------------------------------------------
      -- Soundness, given a well-formed table.

      module Sound (twf : Wf T) (tws : AllT SortOk T) where

        sortAt-ok : (i s : ℕ) → sortAt i ≡ just s → WS ⟦ i ⟧ s
        sortAt-ok i s e with lookupT T i in l
        ... | nothing = ⊥-elim (nothing≢just e)
        ... | just x  = allT-lookup tws i l s e

        denM : Maybe ℕ → Maybe Tm
        denM nothing  = nothing
        denM (just i) = just ⟦ i ⟧

        -- The assignment of terms an assignment of indices stands for.
        den : EnvH → Env
        den b y = denM (b y)

        bindVarH-ok : (y i : ℕ) (b : EnvH) (m : Maybe ℕ) {c : EnvH} → b y ≡ m → bindVarH y i b m ≡ just c
                    → (den b ⊑ den c) × (den c y ≡ just ⟦ i ⟧)
        bindVarH-ok y i b nothing eqy refl = keeps ext , same
          where
            ext : ∀ {z t} → den b z ≡ just t → den (b [ y ↦ i ]ʰ) z ≡ just t
            ext {z} e with y ≟ z
            ... | yes refl = ⊥-elim (nothing≢just (trans (sym (cong denM eqy)) e))
            ... | no _     = e

            same : den (b [ y ↦ i ]ʰ) y ≡ just ⟦ i ⟧
            same with y ≟ y
            ... | yes _ = refl
            ... | no ne = ⊥-elim (ne refl)
        bindVarH-ok y i b (just j) eqy e with when-inv (j ≟ i) e
        ... | refl , refl = ⊑-refl , cong denM eqy

        mutual
          -- Matching an index is matching the term it stands for.
          matchH-ok : (p : Tm) (i : ℕ) (b : EnvH) {c : EnvH} → matchH p i b ≡ just c
                    → (den b ⊑ den c) × (instE (den c) p ≡ just ⟦ i ⟧)
          matchH-ok (var y)     i b e = bindVarH-ok y i b (b y) refl e
          matchH-ok (node f ps) i b e = shape-ok f ps i (entryAt i) refl (at-ok twf i) b e

          shape-ok : (f : ℕ) (ps : List Tm) (i : ℕ) (en : Entry) → entryAt i ≡ en → EntryOk T en
                   → (b : EnvH) {c : EnvH} → matchShape f ps (shape en) b ≡ just c
                   → (den b ⊑ den c) × (instE (den c) (node f ps) ≡ just ⟦ i ⟧)
          shape-ok f ps i _ ei (okvar x) b ()
          shape-ok f ps i _ ei (oknode g {ks} {es} kids) b e
            with bind-inv (when (f ≟ g) b) (matchsH ps ks) e
          ... | b′ , e₁ , e₂ with when-inv (f ≟ g) e₁
          ...   | refl , refl with matchsH-ok ps ks es kids b e₂
          ...     | ext , ok = ext , trans (node-ok f ps ok) (cong just (sym (cong tm ei)))

          matchsH-ok : (ps : List Tm) (ks : List ℕ) (es : List Entry) → Kids T ks es
                     → (b : EnvH) {c : EnvH} → matchsH ps ks b ≡ just c
                     → (den b ⊑ den c) × (instsE (den c) ps ≡ just (map tm es))
          matchsH-ok []       []       []        []          b refl = ⊑-refl , refl
          matchsH-ok (p ∷ ps) (k ∷ ks) (en ∷ es) (lk ∷ kids) b e
            with bind-inv (matchH p k b) (matchsH ps ks) e
          ... | c₁ , e₁ , e₂ with matchH-ok p k b e₁ | matchsH-ok ps ks es kids c₁ e₂
          ...   | ext₁ , ok₁ | ext₂ , ok₂ =
                  ⊑-trans ext₁ ext₂
                  , cons-ok p ps (trans (inst-mono ext₂ p ok₁) (cong just (cong tm (at-lookup lk)))) ok₂
          matchsH-ok []       (k ∷ ks) _ _ b ()
          matchsH-ok (p ∷ ps) []       _ _ b ()

        all-conv : {P : Fact → Set} {qs : List FactH} → All (λ q → P (conv q)) qs → All P (map conv qs)
        all-conv []       = []
        all-conv (p ∷ ps) = p ∷ all-conv ps

        map-++ : {A B : Set} (f : A → B) (xs ys : List A) → map f (xs ++ ys) ≡ (map f xs ++ map f ys)
        map-++ f []       ys = refl
        map-++ f (x ∷ xs) ys = cong (f x ∷_) (map-++ f xs ys)

        hypsOf-conv : (qs : List FactH) → hypsOf (map conv qs) ≡ map ⟦_⟧ (hypsOfH qs)
        hypsOf-conv []       = refl
        hypsOf-conv (q ∷ qs) = trans (cong (map ⟦_⟧ (fst q) ++_) (hypsOf-conv qs)) (sym (map-++ ⟦_⟧ (fst q) (hypsOfH qs)))

        premisesMatchH-ok : (ps : List Tm) (qs : List FactH) (b : EnvH) {c : EnvH}
                          → All (λ q → ValidF (conv q)) qs → premisesMatchH ps qs b ≡ just c
                          → (den b ⊑ den c) × PremsAt (den c) ps (map conv qs)
        premisesMatchH-ok []       []       b vq       refl = ⊑-refl , []
        premisesMatchH-ok (p ∷ ps) (q ∷ qs) b (v ∷ vq) e
          with bind-inv (matchH p (snd q) b) (premisesMatchH ps qs) e
        ... | c₁ , e₁ , e₂ with matchH-ok p (snd q) b e₁ | premisesMatchH-ok ps qs c₁ vq e₂
        ...   | ext₁ , ok₁ | ext₂ , rest = ⊑-trans ext₁ ext₂ , cons (inst-mono ext₂ p ok₁) v rest
        premisesMatchH-ok []       (q ∷ qs) b vq ()
        premisesMatchH-ok (p ∷ ps) []       b vq ()

        resolveH-ok : (fs : Tree FactH) → AllT GoodH fs → (r : RefH) {f : FactH} → resolveH fs r ≡ just f → GoodH f
        resolveH-ok fs gf (refH n) e = allT-lookup gf n e
        resolveH-ok fs gf (atH n bs i) e with bind-inv (lookupT fs n) (instFactH bs i) e
        ... | ([] , j) , e₁ , e₂ with bind-inv (when (all? (λ b → ws? (snd b) (vs (fst b))) (convBs bs)) tt) _ e₂
        ...   | _ , ew , e₃ with when-inv (all? (λ b → ws? (snd b) (vs (fst b))) (convBs bs)) ew
        ...     | ws , _ with when-inv (⟦ i ⟧ ≟ₜ sub (substOf (convBs bs)) ⟦ j ⟧) e₃
        ...       | eq , refl with allT-lookup gf n e₁
        ...         | v , (s , w) =
                      transport (Valid []) (sym eq) (inst-valid v τ (λ x _ → wτ x))
                      , (s , transport (λ t → WS t s) (sym eq) (ws-sub τ w (λ x _ → wτ x)))
          where
            τ : Subst
            τ = substOf (convBs bs)

            wτ : ∀ x → WS (τ x) (vs x)
            wτ x = substOf-ws (convBs bs) ws x
        resolveH-ok fs gf (atH n bs i) e | ((h ∷ H) , j) , e₁ , ()

        resolveAllH-ok : (fs : Tree FactH) → AllT GoodH fs → (rs : List RefH) {qs : List FactH}
                       → resolveAllH fs rs ≡ just qs → All GoodH qs
        resolveAllH-ok fs gf []       refl = []
        resolveAllH-ok fs gf (r ∷ rs) e
          with bind-inv (resolveH fs r) (λ f → resolveAllH fs rs >>= λ qs → just (f ∷ qs)) e
        ... | f , e₁ , e₂ with bind-inv (resolveAllH fs rs) (λ qs → just (f ∷ qs)) e₂
        ...   | qs , e₃ , refl = resolveH-ok fs gf r e₁ ∷ resolveAllH-ok fs gf rs e₃

        -- Cached variables of hypotheses are variables of their terms.
        vrs-hyps : (hs : List ℕ) {x : ℕ} → x ∈ concatMap vrsAt hs → Any (Occ x) (map ⟦_⟧ hs)
        vrs-hyps (h ∷ hs) m with ∈-++⁻ (vrsAt h) m
        ... | inl m′ = here (vrs-occ twf ⟦ h ⟧ (at-ok twf h) refl m′)
        ... | inr m′ = there (vrs-hyps hs m′)

        rule-okH : (fs : Tree FactH) → AllT GoodH fs → (n : ℕ) (refs : List RefH)
                   (binds : List (ℕ × ℕ)) (s : ℕ) {f : FactH}
                 → checkRuleH fs n refs binds s ≡ just f → GoodH f
        rule-okH fs gf n refs binds s e
          with bind-inv (lookup R n) _ e
        ... | r , er , e₁ with bind-inv (resolveAllH fs refs) _ e₁
        ... | qs , eq , e₂ with bind-inv (bindAllH r binds emptyH) _ e₂
        ... | b₀ , eb , e₃ with bind-inv (matchH (concl r) s b₀) _ e₃
        ... | b₁ , ec , e₄ with bind-inv (premisesMatchH (prem r) qs b₁) _ e₄
        ... | b₂ , ep , e₅
          with bind-inv (when (all? (λ y → sortAt (fromMaybeℕ (b₂ y)) ≟ₘ just (rs r y)) (conclOnly r)) tt) _ e₅
        ... | _ , ew , e₆ with when-inv (all? (λ y → sortAt (fromMaybeℕ (b₂ y)) ≟ₘ just (rs r y)) (conclOnly r)) ew
        ... | conclWS , _
          with when-inv (all? (λ x → x ∈? (vrsAt s ++ concatMap vrsAt (hypsOfH qs)))
                              (concatMap (λ y → vrsAt (fromMaybeℕ (b₂ y))) (premOnly r))) e₆
        ... | sideAll , refl =
              transport (Valid (map ⟦_⟧ (hypsOfH qs))) concl-eq
                (transport (λ H → Valid H (sub θ (concl r))) (hypsOf-conv qs)
                  (step-valid (lookup-∈ R n er) θ wθ (premsAt-sem (den b₂) (snd pm)) side))
              , (headSort (concl r) , transport (λ t → WS t _) concl-eq wsJ)
          where
            gqs : All GoodH qs
            gqs = resolveAllH-ok fs gf refs eq

            wfr : RuleWF r
            wfr = all-lookup n wf er

            pm : (den b₁ ⊑ den b₂) × PremsAt (den b₂) (prem r) (map conv qs)
            pm = premisesMatchH-ok (prem r) qs b₁ (all-map fst gqs) ep

            concl-inst : instE (den b₂) (concl r) ≡ just ⟦ s ⟧
            concl-inst = inst-mono (fst pm) (concl r) (snd (matchH-ok (concl r) s b₀ ec))

            θ : Subst
            θ = total (den b₂)

            concl-eq : sub θ (concl r) ≡ ⟦ s ⟧
            concl-eq = inst-subst (den b₂) (concl r) concl-inst

            -- A bound variable's term is the term of its index.
            bound : ∀ y → Σ Tm (λ u → den b₂ y ≡ just u) → θ y ≡ ⟦ fromMaybeℕ (b₂ y) ⟧
            bound y (u , d) with b₂ y
            ... | just j = refl
            ... | nothing = ⊥-elim (nothing≢just d)

            premWS : ∀ y → Occs y (prem r) → WS (θ y) (rs r y)
            premWS = prem-ws r (den b₂) (snd pm) (all-conv (all-map snd gqs)) (fst wfr)

            wθ : ∀ y → OccR y r → WS (θ y) (rs r y)
            wθ y (inl o) = premWS y o
            wθ y (inr o) with y ∈? varss (prem r)
            ... | yes m = premWS y (varss-occs (prem r) m)
            ... | no nm = transport (λ t → WS t (rs r y))
                            (sym (bound y (inst-bound (den b₂) (concl r) concl-inst o)))
                            (sortAt-ok _ _ (all-∈ conclWS (filterOut-∈ (varss (prem r)) (occ-vars (concl r) o) nm)))

            wsJ : WS (sub θ (concl r)) (headSort (concl r))
            wsJ = ws-sub′ θ (snd (snd wfr)) (λ y o → wθ y (inr o))

            allowed : ∀ x → x ∈ (vrsAt s ++ concatMap vrsAt (hypsOfH qs))
                    → Vars (hypsOf (map conv qs)) (sub θ (concl r)) x
            allowed x m with ∈-++⁻ (vrsAt s) m
            ... | inl m′ = inl (transport (Occ x) (sym concl-eq) (vrs-occ twf ⟦ s ⟧ (at-ok twf s) refl m′))
            ... | inr m′ = inr (transport (Any (Occ x)) (sym (hypsOf-conv qs)) (vrs-hyps (hypsOfH qs) m′))

            side : ∀ x → Occs x (subs θ (prem r)) → Vars (hypsOf (map conv qs)) (sub θ (concl r)) x
            side x o with occs-sub θ (prem r) o
            ... | y , oy , ox with y ∈? vars (concl r)
            ...   | yes m = inl (sub-occ θ (concl r) (vars-occ (concl r) m) ox)
            ...   | no nm =
                    allowed x (all-∈ sideAll
                      (concatMap-∈ (λ z → vrsAt (fromMaybeℕ (b₂ z)))
                        (filterOut-∈ (vars (concl r)) (occs-varss (prem r) oy) nm)
                        (occ-vrs twf ⟦ fromMaybeℕ (b₂ y) ⟧ (at-ok twf _) refl
                          (transport (Occ x) (bound y (premsAt-bound (den b₂) (snd pm) oy)) ox))))

        cases-okH : (fs : Tree FactH) → AllT GoodH fs → (X : ℕ) (J : Tm) (cs : List ℕ) (ks : List (ℕ × List ℕ))
                  → checkCasesH fs X J cs ks ≡ just tt → All (SemCase X J) cs
        cases-okH fs gf X J []       []              refl = []
        cases-okH fs gf X J (c ∷ cs) ((m , ys) ∷ ks) e with bind-inv (lookupT fs m) _ e
        ... | f , ef , e₁ with bind-inv (when (caseOk? X J c ys (conv f)) tt) _ e₁
        ...   | _ , ew , e₂ with when-inv (caseOk? X J c ys (conv f)) ew
        ...     | ok , _ = case-sem X J c ys (conv f) (fst (allT-lookup gf m ef)) ok ∷ cases-okH fs gf X J cs ks e₂
        cases-okH fs gf X J []       (k ∷ ks) ()
        cases-okH fs gf X J (c ∷ cs) []       ()

        induct-okH : (fs : Tree FactH) → AllT GoodH fs → (X j : ℕ) (ks : List (ℕ × List ℕ)) {f : FactH}
                   → checkInductH fs X j ks ≡ just f → GoodH f
        induct-okH fs gf X j ks e with bind-inv (when (ws? ⟦ j ⟧ (headSort ⟦ j ⟧)) tt) _ e
        ... | _ , ewj , e₀ with when-inv (ws? ⟦ j ⟧ (headSort ⟦ j ⟧)) ewj
        ... | wJ , _ with bind-inv (when (X ∈? vars ⟦ j ⟧) tt) _ e₀
        ... | _ , em , e₁ with when-inv (X ∈? vars ⟦ j ⟧) em
        ... | mX , _ with bind-inv (checkCasesH fs X ⟦ j ⟧ (ctors (vs X)) ks) _ e₁
        ... | _ , ec , refl =
              Induction.induction X ⟦ j ⟧ (vars-occ ⟦ j ⟧ mX)
                (λ c ce → all-∈ (cases-okH fs gf X ⟦ j ⟧ (ctors (vs X)) ks ec) (complete c X ce))
              , (headSort ⟦ j ⟧ , wJ)

        step-okH : (fs : Tree FactH) → AllT GoodH fs → (s : FormH) {f : FactH}
                 → checkStepH fs s ≡ just f → GoodH f
        step-okH fs gf (hypH j) e with when-inv (ws? ⟦ j ⟧ (headSort ⟦ j ⟧)) e
        ... | w , refl = hyp-valid ⟦ j ⟧ , (headSort ⟦ j ⟧ , w)
        step-okH fs gf (ruleH n refs binds s) e = rule-okH fs gf n refs binds s e
        step-okH fs gf (inductH X j ks)       e = induct-okH fs gf X j ks e


        forceN-id : {B : Set} (n : ℕ) (k : ℕ → B) → forceN n k ≡ k n
        forceN-id zero    k = refl
        forceN-id (suc n) k = refl

        forceL-id : {B : Set} (xs : List ℕ) (k : List ℕ → B) → forceL xs k ≡ k xs
        forceL-id []       k = refl
        forceL-id (x ∷ xs) k = trans (forceN-id x _) (forceL-id xs (λ xs′ → k (x ∷ xs′)))

        forceF-id : {B : Set} (f : FactH) (k : FactH → B) → forceF f k ≡ k f
        forceF-id (hs , j) k = trans (forceL-id hs _) (forceN-id j (λ j′ → k (hs , j′)))

        steps-okH : (fs : Tree FactH) → AllT GoodH fs → (n : ℕ) (ss : List FormH) {gs : Tree FactH}
                  → checkStepsH fs n ss ≡ just gs → AllT GoodH gs
        steps-okH fs gf n []       refl = gf
        steps-okH fs gf n (s ∷ ss) e with bind-inv (checkStepH fs s) _ e
        ... | f , e₁ , e₂ =
              steps-okH (insertT fs n f) (allT-insert gf (step-okH fs gf s e₁) n) (suc n) ss
                (trans (sym (forceF-id f (λ f′ → checkStepsH (insertT fs n f′) (suc n) ss))) e₂)

        goals-okH : (fs : Tree FactH) → AllT GoodH fs → (gs : List Tm) (rs : List RefH)
                  → checkGoalsH fs gs rs ≡ just tt → All (Valid []) gs
        goals-okH fs gf []       []       refl = []
        goals-okH fs gf (g ∷ gs) (r ∷ rs) e with bind-inv (resolveH fs r) _ e
        ... | f , ef , e₁ with bind-inv (when (closed? (conv f) g) tt) _ e₁
        ...   | _ , ew , e₂ with when-inv (closed? (conv f) g) ew
        ...     | (h , j) , _ = closed-fact (conv f) h j (fst (resolveH-ok fs gf r ef)) ∷ goals-okH fs gf gs rs e₂
        goals-okH fs gf []       (r ∷ rs) ()
        goals-okH fs gf (g ∷ gs) []       ()

        acceptsH-sound : (goals : List Tm) (forms : List FormH) (results : List RefH)
                       → acceptsH goals forms results ≡ just tt
                       → All (λ g → ∀ γ → GW γ (λ x → Occ x g) → Der (sub γ g)) goals
        acceptsH-sound goals forms results e with bind-inv (checkStepsH leaf 0 forms) _ e
        ... | fs , e₁ , e₂ = all-map closed (goals-okH fs (steps-okH leaf leaf 0 forms e₁) goals results e₂)

    --------------------------------------------------------------------
    -- Decoding for the hashed checker. The table is the one `certificateP`
    -- reads, now kept as entries; forms refer to terms by index, and every
    -- rule step and instance names the index of its judgment:
    --
    --   FORM = 0 TERM | 1 r n REF^n b (y TERM)^b TERM | 2 X TERM k CASE^k
    --   REF  = 0 n | 1 n b (x TERM)^b TERM
    --
    -- Forms need no proof. The table does: decoding builds each entry from
    -- the entries it names, so the table is well-formed.

    lookupAll : Table → List ℕ → Maybe (List Entry)
    lookupAll T []       = just []
    lookupAll T (k ∷ ks) = lookupT T k >>= λ e → lookupAll T ks >>= λ es → just (e ∷ es)

    lookupAll-ok : (T : Table) (ks : List ℕ) {es : List Entry} → lookupAll T ks ≡ just es → Kids T ks es
    lookupAll-ok T []       refl = []
    lookupAll-ok T (k ∷ ks) e
      with bind-inv (lookupT T k) (λ e → lookupAll T ks >>= λ es → just (e ∷ es)) e
    ... | en , e₁ , e₂ with bind-inv (lookupAll T ks) (λ es → just (en ∷ es)) e₂
    ...   | es , e₃ , refl = e₁ ∷ lookupAll-ok T ks e₃

    entryH : Table → ℕ → Parser Entry
    entryH T zero    = num >>=ₚ λ x → pureₚ (entry (svar x) (var x) (x ∷ []) (just (vs x)))
    entryH T (suc _) =
      num >>=ₚ λ f → num >>=ₚ λ k → many k num >>=ₚ λ ks → liftₚ (lookupAll T ks) >>=ₚ λ es →
      pureₚ (entry (snode f ks) (node f (map tm es)) (unions (map vrs es)) (nodeSort f es))

    tableH : ℕ → ℕ → Table → Parser Table
    tableH zero    i T = pureₚ T
    tableH (suc n) i T = num >>=ₚ entryH T >>=ₚ λ e → tableH n (suc i) (insertT T i e)

    liftₚ-inv : {A : Set} (m : Maybe A) {c : Code} {r : A × Code} → liftₚ m c ≡ just r → m ≡ just (fst r)
    liftₚ-inv (just a) refl = refl

    entryH-ok : (T : Table) (tag : ℕ) (c : Code) {r : Entry × Code} → AllT SortOk T → entryH T tag c ≡ just r
              → EntryOk T (fst r) × SortOk (fst r)
    entryH-ok T zero c sw e with bind-inv (num c) _ e
    ... | (x , c₁) , _ , refl = okvar x , λ { s refl → var }
    entryH-ok T (suc _) c sw e with bind-inv (num c) _ e
    ... | (f , c₁) , _ , e₁ with bind-inv (num c₁) _ e₁
    ... | (k , c₂) , _ , e₂ with bind-inv (many k num c₂) _ e₂
    ... | (ks , c₃) , _ , e₃ with bind-inv (liftₚ (lookupAll T ks) c₃) _ e₃
    ... | (es , c₄) , e₄ , refl =
          oknode f kids , nodeSort-ok f es (kids-sortOk sw kids)
      where
        kids : Kids T ks es
        kids = lookupAll-ok T ks (liftₚ-inv (lookupAll T ks) e₄)

    -- Decoding builds a well-formed table with right cached sorts.
    TableOk : Table → Set
    TableOk T = Wf T × AllT SortOk T

    tableH-ok : (n i : ℕ) (T : Table) (c : Code) {r : Table × Code} → TableOk T → tableH n i T c ≡ just r
              → TableOk (fst r)
    tableH-ok zero    i T c ok refl = ok
    tableH-ok (suc n) i T c (wfT , swT) e with bind-inv ((num >>=ₚ entryH T) c) _ e
    ... | (en , c₂) , e₁ , e₃ with bind-inv (num c) _ e₁
    ... | (tag , c₁) , _ , e₂ with entryH-ok T tag c₁ swT e₂
    ... | eok , sok =
          tableH-ok n (suc i) (insertT T i en) c₂
            ( allT-insert (allT-map (entryOk-ext (insert-ext T i en)) wfT) (entryOk-ext (insert-ext T i en) eok) i
            , allT-insert swT sok i)
            e₃

    refH-tag : ℕ → Parser RefH
    refH-tag zero    = num >>=ₚ λ n → pureₚ (refH n)
    refH-tag (suc _) =
      num >>=ₚ λ n → num >>=ₚ λ b → many b (num >>=ₚ λ x → num >>=ₚ λ t → pureₚ (x , t)) >>=ₚ λ bs →
      num >>=ₚ λ i → pureₚ (atH n bs i)

    formH-tag : ℕ → Parser FormH
    formH-tag zero          = num >>=ₚ λ j → pureₚ (hypH j)
    formH-tag (suc zero)    =
      num >>=ₚ λ r → num >>=ₚ λ n → many n (num >>=ₚ refH-tag) >>=ₚ λ refs →
      num >>=ₚ λ b → many b (num >>=ₚ λ y → num >>=ₚ λ t → pureₚ (y , t)) >>=ₚ λ bs →
      num >>=ₚ λ s → pureₚ (ruleH r refs bs s)
    formH-tag (suc (suc _)) =
      num >>=ₚ λ X → num >>=ₚ λ j → num >>=ₚ λ k → many k caseP >>=ₚ λ cs → pureₚ (inductH X j cs)

    -- Steps are decoded and checked one at a time, so the decoded
    -- certificate is never held in memory as a whole.
    checkStreamH : (T : Table) → Tree (List ℕ × ℕ) → ℕ → ℕ → Code → Maybe (Tree (List ℕ × ℕ) × Code)
    checkStreamH T fs n zero    c = just (fs , c)
    checkStreamH T fs n (suc m) c =
      (num >>=ₚ formH-tag) c >>= λ r →
      Hashed.checkStepH T fs (fst r) >>= λ f →
      Hashed.forceF T f (λ f′ → checkStreamH T (insertT fs n f′) (suc n) m (snd r))

    goalsStreamH : (T : Table) → Tree (List ℕ × ℕ) → List Tm → ℕ → Code → Maybe ⊤
    goalsStreamH T fs []       zero    c = just tt
    goalsStreamH T fs (g ∷ gs) (suc k) c =
      (num >>=ₚ refH-tag) c >>= λ r →
      Hashed.resolveH T fs (fst r) >>= λ f →
      when (closed? (Hashed.conv T f) g) tt >>= λ _ → goalsStreamH T fs gs k (snd r)
    goalsStreamH T fs []       (suc k) c = nothing
    goalsStreamH T fs (g ∷ gs) zero    c = nothing

    runH : (T : Table) → List Tm → Code → Maybe ⊤
    runH T goals c =
      num c >>= λ r₁ → checkStreamH T leaf 0 (fst r₁) (snd r₁) >>= λ r₂ →
      num (snd r₂) >>= λ r₃ → goalsStreamH T (fst r₂) goals (fst r₃) (snd r₃)

    tableP : Parser Table
    tableP = num >>=ₚ λ n → tableH n 0 leaf

    -- CODE = N ENTRY^N  M FORM^M  K REF^K, checked as it is read.
    acceptsCodeH : List Tm → Code → Maybe ⊤
    acceptsCodeH goals c = tableP c >>= λ r → runH (fst r) goals (snd r)

    tableP-ok : (c : Code) {r : Table × Code} → tableP c ≡ just r → TableOk (fst r)
    tableP-ok c e with bind-inv (num c) _ e
    ... | (n , c₁) , _ , e₁ = tableH-ok n 0 leaf c₁ (leaf , leaf) e₁

    module StreamSound (T : Table) (ok : TableOk T) where
      open Hashed T
      open Hashed.Sound T (fst ok) (snd ok)

      stream-ok : (fs : Tree (List ℕ × ℕ)) → AllT GoodH fs → (n m : ℕ) (c : Code) {r : Tree (List ℕ × ℕ) × Code}
                → checkStreamH T fs n m c ≡ just r → AllT GoodH (fst r)
      stream-ok fs gf n zero    c refl = gf
      stream-ok fs gf n (suc m) c e with bind-inv ((num >>=ₚ formH-tag) c) _ e
      ... | (s , c₁) , _ , e₁ with bind-inv (checkStepH fs s) _ e₁
      ... | f , e₂ , e₃ =
            stream-ok (insertT fs n f) (allT-insert gf (step-okH fs gf s e₂) n) (suc n) m c₁
              (trans (sym (forceF-id f (λ f′ → checkStreamH T (insertT fs n f′) (suc n) m c₁))) e₃)

      goals-stream-ok : (fs : Tree (List ℕ × ℕ)) → AllT GoodH fs → (gs : List Tm) (k : ℕ) (c : Code)
                      → goalsStreamH T fs gs k c ≡ just tt → All (Valid []) gs
      goals-stream-ok fs gf []       zero    c refl = []
      goals-stream-ok fs gf (g ∷ gs) (suc k) c e with bind-inv ((num >>=ₚ refH-tag) c) _ e
      ... | (r , c₁) , _ , e₁ with bind-inv (resolveH fs r) _ e₁
      ... | f , ef , e₂ with bind-inv (when (closed? (conv f) g) tt) _ e₂
      ... | _ , ew , e₃ with when-inv (closed? (conv f) g) ew
      ... | (h , j) , _ = closed-fact (conv f) h j (fst (resolveH-ok fs gf r ef)) ∷ goals-stream-ok fs gf gs k c₁ e₃
      goals-stream-ok fs gf []       (suc k) c ()
      goals-stream-ok fs gf (g ∷ gs) zero    c ()

      run-ok : (goals : List Tm) (c : Code) → runH T goals c ≡ just tt → All (Valid []) goals
      run-ok goals c e with bind-inv (num c) _ e
      ... | (m , c₁) , _ , e₁ with bind-inv (checkStreamH T leaf 0 m c₁) _ e₁
      ... | (fs , c₂) , e₂ , e₃ with bind-inv (num c₂) _ e₃
      ... | (k , c₃) , _ , e₄ = goals-stream-ok fs (stream-ok leaf leaf 0 m c₁ e₂) goals k c₃ e₄

    -- Main theorem for compact certificates: if Agda evaluates
    -- `acceptsCodeH goals c` to `just tt`, every well-sorted ground instance
    -- of every goal is derivable.
    acceptsCodeH-sound : (goals : List Tm) (c : Code) → acceptsCodeH goals c ≡ just tt
                       → All (λ g → ∀ γ → GW γ (λ x → Occ x g) → Der (sub γ g)) goals
    acceptsCodeH-sound goals c e with bind-inv (tableP c) _ e
    ... | (T , c′) , e₁ , e₂ = all-map closed (StreamSound.run-ok T (tableP-ok c e₁) goals c′ e₂)

------------------------------------------------------------------------
-- Signatures given by tables, as in certificates exported from the Rust
-- checker (`schematic-kernel --agda`). A decision that evaluates to `yes`
-- supplies its proof through `witness`.

T? : {P : Set} → Dec P → Set
T? (yes _) = ⊤
T? (no _)  = ⊥

witness : {P : Set} (d : Dec P) → T? d → P
witness (yes p) _ = p
witness (no _)  ()

nth : {A : Set} → List A → ℕ → A → A
nth []       i       d = d
nth (x ∷ xs) zero    d = x
nth (x ∷ xs) (suc i) d = nth xs i d

nth-∈ : {A : Set} (xs : List A) (i : ℕ) (d : A) → nth xs i d ∈ (d ∷ xs)
nth-∈ []       i       d = here refl
nth-∈ (x ∷ xs) zero    d = there (here refl)
nth-∈ (x ∷ xs) (suc i) d with nth-∈ xs i d
... | here e  = here e
... | there m = there (there m)

_+_ : ℕ → ℕ → ℕ
zero  + n = n
suc m + n = suc (m + n)

+-zero : (m : ℕ) → m + zero ≡ m
+-zero zero    = refl
+-zero (suc m) = cong suc (+-zero m)

+-suc : (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero    n = refl
+-suc (suc m) n = cong suc (+-suc m n)

-- Positions k, k + 1, ... of the entries equal to s.
indicesOf : ℕ → List ℕ → ℕ → List ℕ
indicesOf k []       s = []
indicesOf k (o ∷ os) s = pick (o ≟ s) (k ∷ indicesOf (suc k) os s) (indicesOf (suc k) os s)

indicesOf-∈ : (junk s k : ℕ) (os : List ℕ) (i : ℕ) → nth os i junk ≡ s → ¬ (s ≡ junk)
            → (k + i) ∈ indicesOf k os s
indicesOf-∈ junk s k []       i       e n = ⊥-elim (n (sym e))
indicesOf-∈ junk s k (o ∷ os) zero    e n with o ≟ s
... | yes _ = here (+-zero k)
... | no ne = ⊥-elim (ne e)
indicesOf-∈ junk s k (o ∷ os) (suc i) e n with o ≟ s
... | yes _ = there (shift (indicesOf-∈ junk s (suc k) os i e n))
  where
    shift : (suc k + i) ∈ indicesOf (suc k) os s → (k + suc i) ∈ indicesOf (suc k) os s
    shift = transport (λ m → m ∈ indicesOf (suc k) os s) (sym (+-suc k i))
... | no _  = transport (λ m → m ∈ indicesOf (suc k) os s) (sym (+-suc k i))
                (indicesOf-∈ junk s (suc k) os i e n)

-- `outT`, `insT`: sort and argument sorts of each symbol; symbols past the
-- table have the sort `junk`. `varT`: sorts of eigenvariables (0 past it).
module Tables (outT : List ℕ) (insT : List (List ℕ)) (varT : List ℕ) (junk : ℕ)
              (rules : List Rule) where
  sig : Signature
  sig = record { out = λ c → nth outT c junk ; ins = λ c → nth insT c [] ; vs = λ x → nth varT x 0 }

  open Signature sig public
  open Calculus sig rules public

  ctors : ℕ → List ℕ
  ctors s = indicesOf 0 outT s

  -- Complete for every eigenvariable sort, provided `junk` is not one.
  complete-from : All (λ s → ¬ (s ≡ junk)) (0 ∷ varT) → (c x : ℕ) → out c ≡ vs x → c ∈ ctors (vs x)
  complete-from ok c x e = indicesOf-∈ junk (vs x) 0 outT c e (all-∈ ok (nth-∈ varT x 0))

  junk? : Dec (All (λ s → ¬ (s ≡ junk)) (0 ∷ varT))
  junk? = all? (λ s → not? (s ≟ junk)) (0 ∷ varT)

------------------------------------------------------------------------
-- Example: max l l l, admissible but not derivable, by induction on l.
-- Symbols: z = 0, s = 1 (sort N = 0), max = 2 (a predicate, given a sort of
-- its own so that every sort's constructors can be listed). Eigenvariables
-- all have sort N: L = 0, P = 1.

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
    out (suc (suc n)) = suc (suc n)   -- each predicate is its own sort

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

    -- The same proof as a certificate, run through the checking algorithm.
    ctors : ℕ → List ℕ
    ctors 0             = 0 ∷ 1 ∷ []
    ctors 1             = []
    ctors (suc (suc n)) = suc (suc n) ∷ []

    complete : (c x : ℕ) → out c ≡ 0 → c ∈ ctors 0
    complete 0             x e  = here refl
    complete 1             x e  = there (here refl)
    complete (suc (suc n)) x ()

    rules-wf : All RuleWF rules
    rules-wf = ([] , (tt , node refl (node refl [] ∷ var ∷ var ∷ [])))
             ∷ (((tt , node refl (var ∷ var ∷ var ∷ [])) ∷ []) , (tt , node refl (s′ 0 ∷ s′ 1 ∷ s′ 2 ∷ [])))
             ∷ []
      where
        s′ : (n : ℕ) → WSv (λ _ → 0) (S (var n)) 0
        s′ n = node refl (var ∷ [])

    open Algorithm rules-wf ctors complete

    certificate : List Form
    certificate =
        ruleF 0 [] ((0 , Z) ∷ []) nothing        -- 0: max z z z
      ∷ hypF (max P P P)                         -- 1: hypothesis
      ∷ ruleF 1 (ref 1 ∷ []) [] nothing          -- 2: max (s P) (s P) (s P)
      ∷ inductF 0 idem ((0 , []) ∷ (2 , 1 ∷ []) ∷ [])   -- 3: max L L L
      ∷ []

    goals : List Tm
    goals = idem ∷ max two two two ∷ []

    results : List Ref
    results = ref 3 ∷ at 3 ((0 , two) ∷ []) ∷ []

    accepted : accepts goals certificate results ≡ just tt
    accepted = refl

    from-algorithm : Der (max two two two)
    from-algorithm = all-∈ (accepts-sound goals certificate results accepted) (there (here refl)) var
                       (λ x o → ⊥-elim (vars-ground (max two two two) refl x o))

    -- Assuming the conclusion itself as the step case is rejected.
    circular : List Form
    circular =
        ruleF 0 [] ((0 , Z) ∷ []) nothing
      ∷ hypF (max (S P) (S P) (S P))
      ∷ inductF 0 idem ((0 , []) ∷ (1 , 1 ∷ []) ∷ [])
      ∷ []

    circular-rejected : accepts (idem ∷ []) circular (ref 2 ∷ []) ≡ nothing
    circular-rejected = refl

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
    sig = record { out = suc ; ins = λ { 0 → 0 ∷ [] ; _ → [] } ; vs = λ _ → 0 }

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

    ctors : ℕ → List ℕ
    ctors 0       = []
    ctors (suc c) = c ∷ []

    complete : (c x : ℕ) → suc c ≡ 0 → c ∈ ctors 0
    complete c x ()

    rules-wf : All RuleWF (intro ∷ elim ∷ [])
    rules-wf = ([] , (tt , node refl (var ∷ [])))
             ∷ (((tt , node refl (var ∷ [])) ∷ []) , (tt , node refl []))
             ∷ []

    open Algorithm rules-wf ctors complete

    -- The checker rejects the elim step from p X.
    elim-step-rejected :
      accepts (q ∷ []) (ruleF 0 [] [] (just (p (var 0))) ∷ ruleF 1 (ref 0 ∷ []) [] nothing ∷ [])
              (ref 1 ∷ []) ≡ nothing
    elim-step-rejected = refl
