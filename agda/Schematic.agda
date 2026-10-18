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
-- goal derivable. Differences from src/schematic.rs: hypotheses are kept as
-- judgments rather than step indices; the model checks explicitly that rule
-- bindings are well-sorted, which the Rust code obtains from its sort
-- discipline; parsing, names, `def` and hash-consing are not modelled.
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
    ws? : (t : Tm) (s : ℕ) → Dec (WS t s)
    ws? (var x) s with vs x ≟ s
    ... | yes refl = yes var
    ... | no ne    = no (λ { var → ne refl })
    ws? (node f ts) s with out f ≟ s | wss? ts (ins f)
    ... | yes e | yes w = yes (node e w)
    ... | no ne | _     = no (λ { (node e _) → ne e })
    ... | yes _ | no nw = no (λ { (node _ w) → nw w })

    wss? : (ts : List Tm) (ss : List ℕ) → Dec (WSs ts ss)
    wss? []       []       = yes []
    wss? []       (s ∷ ss) = no (λ ())
    wss? (t ∷ ts) []       = no (λ ())
    wss? (t ∷ ts) (s ∷ ss) with ws? t s | wss? ts ss
    ... | yes w | yes ws = yes (w ∷ ws)
    ... | no nw | _      = no (λ { (w ∷ _) → nw w })
    ... | yes _ | no nws = no (λ { (_ ∷ ws) → nws ws })

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


  -- `ctors s` lists the constructors of sort s; the checker relies on it
  -- naming every one (in Rust it is built from the declarations).
  module Algorithm (ctors : ℕ → List ℕ) (complete : ∀ c → c ∈ ctors (out c)) where

    Fact : Set
    Fact = List Tm × Tm

    ValidF : Fact → Set
    ValidF f = Valid (fst f) (snd f)

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

    resolve : List Fact → Ref → Maybe Fact
    resolve fs (ref n)   = lookup fs n
    resolve fs (at n bs) = lookup fs n >>= instFact bs

    resolve-ok : (fs : List Fact) → All ValidF fs → (r : Ref) {f : Fact}
               → resolve fs r ≡ just f → ValidF f
    resolve-ok fs vf (ref n) e = all-lookup n vf e
    resolve-ok fs vf (at n bs) e with bind-inv (lookup fs n) (instFact bs) e
    ... | ([] , J) , e₁ , e₂ with when-inv (all? (λ b → ws? (snd b) (vs (fst b))) bs) e₂
    ...   | ws , refl = inst-valid (all-lookup n vf e₁) (substOf bs) (λ x _ → substOf-ws bs ws x)
    resolve-ok fs vf (at n bs) e | ((h ∷ H) , J) , e₁ , ()

    resolveAll : List Fact → List Ref → Maybe (List Fact)
    resolveAll fs []       = just []
    resolveAll fs (r ∷ rs) = resolve fs r >>= λ f → resolveAll fs rs >>= λ qs → just (f ∷ qs)

    resolveAll-ok : (fs : List Fact) → All ValidF fs → (rs : List Ref) {qs : List Fact}
                  → resolveAll fs rs ≡ just qs → All ValidF qs
    resolveAll-ok fs vf []       refl = []
    resolveAll-ok fs vf (r ∷ rs) e
      with bind-inv (resolve fs r) (λ f → resolveAll fs rs >>= λ qs → just (f ∷ qs)) e
    ... | f , e₁ , e₂ with bind-inv (resolveAll fs rs) (λ qs → just (f ∷ qs)) e₂
    ...   | qs , e₃ , refl = resolve-ok fs vf r e₁ ∷ resolveAll-ok fs vf rs e₃

    bindFresh : ℕ → Tm → Env → Maybe Tm → Maybe Env
    bindFresh x t b nothing  = just (b [ x ↦ t ])
    bindFresh x t b (just _) = nothing

    bindAll : List (ℕ × Tm) → Env → Maybe Env
    bindAll []             b = just b
    bindAll ((x , t) ∷ bs) b = bindFresh x t b (b x) >>= bindAll bs

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

    ruleVars : Rule → List ℕ
    ruleVars r = varss (prem r) ++ vars (concl r)

    -- Bindings are well-sorted, and premise variables occur in the
    -- conclusion or the hypotheses.
    finish : Rule → List Fact → Env → Tm → Maybe Fact
    finish r qs b J =
      when (all? (λ y → ws? (total b y) (rs r y)) (ruleVars r)) tt >>= λ _ →
      when (all? (λ x → x ∈? (vars J ++ varss (hypsOf qs))) (varss (subs (total b) (prem r))))
           (hypsOf qs , J)

    checkRule : List Fact → ℕ → List Ref → List (ℕ × Tm) → Maybe Tm → Maybe Fact
    checkRule fs n refs binds stated =
      lookup R n >>= λ r →
      resolveAll fs refs >>= λ qs →
      bindAll binds empty >>= λ b₀ →
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

    checkCases : List Fact → ℕ → Tm → List ℕ → List (ℕ × List ℕ) → Maybe ⊤
    checkCases fs X J []       []              = just tt
    checkCases fs X J (c ∷ cs) ((m , ys) ∷ ks) =
      lookup fs m >>= λ f → when (caseOk? X J c ys f) tt >>= λ _ → checkCases fs X J cs ks
    checkCases fs X J []       (k ∷ ks)        = nothing
    checkCases fs X J (c ∷ cs) []              = nothing

    checkInduct : List Fact → ℕ → Tm → List (ℕ × List ℕ) → Maybe Fact
    checkInduct fs X J ks =
      when (X ∈? vars J) tt >>= λ _ → checkCases fs X J (ctors (vs X)) ks >>= λ _ → just ([] , J)

    checkStep : List Fact → Form → Maybe Fact
    checkStep fs (hypF J)                   = just ((J ∷ []) , J)
    checkStep fs (ruleF n refs binds stated) = checkRule fs n refs binds stated
    checkStep fs (inductF X J ks)           = checkInduct fs X J ks

    -- `fs` are the facts of earlier steps; references reach only them.
    checkSteps : List Fact → List Form → Maybe (List Fact)
    checkSteps fs []       = just fs
    checkSteps fs (s ∷ ss) = checkStep fs s >>= λ f → checkSteps (fs ++ (f ∷ [])) ss

    closed? : (f : Fact) (g : Tm) → Dec ((fst f ≡ []) × (snd f ≡ g))
    closed? ([] , J)      g = yes refl ×? (J ≟ₜ g)
    closed? ((h ∷ H) , J) g = no (λ { (() , _) })

    -- The i-th result names the step proving the i-th goal; goals may
    -- contain variables.
    checkGoals : List Fact → List Tm → List Ref → Maybe ⊤
    checkGoals fs []       []       = just tt
    checkGoals fs (g ∷ gs) (r ∷ rs) =
      resolve fs r >>= λ f → when (closed? f g) tt >>= λ _ → checkGoals fs gs rs
    checkGoals fs []       (r ∷ rs) = nothing
    checkGoals fs (g ∷ gs) []       = nothing

    accepts : List Tm → List Form → List Ref → Maybe ⊤
    accepts goals forms results = checkSteps [] forms >>= λ fs → checkGoals fs goals results


    --------------------------------------------------------------------
    -- Soundness of the algorithm

    data PremsAt (c : Env) : List Tm → List Fact → Set where
      []   : PremsAt c [] []
      cons : {p : Tm} {ps : List Tm} {f : Fact} {qs : List Fact}
           → instE c p ≡ just (snd f) → ValidF f → PremsAt c ps qs → PremsAt c (p ∷ ps) (f ∷ qs)

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

    rule-ok : (fs : List Fact) → All ValidF fs → (n : ℕ) (refs : List Ref)
              (binds : List (ℕ × Tm)) (stated : Maybe Tm) {f : Fact}
            → checkRule fs n refs binds stated ≡ just f → ValidF f
    rule-ok fs vf n refs binds stated e
      with bind-inv (lookup R n) _ e
    ... | r , er , e₁ with bind-inv (resolveAll fs refs) _ e₁
    ... | qs , eq , e₂ with bind-inv (bindAll binds empty) _ e₂
    ... | b₀ , _ , e₃ with bind-inv (conclude (concl r) stated b₀) _ e₃
    ... | b₁ , ec , e₄ with bind-inv (premisesMatch (prem r) qs b₁) _ e₄
    ... | b₂ , ep , e₅ with bind-inv (answer stated (instE b₂ (concl r))) (finish r qs b₂) e₅
    ... | J , ea , e₆ with bind-inv (when (all? (λ y → ws? (total b₂ y) (rs r y)) (ruleVars r)) tt) _ e₆
    ... | _ , ew , e₇ with when-inv (all? (λ y → ws? (total b₂ y) (rs r y)) (ruleVars r)) ew
    ... | wsAll , _ with when-inv (all? (λ x → x ∈? (vars J ++ varss (hypsOf qs)))
                                        (varss (subs (total b₂) (prem r)))) e₇
    ... | sideAll , refl =
          transport (Valid (hypsOf qs)) concl-eq
            (step-valid (lookup-∈ R n er) θ wθ (premsAt-sem b₂ (snd pm)) side)
      where
        θ : Subst
        θ = total b₂

        pm : (b₁ ⊑ b₂) × PremsAt b₂ (prem r) qs
        pm = premisesMatch-ok (prem r) qs b₁ (resolveAll-ok fs vf refs eq) ep

        concl-eq : sub θ (concl r) ≡ J
        concl-eq = inst-subst b₂ (concl r) (conclusion-ok (concl r) stated b₀ b₁ b₂ ec (fst pm) ea)

        wθ : ∀ y → OccR y r → WS (θ y) (rs r y)
        wθ y (inl o) = all-∈ wsAll (any-++ˡ (occs-varss (prem r) o))
        wθ y (inr o) = all-∈ wsAll (any-++ʳ (varss (prem r)) (occ-vars (concl r) o))

        side : ∀ x → Occs x (subs θ (prem r)) → Vars (hypsOf qs) (sub θ (concl r)) x
        side x o with ∈-++⁻ (vars J) (all-∈ sideAll (occs-varss (subs θ (prem r)) o))
        ... | inl m = inl (transport (Occ x) (sym concl-eq) (vars-occ J m))
        ... | inr m = inr (occs-any (varss-occs (hypsOf qs) m))

    all-map : {A : Set} {P Q : A → Set} → (∀ {x} → P x → Q x) → {xs : List A} → All P xs → All Q xs
    all-map f []       = []
    all-map f (p ∷ ps) = f p ∷ all-map f ps

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

    cases-ok : (fs : List Fact) → All ValidF fs → (X : ℕ) (J : Tm) (cs : List ℕ) (ks : List (ℕ × List ℕ))
             → checkCases fs X J cs ks ≡ just tt → All (SemCase X J) cs
    cases-ok fs vf X J []       []              refl = []
    cases-ok fs vf X J (c ∷ cs) ((m , ys) ∷ ks) e with bind-inv (lookup fs m) _ e
    ... | f , ef , e₁ with bind-inv (when (caseOk? X J c ys f) tt) _ e₁
    ...   | _ , ew , e₂ with when-inv (caseOk? X J c ys f) ew
    ...     | ok , _ = case-sem X J c ys f (all-lookup m vf ef) ok ∷ cases-ok fs vf X J cs ks e₂
    cases-ok fs vf X J []       (k ∷ ks) ()
    cases-ok fs vf X J (c ∷ cs) []       ()

    induct-ok : (fs : List Fact) → All ValidF fs → (X : ℕ) (J : Tm) (ks : List (ℕ × List ℕ)) {f : Fact}
              → checkInduct fs X J ks ≡ just f → ValidF f
    induct-ok fs vf X J ks e with bind-inv (when (X ∈? vars J) tt) _ e
    ... | _ , em , e₁ with when-inv (X ∈? vars J) em
    ...   | mX , _ with bind-inv (checkCases fs X J (ctors (vs X)) ks) _ e₁
    ...     | _ , ec , refl =
              Induction.induction X J (vars-occ J mX)
                (λ c ce → all-∈ (cases-ok fs vf X J (ctors (vs X)) ks ec)
                                (transport (λ s → c ∈ ctors s) ce (complete c)))

    step-ok : (fs : List Fact) → All ValidF fs → (s : Form) {f : Fact} → checkStep fs s ≡ just f → ValidF f
    step-ok fs vf (hypF J)                    refl = hyp-valid J
    step-ok fs vf (ruleF n refs binds stated) e    = rule-ok fs vf n refs binds stated e
    step-ok fs vf (inductF X J ks)            e    = induct-ok fs vf X J ks e

    steps-ok : (fs : List Fact) → All ValidF fs → (ss : List Form) {gs : List Fact}
             → checkSteps fs ss ≡ just gs → All ValidF gs
    steps-ok fs vf []       refl = vf
    steps-ok fs vf (s ∷ ss) e with bind-inv (checkStep fs s) _ e
    ... | f , e₁ , e₂ = steps-ok (fs ++ (f ∷ [])) (all-snoc vf (step-ok fs vf s e₁)) ss e₂

    closed-fact : (f : Fact) {g : Tm} → fst f ≡ [] → snd f ≡ g → ValidF f → Valid [] g
    closed-fact ([] , J) refl refl v = v

    goals-ok : (fs : List Fact) → All ValidF fs → (gs : List Tm) (rs : List Ref)
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
    accepts-sound goals forms results e with bind-inv (checkSteps [] forms) _ e
    ... | fs , e₁ , e₂ = all-map closed (goals-ok fs (steps-ok [] [] forms e₁) goals results e₂)

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

    complete : ∀ c → c ∈ ctors (out c)
    complete 0             = here refl
    complete 1             = there (here refl)
    complete (suc (suc n)) = here refl

    open Algorithm ctors complete

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
    from-algorithm with accepts-sound goals certificate results accepted
    ... | _ ∷ d ∷ [] = d var (λ x o → ⊥-elim (vars-ground (max two two two) refl x o))

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

    complete : ∀ c → c ∈ ctors (suc c)
    complete c = here refl

    open Algorithm ctors complete

    -- The checker rejects the elim step from p X.
    elim-step-rejected :
      accepts (q ∷ []) (ruleF 0 [] [] (just (p (var 0))) ∷ ruleF 1 (ref 0 ∷ []) [] nothing ∷ [])
              (ref 1 ∷ []) ≡ nothing
    elim-step-rejected = refl
