{-# OPTIONS --without-K #-}

module hott where

{- we follow the "real" HoTT-Agda library in renaming Set. However,
   we use U instead of Type
-}

open import Agda.Primitive public using (lzero; lsuc)
  renaming (Level to ULevel; _⊔_ to lmax)

U : (i : ULevel) → Set (lsuc i)
U i = Set i

U₀ = U lzero
U₁ = U (lsuc lzero)

{-Basic types and type formers-}

-- Empty type and negation
data ⊥ : U₀ where

¬ : ∀ {i} (A : U i) → U i
¬ A = A → ⊥

-- unit type
data 𝟙 : U₀ where
  ⋆ : 𝟙
  
-- unit induction. We write it as "rec", because whatever...
𝟙-rec : ∀ {i} {C : 𝟙 → U i} (c : C ⋆) (x : 𝟙) → C x
𝟙-rec c ⋆ = c

-- Booleans
data 𝟚 : U₀ where
  true, false : 𝟚
  
data ℕ : U₀ where
  zero : ℕ
  succ : ℕ → ℕ

-- Sigma types. We associate to the right. I.e., (x , y , z) is (x , (y , z))
-- In practice, we much more frequently have a string of Σs than a Σ over
--a Σ

infixr 1 _,_

record Σ {i j} {A : U i} (B : A → U j) : U (lmax i j) where
  constructor _,_ 
  field fst : A
        snd : B fst
open Σ public
  
-- product
infixr 2 _×_
_×_ : ∀ {i j} (A : U i) (B : U j) → U (lmax i j)
A × B = Σ {_} {_} {A} (λ x → B)
  
-- Prettier Pi types. Honestly, this doesn't come in handy often
Π : ∀ {i j} (A : U i) (B : A → U j) → U (lmax i j)
Π A B = (x : A) → B x


-- identity types and some properites
infix 5 _≡_
data _≡_ {i} {A : U i} : A → A → U i where
  refl : {x : A} → x ≡ x
  
_⁻¹ : ∀ {i} {A : U i} {x y : A} → x ≡ y → y ≡ x
refl ⁻¹ = refl

_·_ : ∀ {i} {A : U i} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
refl · refl = refl

infixr 8 _·_
infix  2 _∎
infixr 2 _=⟨_⟩_

_=⟨_⟩_ : ∀ {i} {A : U i} (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
_ =⟨ p ⟩ q = p · q

_∎ : ∀ {i} {A : U i} (x : A) → x ≡ x
_ ∎ = refl

{- groupoid laws for identity types -}
refl-unitl : ∀ {i} {A : U i} {x y : A} (p : x ≡ y) → refl · p ≡ p
refl-unitl refl = refl
-- backwards
refl-unitl! : ∀ {i} {A : U i} {x y : A} (p : x ≡ y) → p ≡ refl · p
refl-unitl! p = (refl-unitl p) ⁻¹

refl-unitr : ∀ {i} {A : U i} {x y : A} (p : x ≡ y) → p · refl ≡ p
refl-unitr refl = refl
-- backwards
refl-unitr! : ∀ {i} {A : U i} {x y : A} (p : x ≡ y) → p ≡ p · refl
refl-unitr! p = (refl-unitr p) ⁻¹

path-assoc : ∀ {i} {A : U i} {x y z w : A} (p : x ≡ y) (q : y ≡ z) (r : z ≡ w) →
  (p · q) · r ≡ p · q · r
path-assoc refl refl refl = refl
-- backwards
path-assoc! : ∀ {i} {A : U i} {x y z w : A} (p : x ≡ y) (q : y ≡ z) (r : z ≡ w) →
  p · q · r ≡ (p · q) · r
path-assoc! p q r = (path-assoc p q r) ⁻¹


path-syml : ∀ {i} {A : U i} {x y : A} (p : x ≡ y) → p · p ⁻¹ ≡ refl
path-syml refl = refl
-- backwards
path-syml! : ∀ {i} {A : U i} {x y : A} (p : x ≡ y) → refl ≡ (p · p ⁻¹)
path-syml! p = (path-syml p) ⁻¹

path-symr : ∀ {i} {A : U i} {x y : A} (p : x ≡ y) → (p ⁻¹ · p) ≡ refl
path-symr refl = refl
-- backwards
path-symr! : ∀ {i} {A : U i} {x y : A} (p : x ≡ y) → refl ≡ (p ⁻¹ · p)
path-symr! p = (path-symr p) ⁻¹

-- right whiskering.
_·ᵣ_ : ∀ {i} {A : U i} {x y z : A} {p q : x ≡ y} → (p ≡ q) → (r : y ≡ z) →
     (p · r) ≡ (q · r)
α ·ᵣ refl = (refl-unitr _) · (α · (refl-unitr _) ⁻¹)

--and left whiskering
_·ₗ_ : ∀ {i} {A : U i} {x y z : A} {p q : y ≡ z} → (r : x ≡ y) → (p ≡ q) →
     (r · p) ≡ (r · q)
refl ·ₗ α = (refl-unitl _) · (α · (refl-unitl _) ⁻¹)

-- ap on paths, composition, etc
ap : ∀ {i j} {A : U i} {B : U j} {x y : A} (f : A → B) → x ≡ y → f x ≡ f y
ap f refl = refl

infixr 5 _∘_                       
_∘_ : ∀ {i j k} {A : U i} {B : A → U j} {C : (x : A) → B x → U k}
  (g : {x : A} (y : B x) → C x y) (f : Π A B) → (x : A) → C x (f x)
(g ∘ f) x = g (f x)

-- prettier application
infix 0 _$_
_$_ : ∀ {i j} {A : U i} {B : A → U j}  → Π A B → Π A B
f $ x = f x

id : ∀ {i} {A : U i} → A → A
id x = x

-- but agda can be a pain: agda doesn't believe that ap id p = p.
-- We have to make heavy use of this path, and it makes some 
-- should-be-judgmental equalities into propositional equalities.
apid : ∀ {i} {A : U i} {x y : A} {p : x ≡ y} → (ap id p) ≡ p
apid {_} {A} {_} {._} {refl} = refl


-- K combinator (constant map)
const : ∀ {i j} {A : U i} {B : U j} → B → A → B
const b a = b

-- This was ripped from the "real" hott-agda library.
-- I don't see why they did it this way;
coe : ∀ {i} {A B : U i} (p : A ≡ B) → A → B
coe refl x = x

coe! : ∀ {i} {A B : U i} (p : A ≡ B) → B → A
coe! p x = coe (p ⁻¹) x

-- transport forward,
transport : ∀ {i j} {A : U i} (B : A → U j) {x y : A} → x ≡ y → B x → B y
transport B p = coe $ ap B p

--transport backward
transport! : ∀ {i j} {A : U i} (B : A → U j) {x y : A} → x ≡ y → B y → B x
transport! B p = transport B (p ⁻¹)

{-copying some stuff about paths over a path from the "real" HoTT-Agda library
 The point is that we can define the type of path over a path directly, and
 this is often a nicer way to write things.
-}

-- transport in idenity types. This needs a new name
tpid : ∀ {i} {A : U i} {a : A} {x y : A} (p : x ≡ y) (q : x ≡ a) →
  transport (λ x → x ≡ a) p q ≡ (p ⁻¹ · q)
tpid refl refl = refl


PathOver : ∀ {i j} {A : U i} (B : A → U j) {x y : A} (p : x ≡ y)
         (u : B x) (v : B y) → U j
PathOver B p u v = (transport B p u) ≡ v

syntax PathOver B p u v =
  u ≡ v [ B ↓ p ]

-- apd f p gives us a path from x to y lying over p
apd : ∀ {i j} {A : U i} {B : A → U j} {x y : A} (f : (x : A) → B x)
  (p : x ≡ y) → f x ≡ f y [ B ↓ p ]
apd f refl = refl

-- - some useful things about transport and paths
-- tp respects composition
tp· : ∀ {i j} {A : U i} {C : A → U j} {x y z : A} (p : x ≡ y) (q : y ≡ z)
  (u : C x) →  transport C q (transport C p u) ≡ transport C (p · q) u
tp· refl refl _ = refl

tp∘ : ∀ {i j k} {A : U i} {B : U j} { f : A → B} {E : B → U k} {x y : A} (p : x ≡ y) (u : E (f x)) →
    transport (E ∘ f) p u ≡ transport E (ap f p) u
tp∘ refl _ = refl

tpπ : ∀ {i j} {A : U i} {P Q : A → U j} {x y : A} {f : (x : A) → (P x → Q x)} (p : x ≡ y)
  (u : P x) → transport Q p (f x u) ≡ f y (transport P p u)
tpπ refl _ = refl

-- tp in identity paths is nicely behaved
tp=ₗ : ∀ {i} {A : U i} {x y a : A} (q : a ≡ x) (p : x ≡ y) → 
    transport (λ x → a ≡ x) p q ≡ (q · p)
tp=ₗ q refl = refl-unitr! q

tp=ᵣ : ∀ {i} {A : U i} {x y a : A} (q : x ≡ a) (p : x ≡ y) → 
    transport (λ x → x ≡ a) p q ≡ (p ⁻¹ · q)
tp=ᵣ q refl = refl-unitl! q

tp=ₛ : ∀ {i} {A : U i} {x y : A} (q : x ≡ x) (p : x ≡ y) →
    transport (λ x → x ≡ x) p q ≡ p ⁻¹ · (q · p)
tp=ₛ q refl =  refl-unitr! q ·  refl-unitl! (q · refl)

-- the "introduction rule" for ≡ in Σ types
-- We prove that ap _ₗ and ap _ᵣ are eliminators with the
-- (propositional) η and β laws later.
pair= : ∀ {i j} {A : U i} {B : A → U j} {a a' : A} {b : B a} {b' : B a'}
  (p : a ≡ a') (q : b ≡ b' [ B ↓ p ]) → (a , b) ≡ (a' , b')
pair= refl q = ap (_,_ _) q

{-contractible types, propositions and sets.
Since this is for doing analysis, I don't need anything higher.
-}

isContr : ∀ {i} → U i → U i
isContr A = Σ {_} {_} {A} (λ x → (y : A) → x ≡ y)

-- the center, and the contraction; this is clearer
-- than simply using projections.
-- We keep the contractibility proof explicit.
-- I don't know if this is the right thing to do.
center : ∀ {i} {A : U i} → (isContr A) → A
center  = fst

contraction : ∀ {i} {A : U i} → (c : isContr A) → ((y : A) → center c ≡ y)
contraction = snd

isProp : ∀ {i} → U i → U i
isProp A = (x y : A) → x ≡ y

isSet : ∀ {i} → U i → U i
isSet A = (x y : A) → isProp (x ≡ y)

{-Equivalences. We take "contractible fibers" as our definition.
  We'll provide the other definitions, and proofs of equivalence
  later.
-}
fiber : ∀ {i j} {A : U i} {B : U j} → (A → B) → B → U (lmax i j)
fiber f b = Σ (λ x → f x ≡ b)

isEquiv : ∀ {i j} {A : U i} {B : U j} → (A → B) → U (lmax i j)
isEquiv {_} {_} {A} {B} f = (b : B) → isContr (fiber f b)

infix 3 _≃_
_≃_ : ∀ {i j} → U i → U j → U (lmax i j)
A ≃ B = Σ {_} {_} {A → B} (λ f → isEquiv f)

-- extracting an inverse. We prove it *is* an inverse later
_! : ∀ {i j} {A : U i} {B : U j} (f : A → B) → {e : isEquiv f} → B → A
(f !) {e} b = fst $ center (e b)

{- Properties of contractibility, props and sets -}

1-is-contr : isContr 𝟙
1-is-contr = (⋆ , 𝟙-rec refl)

contr-is-prop : ∀ {i} {A : U i} → isContr A → isProp A
contr-is-prop (c , paths) x y = x =⟨ paths x ⁻¹ ⟩
                                c =⟨ paths y ⟩
                                y ∎


-- inhabited props are contractible
inhProp-isContr : ∀ {i} {P : U i} → P → isProp P → isContr P
inhProp-isContr p w = (p , w p)

-- contractible types are propositions
contr-isProp : ∀ {i} {P : U i} → isContr P → isProp P
contr-isProp (c , p) x y = p x ⁻¹ · p y

-- propositions have contractible identity types.
-- This is surprisingly non-trivial: we need a clever
-- path induction.
-- The point is that we can show that for *any* y z, we can show
-- that any path y ≡ z is the composition of g y and g z (modulo
-- direction of the path).
propId-isContr : ∀ {i} (P : U i) → isProp P → (x y : P) → isContr (x ≡ y)
propId-isContr P p x y = (p x y , lemma₂) where
               g : (y : P) → x ≡ y
               g = p x
               lemma₁ : {a b : P} (q : a ≡ b) → q ≡ (g a ⁻¹ · g b)
               lemma₁ {a} {.a} refl = path-symr (g a) ⁻¹
               lemma₂ : (q : x ≡ y) → p x y ≡ q
               lemma₂ q = (p x y) =⟨ lemma₁ (p x y) ⟩ (g x ⁻¹ · g y)
                                  =⟨ (lemma₁ q) ⁻¹ ⟩ q ∎
                                  
-- As an immediate corollary, all props are sets:
prop-isSet : ∀ {i} (P : U i) → isProp P → isSet P
prop-isSet P p x y = contr-isProp (propId-isContr P p x y)

-- Now, we can show that when props P and Q imply each other, then
-- they are equivalent. As the center of fib(b) we take f g b with the
-- path defined by isProp Q;
-- to get contractibility, we use pair= and the fact that props are sets.
biimplication-isEquiv : ∀ {i} {j} {P : U i} {Q : U j} → isProp P → isProp Q →
  (f : P → Q) → (Q → P) → isEquiv f
biimplication-isEquiv {_} {_} {P} {Q} p q f g b =
               ((gb , q fgb b) , lemma) where
                      gb  = g b
                      fgb = f (g b)
                      prop : (x : fiber f b) →
                        (q fgb b ≡ (snd x) [ (λ x → f x ≡ b) ↓ p gb (fst x) ])
                        --prop-isSet Q q gives us that identity types for all
                        --elements (in this case, fx and b) are mere props.
                        --So we take two paths to get an equality.
                      prop (x , r) = (prop-isSet Q q) (f x) b
                        (transport ((λ x → f x ≡ b)) (p gb x) (q fgb b)) r
                      lemma : (x : fiber f b) → (gb , q fgb b) ≡ x
                      lemma (x , path) = pair= (p (g b) x) (prop (x , path))
                      
-- Corollary: contractible types are all equivalent
contr-areEquiv : ∀ {i} {j} (C : U i) (D : U j) {e : isContr C}
  {f : isContr D} → C ≃ D
contr-areEquiv C D {(c , p)} {(d , q)} =
  (const d , biimplication-isEquiv propC propD (const d) (const c)) where
  propC = contr-isProp (c , p)
  propD = contr-isProp (d , q)
  
-- 𝟙 is contractible:
𝟙-isContr : isContr 𝟙
𝟙-isContr = (⋆ , f) where
  f : (x : 𝟙) → ⋆ ≡ x
  f ⋆ = refl

-- some simple corollaries. Ostensibly, these are useful, but really we
-- use contractibility more than (≃1)
contr-is-1 : ∀ {i} {C : U i} → isContr C → C ≃ 𝟙
contr-is-1 {_} {C} e = contr-areEquiv C 𝟙 {e} {𝟙-isContr}

inhProp-is-1 : ∀ {i} {P : U i} → P → isProp P → P ≃ 𝟙
inhProp-is-1 p w = contr-is-1 (inhProp-isContr p w)

{- homotopies; naturality and other basic properties.
   -}

module homotopies {i j} {A : U i} {C : A → U j} where
    _∼_ : (f g : Π A C) → U (lmax i j)
    _∼_ f g = (x : A) → (f x ≡ g x)
    infix 3 _∼_
open homotopies public

homotopy-natural : ∀ {i j}  {A : U i} {B : U j} {f g : A → B}
  (H : f ∼ g) {x y : A} (p : x ≡ y) → (H x · ap g p) ≡ (ap f p · H y)
homotopy-natural H refl = refl-unitr (H _) · (refl-unitl (H _) ⁻¹)

-- When H : f ∼ id, then Hf = fH
-- We whisker the naturality square Hfx · Hx ≡ fHx · Hx with Hx⁻¹ to get
-- the result.

homotopy-switch : ∀ {i} {A : U i} (f : A → A) (H : f ∼ id) → ap f ∘ H ∼ H ∘ f
homotopy-switch f H x = fHx =⟨ refl-unitr! fHx ⟩        (fHx · refl)
                            =⟨ fHx ·ₗ path-syml! Hx ⟩   (fHx · (Hx · Hx!))
                            =⟨ path-assoc! fHx Hx Hx! ⟩ ((fHx · Hx) · Hx!)
                            =⟨ (naturality ⁻¹) ·ᵣ Hx! ⟩  ((Hfx · Hx) · Hx!)
                            =⟨ path-assoc Hfx Hx Hx! ⟩  (Hfx · (Hx · Hx!))
                            =⟨ Hfx ·ₗ path-syml Hx ⟩    (Hfx · refl)
                            =⟨ refl-unitr Hfx ⟩ Hfx ∎ where
                fHx = ap f (H x)
                Hfx = H (f x)
                Hx = H x
                Hx! = (H x) ⁻¹
                --We need to fill in some extra cells, since agda
                --doesn't believe that ap id p = p.
                natsquare : (Hfx · ap id Hx) ≡ (fHx · Hx)
                natsquare = homotopy-natural H (H x)
                naturality : (Hfx · Hx) ≡ (fHx · Hx)
                naturality = Hfx ·ₗ apid ⁻¹ · natsquare

-- Section and retraction.
module section {i} {j} {A : U i} {B : U j} where
  _isSectionOf_ : (A → B) → (B → A) → U i
  f isSectionOf g = (g ∘ f) ∼ id
  infix 3 _isSectionOf_
open section public

-- The diagonal of a type, and the diagonal map.
-- Perhaps this should be elsewhere?
Δ : ∀ {i} → U i → U i
Δ B = Σ {_} {_} {B} (λ x → Σ λ y → x ≡ y)

δ : ∀ {i} {A : U i} → A → Δ A
δ x = (x , x , refl)

-- two definitions for the the inverse of δ 
π₁ : ∀ {i} {A : U i} → Δ A → A
π₁ (x , _ , _) = x

π₂ : ∀ {i} {A : U i} → Δ A → A
π₂ (_ , y , _) = y
