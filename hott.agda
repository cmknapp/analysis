{-# OPTIONS --without-K #-}
{-# OPTIONS --type-in-type #-}

module hott where

U = Set

{-Basic types and type formers-}

-- Empty type and negation
data ⊥ : U where

¬ : (A : U) → U
¬ A = A → ⊥

-- unit type
data 𝟙 : U where
  ★ : 𝟙
  
-- unit induction. We write it as "rec", because whatever...
𝟙-rec : {C : 𝟙 → U} (c : C ★) (x : 𝟙) → C x
𝟙-rec c ★ = c

-- Booleans
data 𝟚 : U where
  true, false : 𝟚
  
data ℕ : U where
  zero : ℕ
  succ : ℕ → ℕ

-- Sigma types. We associate to the right. I.e., (x , y , z) is (x , (y , z))
-- In practice, we much more frequently have a string of Σs than a Σ over
--a Σ

infixr 1 _,_

record Σ {A : U} (B : A → U) : U where
  constructor _,_ 
  field fst : A
        snd : B fst
open Σ public
  
-- product
infixr 2 _×_
_×_ : (A B : U) → U
A × B = Σ {A} (λ x → B)
  
-- Prettier Pi types. Honestly, this doesn't come in handy often
Π : (A : U) (B : A → U) → U
Π A B = (x : A) → B x


-- identity types and some properites
infix 5 _≡_
data _≡_ {X : U} : X → X → U where
  refl : {x : X} → x ≡ x
  
_⁻¹ : {X : U} {x y : X} → x ≡ y → y ≡ x
refl ⁻¹ = refl

_·_ : {X : U} {x y z : X} → x ≡ y → y ≡ z → x ≡ z
refl · refl = refl

infixr 8 _·_
infix  2 _∎
infixr 2 _=⟨_⟩_

_=⟨_⟩_ : {A : U} (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
_ =⟨ p ⟩ q = p · q

_∎ : {A : U} (x : A) → x ≡ x
_ ∎ = refl

{- groupoid laws for identity types -}
refl-unitl : {X : U} {x y : X} (p : x ≡ y) → refl · p ≡ p
refl-unitl refl = refl
-- backwards
refl-unitl! : {X : U} {x y : X} (p : x ≡ y) → p ≡ refl · p
refl-unitl! p = (refl-unitl p) ⁻¹

refl-unitr : {X : U} {x y : X} (p : x ≡ y) → p · refl ≡ p
refl-unitr refl = refl
-- backwards
refl-unitr! : {X : U} {x y : X} (p : x ≡ y) → p ≡ p · refl
refl-unitr! p = (refl-unitr p) ⁻¹

path-assoc : {X : U } {x y z w : X} (p : x ≡ y) (q : y ≡ z) (r : z ≡ w) →
  (p · q) · r ≡ p · q · r
path-assoc refl refl refl = refl
-- backwards
path-assoc! : {X : U } {x y z w : X} (p : x ≡ y) (q : y ≡ z) (r : z ≡ w) →
  p · q · r ≡ (p · q) · r
path-assoc! p q r = (path-assoc p q r) ⁻¹


path-syml : {X : U} {x y : X} (p : x ≡ y) → p · p ⁻¹ ≡ refl
path-syml refl = refl
-- backwards
path-syml! : {X : U} {x y : X} (p : x ≡ y) → refl ≡ (p · p ⁻¹)
path-syml! p = (path-syml p) ⁻¹

path-symr : {X : U} {x y : X} (p : x ≡ y) → (p ⁻¹ · p) ≡ refl
path-symr refl = refl
-- backwards
path-symr! : {X : U} {x y : X} (p : x ≡ y) → refl ≡ (p ⁻¹ · p)
path-symr! p = (path-symr p) ⁻¹

-- right whiskering.
_·ᵣ_ : {X : U} {x y z : X} {p q : x ≡ y} → (p ≡ q) → (r : y ≡ z) →
     (p · r) ≡ (q · r)
α ·ᵣ refl = (refl-unitr _) · (α · (refl-unitr _) ⁻¹)

--and left whiskering
_·ₗ_ : {X : U} {x y z : X} {p q : y ≡ z} → (r : x ≡ y) → (p ≡ q) →
     (r · p) ≡ (r · q)
refl ·ₗ α = (refl-unitl _) · (α · (refl-unitl _) ⁻¹)

-- ap on paths, composition, etc
ap : {X : U} {Y : U} {x y : X} (f : X → Y) → x ≡ y → f x ≡ f y
ap f refl = refl

infixr 5 _∘_                       
_∘_ : {A : U} {B : A → U} {C : (x : A) → B x → U}
  (g : {x : A} (y : B x) → C x y) (f : Π A B) → (x : A) → C x (f x)
(g ∘ f) x = g (f x)

-- prettier application
infix 0 _$_
_$_ : {A : U} {B : A → U}  → Π A B → Π A B
f $ x = f x

id : {A : U} → A → A
id x = x

-- but agda can be a pain: agda doesn't believe that ap id p = p.
-- We have to make heavy use of this path, and it makes some 
-- should-be-judgmental equalities into propositional equalities.
apid : {A : U} {x y : A} {p : x ≡ y} → (ap id p) ≡ p
apid {A} {_} {._} {refl} = refl


-- K combinator (constant map)
const : {A B : U} → B → A → B
const b a = b

-- This was ripped from the "real" hott-agda library.
-- I don't see why they did it this way;
coe : {A B : U} (p : A ≡ B) → A → B
coe refl x = x

coe! : {A B : U} (p : A ≡ B) → B → A
coe! p x = coe (p ⁻¹) x

-- transport forward,
transport : {A : U} (B : A → U) {x y : A} → x ≡ y → B x → B y
transport B p = coe $ ap B p

--transport backward
transport! : {A : U} (B : A → U) {x y : A} → x ≡ y → B y → B x
transport! B p = transport B (p ⁻¹)

{-copying some stuff about paths over a path from the "real" HoTT-Agda library
 The point is that we can define the type of path over a path directly, and
 this is often a nicer way to write things.
-}

-- transport in idenity types. This needs a new name
tpid : {A : U} {a : A} {x y : A} (p : x ≡ y) (q : x ≡ a) →
  transport (λ x → x ≡ a) p q ≡ (p ⁻¹ · q)
tpid refl refl = refl


PathOver : {A : U} (B : A → U) {x y : A} (p : x ≡ y) (u : B x) (v : B y) → U
PathOver B p u v = (transport B p u) ≡ v

syntax PathOver B p u v =
  u ≡ v [ B ↓ p ]

-- apd f p gives us a path from x to y lying over p
apd : {A : U} {B : A → U} {x y : A} (f : (x : A) → B x) (p : x ≡ y) →
  f x ≡ f y [ B ↓ p ]
apd f refl = refl

-- - some useful things about transport and paths
-- tp respects composition
tp· : {A : U} {C : A → U} {x y z : A} (p : x ≡ y) (q : y ≡ z) (u : C x) →
    transport C q (transport C p u) ≡ transport C (p · q) u
tp· refl refl _ = refl

tp∘ : {A B : U} { f : A → B} {E : B → U} {x y : A} (p : x ≡ y) (u : E (f x)) →
    transport (E ∘ f) p u ≡ transport E (ap f p) u
tp∘ refl _ = refl

tpπ : {A : U} {P Q : A → U} {x y : A} {f : (x : A) → (P x → Q x)} (p : x ≡ y)
  (u : P x) → transport Q p (f x u) ≡ f y (transport P p u)
tpπ refl _ = refl

-- tp in identity paths is nicely behaved
tp=ₗ : {A : U} {x y a : A} (q : a ≡ x) (p : x ≡ y) → 
    transport (λ x → a ≡ x) p q ≡ (q · p)
tp=ₗ q refl = refl-unitr! q

tp=ᵣ : {A : U} {x y a : A} (q : x ≡ a) (p : x ≡ y) → 
    transport (λ x → x ≡ a) p q ≡ (p ⁻¹ · q)
tp=ᵣ q refl = refl-unitl! q

tp=ₛ : {A : U} {x y : A} (q : x ≡ x) (p : x ≡ y) →
    transport (λ x → x ≡ x) p q ≡ p ⁻¹ · (q · p)
tp=ₛ q refl =  refl-unitr! q ·  refl-unitl! (q · refl)

-- the "introduction rule" for ≡ in Σ types
-- We prove that ap _ₗ and ap _ᵣ are eliminators with the
-- (propositional) η and β laws later.
pair= : {A : U} {B : A → U} {a a' : A} {b : B a} {b' : B a'}
  (p : a ≡ a') (q : b ≡ b' [ B ↓ p ]) → (a , b) ≡ (a' , b')
pair= refl q = ap (_,_ _) q

{-contractible types, propositions and sets.
Since this is for doing analysis, I don't need anything higher.
-}

isContr : U → U
isContr A = Σ {A} (λ x → (y : A) → x ≡ y)

-- the center, and the contraction; this is clearer
-- than simply using projections.
-- We keep the contractibility proof explicit.
-- I don't know if this is the right thing to do.
center : {A : Set} → (isContr A) → A
center  = fst

contraction : {A : Set} → (c : isContr A) → ((y : A) → center c ≡ y)
contraction = snd

isProp : U → U
isProp A = (x y : A) → x ≡ y

isSet : U → U
isSet A = (x y : A) → isProp (x ≡ y)

{-Equivalences. We take "contractible fibers" as our definition.
  We'll provide the other definitions, and proofs of equivalence
  later.
-}
fiber : {A B : U} → (A → B) → B → U
fiber f b = Σ (λ x → f x ≡ b)

isEquiv : {A B : U} → (A → B) → U
isEquiv {A} {B} f = (b : B) → isContr (fiber f b)

infix 3 _≃_
_≃_ : U → U → U
A ≃ B = Σ {A → B} (λ f → isEquiv f)

-- extracting an inverse. We prove it *is* an inverse later
_! : {A B : U} (f : A → B) → {e : isEquiv f} → B → A
(f !) {e} b = fst $ center (e b)

{- Properties of contractibility, props and sets -}

1-is-contr : isContr 𝟙
1-is-contr = (★ , 𝟙-rec refl)

contr-is-prop : {A : U} → isContr A → isProp A
contr-is-prop (c , paths) x y = x =⟨ paths x ⁻¹ ⟩
                                c =⟨ paths y ⟩
                                y ∎


-- inhabited props are contractible
inhProp-isContr : {P : U} → P → isProp P → isContr P
inhProp-isContr p w = (p , w p)

-- contractible types are propositions
contr-isProp : {P : U} → isContr P → isProp P
contr-isProp (c , p) x y = p x ⁻¹ · p y

-- propositions have contractible identity types.
-- This is surprisingly non-trivial: we need a clever
-- path induction.
-- The point is that we can show that for *any* y z, we can show
-- that any path y ≡ z is the composition of g y and g z (modulo
-- direction of the path).
propId-isContr : (P : U) → isProp P → (x y : P) → isContr (x ≡ y)
propId-isContr P p x y = (p x y , lemma₂) where
               g : (y : P) → x ≡ y
               g = p x
               lemma₁ : {a b : P} (q : a ≡ b) → q ≡ (g a ⁻¹ · g b)
               lemma₁ {a} {.a} refl = path-symr (g a) ⁻¹
               lemma₂ : (q : x ≡ y) → p x y ≡ q
               lemma₂ q = (p x y) =⟨ lemma₁ (p x y) ⟩ (g x ⁻¹ · g y)
                                  =⟨ (lemma₁ q) ⁻¹ ⟩ q ∎
                                  
-- As an immediate corollary, all props are sets:
prop-isSet : (P : U) → isProp P → isSet P
prop-isSet P p x y = contr-isProp (propId-isContr P p x y)

-- Now, we can show that when props P and Q imply each other, then
-- they are equivalent. As the center of fib(b) we take f g b with the
-- path defined by isProp Q;
-- to get contractibility, we use pair= and the fact that props are sets.
biimplication-isEquiv : {P Q : U} → isProp P → isProp Q →
  (f : P → Q) → (Q → P) → isEquiv f
biimplication-isEquiv {P} {Q} p q f g b = ((gb , q fgb b) , lemma) where
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
contr-areEquiv : (C D : U) {e : isContr C} {f : isContr D} → C ≃ D
contr-areEquiv C D {(c , p)} {(d , q)} =
  (const d , biimplication-isEquiv propC propD (const d) (const c)) where
  propC = contr-isProp (c , p)
  propD = contr-isProp (d , q)
  
-- 𝟙 is contractible:
𝟙-isContr : isContr 𝟙
𝟙-isContr = (★ , f) where
  f : (x : 𝟙) → ★ ≡ x
  f ★ = refl

-- some simple corollaries. Ostensibly, these are useful, but really we
-- use contractibility more than (≃1)
contr-is-1 : {C : U} → isContr C → C ≃ 𝟙
contr-is-1 {C} e = contr-areEquiv C 𝟙 {e} {𝟙-isContr}

inhProp-is-1 : {P : U} → P → isProp P → P ≃ 𝟙
inhProp-is-1 p w = contr-is-1 (inhProp-isContr p w)

{- homotopies; naturality and other basic properties.
   -}

module homotopies {A : U} {C : A → U} where
    _∼_ : (f g : Π A C) → U
    _∼_ f g = (x : A) → (f x ≡ g x)
    infix 3 _∼_
open homotopies public

homotopy-natural : {A B : U} {f g : A → B} (H : f ∼ g) {x y : A} (p : x ≡ y)
  → (H x · ap g p) ≡ (ap f p · H y)
homotopy-natural H refl = refl-unitr (H _) · (refl-unitl (H _) ⁻¹)

-- When H : f ∼ id, then Hf = fH
-- We whisker the naturality square Hfx · Hx ≡ fHx · Hx with Hx⁻¹ to get
-- the result.

homotopy-switch : {A : U} (f : A → A) (H : f ∼ id) → ap f ∘ H ∼ H ∘ f
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

-- Section and retraction. We use f ↯ g to mean "f is a section of g";
-- As a mnemonic, read f ↯ g as "f splits g", and as we all know,
-- every epi splits. (Ha!)
module section {X Y : U} where
  _isSectionOf_ : (X → Y) → (Y → X) → U
  f isSectionOf g = (g ∘ f) ∼ id
  infix 3 _isSectionOf_
open section public

-- The diagonal of a type, and the diagonal map.
-- Perhaps this should be elsewhere?
Δ : U → U
Δ Y = Σ {Y} (λ x → Σ λ y → x ≡ y)

δ : {X : U} → X → Δ X
δ x = (x , x , refl)

-- two definitions for the the inverse of δ 
π₁ : {X : U} → Δ X → X
π₁ (x , _ , _) = x

π₂ : {X : U} → Δ X → X
π₂ (_ , y , _) = y
