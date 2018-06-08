{-# OPTIONS --without-K #-}

--U = Set

open import hott
{-
open import Agda.Primitive public using (lzero; lsuc)
  renaming (Level to ULevel; _⊔_ to lmax)
open import hott using (U; Σ; Δ; δ; id; _∼_; transport)
-}

{-Proving that funext follows from univalence.

We do this in a rather general way:
The proof from VV (available at http://www.pitt.edu/~krk56/UA_implies_FE.pdf),
only uses a few facts about equivalences:

 1. The identity map is an equivalence.
 1a. Transports are equivalences (this follows from 1.)
 2. The diagonal map δ : Δ X → X is an equivalence.
 3. There is a map idtoeqv X=Y → Σ (f: X → Y) equiv(f), with
     idtoeqv(refl) = id + i(this follows from 1)

We may then state UA as "idtoequiv has a section", and this is sufficient
to prove funext.
 
So, we create a module with an input paramter being any type family satisfying
conditions 1 and 2, state UA accordingly, and prove funext from this
 -}
module UA_implies_FE
  {E : ∀ {i j} {X : U i} {Y : U j} → (X → Y) → U (lmax i j)}
  {I : ∀ {i} {X : U i} → (E {_} {_} {X} {X} id)} --id is an E-map
  {d : ∀ {i} {X : U i} → E {_} {_} {X} {Δ X} δ} --δ is an E-map
  {H : ∀ {i j} {X : U i} {Y : U j} {f g : X → Y} --homotopies preserve E-maps
    → E f → f ∼ g → E g}
  where
  
--The type of E-maps from X to Y. We don't need to know that this is an
--equivalence relation
_≅ᴱ_ : ∀ {i j} → U i → U j → U (lmax i j)
X ≅ᴱ Y = Σ λ(f : X → Y) → E f

-- fact 1a and 3
transportIsE : ∀ {i j} {X : U i} {Y : X → U j} {x y : X} (p : x ≡ y) →
             E (transport Y p)
transportIsE refl = I
transportIsE! : ∀ {i j} {X : U i} {Y : X → U j} {x y : X} (p : x ≡ y) →
             E (transport! Y p)
transportIsE! p = transportIsE (p ⁻¹)

-- Since we use transport id a lot here, we give it a special name.
-- Perhaps this should be standard?
tpMap : ∀ {i} {X : U i} {Y : U i} (p : X ≡ Y) → X → Y
tpMap p = transport id p

R : ∀ {i} {X : U i} {Y : U i}  (p : X ≡ Y) → X ≅ᴱ Y
R {X} {Y} p = (tpMap p , transportIsE p)

-- ua says R has a section.
module identitySection {i} {S : {X Y : U i} → X ≅ᴱ Y → X ≡ Y}
                       {UU : {X Y : U i} → (S {X} {Y}) isSectionOf (R {i} {X} {Y})}
                       where

    -- the assumptions give us an η law for E
    ηᴱ : {X Y : U i} (e : X ≅ᴱ Y) → fst (R (S e)) ≡ fst  e 
    ηᴱ {_} {_} e = ap fst (UU e) 

    -- A key point is that univalence says that in
    -- order to prove anything about all equivalences, it suffices to prove
    -- it about all transport maps. Going a step farther, we can actually
    -- prove facts about all equivalences by simply proving it for all
    -- identity functions.
    
    -- This needs a new name
    lift : ∀ {j} {X Y : U i} (P : (X → Y) → U j) → ((p : X ≡ Y) → P(tpMap p)) 
         → (f : X → Y) → E f → P f
    lift {j} {X} {Y} P φ f e = transport P η Φ
     where
      p : X ≡ Y
      p = S(f , e)
      Φ : P(tpMap p)
      Φ = φ p
      η : tpMap p ≡ f
      η = ηᴱ (f , e)

    liftFromId : ∀ {j} {X Y : U i} (P : {X Y : U i} → (X → Y) → U j) →
      ({Z : U i} → (P (id {_} {Z}))) → (f : X → Y) → E f → P f
    liftFromId P W f e = lift P witness f e where
      witness : {X Y : U i} (p : X ≡ Y) → P(tpMap p)
      witness refl = W 

    -- we need that any E is injective. It's easier to simply show that it's a
    -- section, using the "lifting" operations above.

    EisSect' : {X Y : U i} (p : X ≡ Y) → Σ (λ g → (tpMap p) isSectionOf g)
    EisSect' refl = (id , λ x → refl)

    EisSect : {X Y : U i} (f : X → Y) → E f → Σ (λ g → f isSectionOf g)
    EisSect = liftFromId (λ z → Σ (_isSectionOf_ z)) idsect where
        idsect : {Z : U i} → Σ (λ g → id isSectionOf g)
        idsect {Z} = id {i} {Z} , λ x → refl

    --E maps are sections, so injective
    EisInjective : {X A : U i} (f : X → A) → E f → (x y : X)
      → f x ≡ f y → x ≡ y
    EisInjective {X} {A} f e x y p  = cancelx · (ap g p) · cancely where
      g,p : Σ (_isSectionOf_ f)
      g,p = EisSect f e
      g : A → X
      g = fst g,p
      P : (x : X) → g (f x) ≡ x
      P = snd g,p
      cancelx : x ≡ g (f x)
      cancelx = P x ⁻¹
      cancely : g (f y) ≡ y
      cancely = P y

    -- starting with a path, transporting along that path is the same as
    -- precomposing with the corresponding transport map.
    transportIsComp : {X X' Y : U i} (p : X ≡ X') (g : X' → Y) →
       transport! (λ Z → Z → Y) p g ≡ (g ∘ tpMap p) 
    transportIsComp refl g = refl

    -- starting with an equivalence, precomposing is the same as transporting
    -- along the corresponding path.
    preCompIsTransport : {X X' Y : U i} (e : X ≅ᴱ X') (g : X' → Y) →
       transport! (λ Z → Z → Y) (S e) g ≡ (g ∘ (fst e)) 
    preCompIsTransport f,e g =  transportIsComp (S f,e) g · η where
      f = fst f,e
      η : (g ∘ tpMap (S f,e)) ≡ (g ∘ f)
      η = ap (λ f → g ∘ f) (ηᴱ f,e) 

    -- H is the proof that E is preserved by homotopies
    preCompIsE : {X X' Y : U i} (f : X ≅ᴱ X') → E(λ (g : X' → Y) → g ∘ (fst f))
    preCompIsE f,e = H (transportIsE! (S f,e)) (preCompIsTransport f,e)

    preCompδ : {X Y : U i} → (Δ X → Y) → X → Y
    preCompδ g = g ∘ δ

    preCompδIsE : {X Y : U i} → E (preCompδ {X} {Y})
    preCompδIsE = preCompIsE (δ , d)

    lemma₁ : {X : U i} → (π₁ ∘ (δ {_} {X})) ≡ (π₂ ∘ δ)
    lemma₁ {X} = refl

    lemma₂ : {X : U i} → π₁ {_} {X} ≡ π₂
    lemma₂ {X} = EisInjective preCompδ preCompδIsE π₁ π₂ lemma₁

    funext : {X Y : U i} (f₁ f₂ : X → Y) → (f₁ ∼ f₂) → f₁ ≡ f₂
    funext {X} {Y} f₁ f₂ h = ap composef lemma₂
       where
           f : X → Δ Y
           f x = (f₁ x , f₂ x , h x)
           composef : (Δ Y → Y) → X → Y
           composef k = k ∘ f
open identitySection
