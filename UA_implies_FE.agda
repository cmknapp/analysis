{-# OPTIONS --without-K #-}
{-# OPTIONS --type-in-type #-}

--U = Set

open import hott

{-Proving that funext follows from univalence.

We do this in an incredibly general way:
In the proof from VV (informalized by Gambino, Kapulkin and Lumsdaine),
we only use a few facts about equivalences:

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
module UA_implies_FE {E : {X Y : U} → (X → Y) → U}
  {i : {X : U} → (E {X} {X} id)} {d : {X : U} → E {X} {Δ X} δ}
  {H : {X Y : U} {f g : X → Y} → E f → f ∼ g → E g} where
  
_≅ᴱ_ : U → U → U
X ≅ᴱ Y = Σ λ(f : X → Y) → E f

-- fact 1a and 3
transportIsE : {X : U} {Y : X → U} {x y : X} (p : x ≡ y) →
             E (transport Y p)
transportIsE refl = i
transportIsE! : {X : U} {Y : X → U} {x y : X} (p : x ≡ y) →
             E (transport! Y p)
transportIsE! p = transportIsE (p ⁻¹)

-- Since we use transport id a lot here, we give it a special name.
-- Perhaps this should be standard?
tpMap : {X Y : U} (p : X ≡ Y) → X → Y
tpMap p = transport id p

R : {X Y : U} (p : X ≡ Y) → X ≅ᴱ Y
R {X} {Y} p = (tpMap p , transportIsE p)

-- ua says R has a section.
module identitySection {S : {X Y : U} → X ≅ᴱ Y → X ≡ Y}
                       {u : {X Y : U} → (S {X} {Y}) isSectionOf (R {X} {Y})}
                       where

    univalence' : {X Y : U} → (f : X → Y)(e : E f) → R(S(f , e)) ≡ (f , e)
    univalence' {X} {Y} f e = u (f , e)

    -- starting with a path, transporting along that path is the same as
    -- precomposing with the corresponding transport map.
    transportIsComp : {X X' Y : U} (p : X ≡ X') (g : X' → Y) →
       transport! (λ Z → Z → Y) p g ≡ (g ∘ tpMap p) 
    transportIsComp refl g = refl

    ηᴱ : {X Y : U} (e : X ≅ᴱ Y) → fst e ≡ fst (R (S e ))
    ηᴱ {_} {_} e = ap fst (u e) ⁻¹

    -- starting with an equivalence, precomposing is the same as transporting
    -- along the corresponding path.
    preCompIsTransport : {X X' Y : U} (f : X ≅ᴱ X') (g : X' → Y) →
       transport! (λ Z → Z → Y) (S f) g ≡ (g ∘ (fst f)) 
    preCompIsTransport fe g =  transportIsComp (S fe) g · η where
      f = fst fe
      e = snd fe
      η : g ∘ tpMap (S fe) ≡ (g ∘ f)
      η = ap (λ f → g ∘ f) ((ηᴱ fe) ⁻¹) 

    -- H is the proof that E is preserved by homotopies
    preCompIsE : {X X' Y : U} (f : X ≅ᴱ X') → E (λ (g : X' → Y) → g ∘ (fst f))
    preCompIsE f = H (transportIsE! (S f)) (preCompIsTransport f)

    preCompδ : {X Y : U} → (Δ X → Y) → X → Y
    preCompδ g = g ∘ δ

    preCompδIsE : {X Y : U} → E (preCompδ {X} {Y})
    preCompδIsE = preCompIsE (δ , d)


    -- we need that any E is mono. It's easier to simply show that it's a
    -- section. The inverse is transportⁱᵈ(⟪f⟫⁻¹). As usual, we start with
    -- a more general lemma on paths. This is actually a special case of
    -- [tp·], (see hott.agda) but laying it out here makes things cleaner.

    tpInv : {X : U} {C : X → U} {x y : X} (p : x ≡ y) (u : C x) →
      transport C (p ⁻¹) (transport C p u) ≡ u
    tpInv {_} {C} {x} {y} p u = tp· p (p ⁻¹) u · ap tp (path-syml p) where
      tp : x ≡ x → C x
      tp = λ p → transport C p u


    blah : {X Y : U} (P : (X → Y) → U) → ((p : X ≡ Y) → P(tpMap p)) 
         → (f : X → Y) → E f → P f
    blah {X} {Y} P φ f e = transport P c2 c1
     where
      p : X ≡ Y
      p = S(f , e)
      c1 : P(tpMap p)
      c1 = φ p
      c2 : tpMap p ≡ f
      c2 = ap fst (u (f , e))

    EisSect' : {X Y : U} (p : X ≡ Y) → Σ (λ g → (tpMap p) isSectionOf g)
    EisSect' refl = id , λ x → refl


    EisSect : {X Y : U} (f : X → Y) → E f → Σ (λ g → f isSectionOf g)
    EisSect {X} {Y} = blah (λ z → Σ (_isSectionOf_ z)) EisSect'

    blahblah : {X A : U} (f : X → A) → E f → (x y : X) → f x ≡ f y → x ≡ y
    blahblah {X} {A} f e x y p  = cancelx · (ap g p) · cancely where
      g' : Σ (_isSectionOf_ f)
      g' = EisSect f e
      g : A → X
      g = fst g'
      P : (x : X) → g (f x) ≡ x
      P = snd g'
      cancelx : x ≡ g (f x)
      cancelx = P x ⁻¹
      cancely : g (f y) ≡ y
      cancely = P y

    lemma₁ : {X : U} → (π₁ ∘ (δ {X})) ≡ (π₂ ∘ δ)
    lemma₁ {X} = refl

    lemma₂ : {X : U} → π₁ {X} ≡ π₂
    lemma₂ {X} = blahblah preCompδ preCompδIsE π₁ π₂ lemma₁

    funext : {X Y : U} (f₁ f₂ : X → Y) → (f₁ ∼ f₂) → f₁ ≡ f₂
    funext {X} {Y} f₁ f₂ h = f₁ =⟨ refl ⟩ π₁ ∘ f
                              =⟨ ap composef lemma₂ ⟩ π₂ ∘ f
                              =⟨ refl ⟩ f₂ ∎ where
           f : X → Δ Y
           f x = (f₁ x , f₂ x , h x)
           composef : (Δ Y → Y) → X → Y
           composef k = k ∘ f
open identitySection
