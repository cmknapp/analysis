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
X ≅ᴱ Y = Σ {X → Y} (λ f → E f)

-- fact 1a and 3
transportIsE : {X : U} {Y : X → U} {x y : X} (p : x ≡ y) →
             E (transport Y p)
transportIsE refl = i
transportIsE! : {X : U} {Y : X → U} {x y : X} (p : x ≡ y) →
             E (transport! Y p)
transportIsE! p = transportIsE (p ¹)

id2E : {X Y : U} (p : X ≡ Y) → X ≅ᴱ Y
id2E {X} {Y} p = (transport id p , transportIsE p)
--extracting the actual map. This is really just transport again.
tpMap : {X Y : U} (p : X ≡ Y) → X → Y
tpMap p = id2E p ₗ


-- ua says id2E has a section
postulate ua : {X Y : U} → X ≅ᴱ Y → X ≡ Y
postulate univalence : {X Y : U} → (ua {X} {Y}) ↯ (id2E {X} {Y})

syntax ua f = ⟪ f ⟫

{- We (may) need that this section also provides a retraction. The proof
is due to Martin Escardo, and goes like this: for any function
     f : {x y:X} x≡y → x≡y,
we have f(p) = f(refl) · p. Then if f is idempotent, f(p) = f(refl)·f(p).
In particular, we have that f(refl) = f(refl)², so f(refl) = refl. Then by
induction, f is (homotopic to) the identity.

taking f as E2id ∘ id2E, we get our retraction.

This should really be in a different file.
-}

module retr2eq {A : U} (f : {x y : A} → x ≡ y → x ≡ y) where
    fIsConcat : {x y : A} (p : x ≡ y) → f p ≡ (f refl · p)
    fIsConcat refl = refl-unitr! (f refl)

    idempotentIsId : (e : {x y : A} (p : x ≡ y) → f p ≡ f (f p)) →
                   {x y : A} (p : x ≡ y) → p ≡ f p
    idempotentIsId e refl =
                   refl =⟨ path-syml! fr ⟩        (fr · fr!)
                        =⟨ (e refl) ∗ᵣ fr!  ⟩     (ffr · fr!)
                        =⟨ fIsConcat fr ∗ᵣ fr! ⟩  ((fr · fr) · fr!)
                        =⟨ path-assoc fr fr fr! ⟩ (fr · (fr · fr!))
                        =⟨ fr ∗ₗ path-syml fr ⟩   (fr · refl)
                        =⟨ refl-unitr fr ⟩        fr ∎ where
          fr  = f refl
          fr! = (f refl) ¹
          ffr = f (f refl)
open retr2eq

{- TODO : This. (Martin's retraction→equiv proof)
    ua↯ : {X Y : U} → id2E {X} {Y} ↯ ua
    ua↯ {X} {Y} = idempotentIsId {U} (ua ∘ id2E) e where
      e : {X Y : U} (p : X ≡ Y)
      e p = ap ua (univalence ₗ (id2e p))
      -}

-- starting with a path, transporting along that path is the same as
-- precomposing with the corresponding transport map.
transportIsComp : {X X' Y : U} (p : X ≡ X') (g : X' → Y) →
   transport! (λ Z → Z → Y) p g ≡ (g ∘ tpMap p) 
transportIsComp refl g = refl

ηᴱ : {X Y : U} (e : X ≅ᴱ Y) → e ₗ ≡ id2E ⟪ e ⟫ ₗ
ηᴱ {_} {_} e = ap (_ₗ) (univalence e) ¹

-- starting with an equivalence, precomposing is the same as transporting
-- along the corresponding path.
preCompIsTransport : {X X' Y : U} (f : X ≅ᴱ X') (g : X' → Y) →
   transport! (λ Z → Z → Y) ⟪ f ⟫ g ≡ (g ∘ f ₗ) 
preCompIsTransport fe g =  transportIsComp ⟪ fe ⟫ g · η where
  f = fe ₗ
  e = fe ᵣ
  η : (g ∘ tpMap ⟪ fe ⟫) ≡ (g ∘ f)
  η = ap (λ f → g ∘ f) ((ηᴱ fe) ¹) 

-- H is the proof that E is preserved by homotopies
preCompIsE : {X X' Y : U} (f : X ≅ᴱ X') → E (λ (g : X' → Y) → g ∘ f ₗ)
preCompIsE f = H (transportIsE! ⟪ f ⟫) (preCompIsTransport f)

-- we need that any E is mono. It's easier to simply show that it's a
-- section. The inverse is transportⁱᵈ(⟪f⟫⁻¹). As usual, we start with
-- a more general lemma on paths. This is actually a special case of
-- [tp·], (see hott.agda) but laying it out here makes things cleaner.

tpInv : {X : U} {C : X → U} {x y : X} (p : x ≡ y) (u : C x) →
  transport C (p ¹) (transport C p u) ≡ u
tpInv {_} {C} {x} {y} p u = tp· p (p ¹) u · ap tp (path-syml p) where
  tp : x ≡ x → C x
  tp = λ p → transport C p u

EisSect : {X Y : U} (f : X → Y) → E f → Σ (λ g → f ↯ g)
EisSect {X} {Y} f e = ( f¹ , s) where
 f¹ : Y → X
 f¹ = transport id (⟪ f , e ⟫ ¹)
 s : (x : X) → f¹ (f x) ≡ x
 s x = ap {!!} (univalence {!!} ¹) · tpInv {U} {id} ⟪ f , e ⟫ x

