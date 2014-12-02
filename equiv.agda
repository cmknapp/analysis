{-# OPTIONS --without-K #-}
{-# OPTIONS --type-in-type #-}

module equiv {A B : Set} {C : A → Set} where

open import hott

--"quasi" equivalence.
qequiv : (A → B) → U
qequiv f = Σ (λ g → f ↯ g × g ↯ f)

--bi-invertibility.
--To keep left from right,
--"f is a section and a retraction" sounds better than
--"f is a retraction and a section)

biinv : (A → B) → U
biinv f = (Σ (λ g → f ↯ g)) × (Σ (λ h → h ↯ f))

--binvertibility and quasiequivalence are clearly (logically)
--equivalent:

--easy direction
qequiv-is-biinv : {f : A → B} → qequiv f → biinv f
qequiv-is-biinv (g , (p , q)) = (g , p) , (g , q)

--harder direction: we take gfh as the inverse, and then we need to
--play with paths for a bit.
biinv-is-qequiv : {f : A → B} → biinv f → qequiv f
biinv-is-qequiv {f} ((g , p) , (h , q)) = (g ∘ f ∘ h ,
                                          (associateₗ , associateᵣ)) where
  associateₗ : f ↯ (g ∘ f ∘ h)
  associateₗ x = g (f (h (f x))) =⟨ ap g (q (f x)) ⟩ g (f x)
                                 =⟨ p x ⟩ x ∎
  associateᵣ : g ∘ f ∘ h ↯ f
  associateᵣ x = ap f (p (h x)) · q x

--half-adjoint equivalence
hae : (f : A → B) (g : B → A) → (g ∘ f ∼ id) → (f ∘ g ∼ id ) → U
hae f g η ε = (ap f ∘ η) ∼ (ε ∘ f)

--A "predicate"
ishae : (A → B) → U
ishae f = Σ λ g →
            Σ λ η → 
              Σ λ ε →
                hae f g η ε

--half-adjoint obviously implies quasi-invertible
hae-is-qequiv : (f : A → B) → ishae f → qequiv f
hae-is-qequiv f (g , η , ε , τ) = (g , η , ε)

{-The other direction is more work. We need to rebuild ε, and then
 -built τ from that. This requires some path-magic.
 
 -intuitively, we're trying to conjugate fηg by ε, but this doesn't
 -give us the right type, so on the left we use εfg⁻¹. This gives us
 -ε' : fg ∼ fgfg ∼ fg ∼ id. Naturality and some clever whiskering lets
 -us fill in the resulting opetope.
 -}
qequiv-is-hae : (f : A → B) → qequiv f → ishae f
qequiv-is-hae f (g , η , ε) = (g , η , ε' , τ) where
            ε' : f ∘ g ∼ id
            ε' x =  ε (f (g x)) ¹ · ap f (η (g x)) · (ε x)
            commute : (x : A) → (ap f (η (g (f x)))) ≡ (ap f (ap (g ∘ f) (η x)))
            commute x = ap (ap f) {!!}
            naturality : (x : A) →
              (ap (f ∘ g ∘ f) (η x) · ε (f x)) ≡
              (ε ((f ∘ g ∘ f) x) · (ap f (η x)))
            naturality = {!!}
            τ : ap f ∘ η ∼ ε' ∘ f
            τ x = {!!}

