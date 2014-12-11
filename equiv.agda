{-# OPTIONS --without-K #-}
{-# OPTIONS --type-in-type #-}

module equiv {A B : Set} {C : A → Set} where

open import hott

-- We use "invertible" for a function with a (homotopy) inverse, rather
-- than the (in my mind) misleading title of "quasiequivalence"
invertible : (A → B) → U
invertible f = Σ (λ g → f isSectionOf g × g isSectionOf f)

-- bi-invertibility; we use a quick name, since we won't ever use it again.
--To keep left from right,
--"f is a section and a retraction" sounds better than
--"f is a retraction and a section"

biinv : (A → B) → U
biinv f = (Σ (λ g → f isSectionOf g)) × (Σ (λ h → h isSectionOf f))

-- binvertibility and quasiequivalence are clearly (logically)
-- equivalent:

-- easy direction
invertible-is-biinv : {f : A → B} → invertible f → biinv f
invertible-is-biinv (g , (p , q)) = (g , p) , (g , q)

-- harder direction: we take gfh as the inverse, and then we need to
-- play with paths for a bit.
biinv-is-invertible : {f : A → B} → biinv f → invertible f
biinv-is-invertible {f} ((g , p) , (h , q)) = (g ∘ f ∘ h ,
                                          (associateₗ , associateᵣ)) where
  associateₗ : f isSectionOf (g ∘ f ∘ h)
  associateₗ x = g (f (h (f x))) =⟨ ap g (q (f x)) ⟩ g (f x)
                                 =⟨ p x ⟩ x ∎
  associateᵣ : g ∘ f ∘ h isSectionOf f
  associateᵣ x = ap f (p (h x)) · q x

-- "half-adjoint" equivalence
hae : (f : A → B) (g : B → A) → (g ∘ f ∼ id) → (f ∘ g ∼ id ) → U
hae f g η ε = (ap f ∘ η) ∼ (ε ∘ f)

-- A "predicate"
ishae : (A → B) → U
ishae f = Σ λ g →
            Σ λ η → 
              Σ λ ε →
                hae f g η ε

-- half-adjoint obviously implies invertible
hae-is-inv : (f : A → B) → ishae f → invertible f
hae-is-inv f (g , η , ε , τ) = (g , η , ε)

{-The other direction is more work. We need to rebuild ε, and then
 -built τ from that. This requires some path-magic.
 
 -intuitively, we're trying to conjugate fηg by ε, but this doesn't
 -give us the right type, so on the left we use εfg⁻¹. This gives us
 -ε' : fg ∼ fgfg ∼ fg ∼ id. Naturality and some clever whiskering lets
 -us fill in the resulting opetope.
 -}
 {-
inv-is-hae : (f : A → B) → invertible f → ishae f
inv-is-hae f (g , η , ε) = (g , η , ε' , τ) where
            --just renaming to make life easier:
            fgfη   : (x : A) → (f (g (f (g (f x))))) ≡ (f (g (f x)))
            fgfη x = (ap f (ap (g ∘ f) (η x)))
            fη     : (x : A) → (f (g (f x))) ≡ (f x)
            fη   x = ap f (η x)
            εf     : (x : A) → f (g (f x)) ≡ f x
            εf   x = ε (f x)
            εfg    : (x : B) → f (g (f (g x))) ≡ f (g x)
            εfg  x = ε (f ( g x))
            fηg    : (x : B) → f (g (f (g x))) ≡ f (g x)
            fηg  x = ap f (η (g x))
            ε' : f ∘ g ∼ id
            ε' x =  (εfg x) ¹ · (fηg x) · (ε x)
            commute : (x : A) → (fηg (f x)) ≡ fgfη x
            commute x = ap (ap f) ((homotopy-switch (g ∘ f) η x) ¹)
            naturality : (x : A) →
              (εfg (f x) · (fη x)) ≡ (fgfη x · εf x)
            naturality x = homotopy-natural εf (η x)
            τ : ap f ∘ η ∼ ε' ∘ f
            τ x = {!                     ap f (η x)  =⟨ ? ⟩
                                 refl · ap f (η x)  =⟨ ? ⟩
       (ε (f (g x)) ¹ · ε (f (g x)))  · ap f (η x)  =⟨ ? ⟩
        ε (f (g x)) ¹ · (ε (f (g x))  · ap f (η x)  =⟨ ? ⟩
        ε (f (g x)) ¹ · (ap f (ap (g ∘ f) (η x)))  · ε (f x) =⟨ ? ⟩

!}

-}

-- Grad lemma: invertible is (logically) equivalent to equivalence.
inv-is-equiv : (f : A → B) → invertible f → isEquiv f
inv-is-equiv f (g , η , ε) b = ( gb , paths) where
             gb    = (g b , ε b)
             g-_η : {x : A} (p : f x ≡ b) →
               g b ≡ x
             g- p η = ap g p ⁻¹ · η _
             lift : (x : A) (p : f x ≡ b) →
                ε b ≡ p [ (λ v → f v ≡ b) ↓ (g- p η) ]
             lift x p = {!(tp∘ (g- p η) ε b) · ?!}
             paths : (x : fiber f b) → (gb ≡ x)
             paths (x , p) = pair= (ap g p ⁻¹ · η x) (lift x p)
{-
equiv-is-inv : (f : A → B) → isEquiv f → invertible f
equiv-is-inv f e = (f ! , η , ε) where
             η = ?
             ε = ?
             -}

