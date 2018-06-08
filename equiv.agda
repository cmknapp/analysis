{-# OPTIONS --without-K #-}

--TODO: we force a and b to have the same U-level for now...
--I'm fumbling on a universe issue I don't want to deal with.

open import hott
module equiv {i k} {A : U i} {B : U i} {C : A → U k} where
--module equiv {i j k} {A : U i} {B : U j} {C : A → U k} where


-- We use "invertible" for a function with a (homotopy) inverse, rather
-- than the (in my mind) misleading title of "quasiequivalence"
invertible : (A → B) → U i --(lmax i j)
invertible f = Σ (λ g → f isSectionOf g × g isSectionOf f)

-- bi-invertibility; we use a quick name, since we won't ever use it again.
--To keep left from right,
--"f is a section and a retraction" sounds better than
--"f is a retraction and a section"

biinv : (A → B) → U i --(lmax i j)
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
hae : (f : A → B) (g : B → A) → (g ∘ f ∼ id) → (f ∘ g ∼ id ) →
 U i -- U (lmax i j)
hae f g η ε = (ap f ∘ η) ∼ (ε ∘ f)

-- A "predicate"
ishae : (A → B) → U i --(lmax i j)
ishae f = Σ λ g →
            Σ λ η → 
              Σ λ ε →
                hae f g η ε

-- half-adjoint obviously implies invertible
hae-is-inv : (f : A → B) → ishae f → invertible f
hae-is-inv f (g , η , ε , τ) = (g , η , ε)

{- Grad lemma: invertible is (logically) equivalent to equivalence.
   This whole proof should go in its own module, with some of this
   stuff hidden.
-}

    {- Eqv => Inv. The idea is to use the contractibility of fibers
       to extract the paths we need -}
--Fibers of f(x) contract to (x,refl). There's a more general version
--we should use.
contr-lemma : (f : A → B) (e : isEquiv f) (x : A) (y : fiber f (f x)) →
            y ≡ (x , refl)
contr-lemma f e x y = contr-isProp (e (f x)) y (x , refl)

-- f ∘ f! ∘ f ∼ f. So, going back and forth and back gives us something
-- in the fiber. Using contr-lemma, we can remove the f form the front
-- to get a homotopy f! ∘ f ∼ id
zigzag-lemma : (f : A → B) → (e : isEquiv f) → (f ∘ (f !) {e} ∘ f) ∼ f
zigzag-lemma f e x = snd (center (e (f x)))

-- f! ∘ f ∼ id comes from the above. For the other direction, we
-- know that f!(y) lies in the fiber of y.
equiv-is-inv : (f : A → B) → isEquiv f → invertible f
equiv-is-inv f e = ((f !) {e} , η , ε) where
        contract = contr-lemma f e
        f! = (f !) {e}
        f!f = f! ∘ f
        η = λ x → ap fst (contract x (f!f x , zigzag-lemma f e x))
        ε = λ y → snd (center (e y))

--We show that fiber f y is a proposition. We have an obvious inhabitant
--as (g b, ε b)
inv-is-equiv : (f : A → B) → invertible f → isEquiv f
inv-is-equiv f (g , η , ε) b = inhProp-isContr (g b , ε b) prop where
        r : (x y : fiber f b) → (fst x ≡ fst y)
        r (x , p) (y , q) = (η x ⁻¹) · (ap g p) · (ap g q ⁻¹) · (η y)
        prop : isProp (fiber f b)
        prop x y = pair= (r x y) ({!!})
