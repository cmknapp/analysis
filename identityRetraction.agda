{-# OPTIONS --without-K #-}

open import hott

-- TODO: There's so much more work to do here...

{- Any section of the identity type also provides a retraction. The proof
is due to Martin Escardo, and goes like this: for any function
     f : {x y:X} x≡y → x≡y,
we have f(p) = f(refl) · p. Then if f is idempotent, f(p) = f(refl)·f(p).
In particular, we have that f(refl) = f(refl)², so f(refl) = refl. Then by
induction, f is (homotopic to) the identity.

taking f as S ∘ R, we get our retraction.
-}


module identityRetraction {i} {A : U i} (f : {x y : A} → x ≡ y → x ≡ y) where

fIsConcat : {x y : A} (p : x ≡ y) → f p ≡ ((f refl) · p)
fIsConcat refl = refl-unitr! (f refl)

idempotentIsId : (e : {x y : A} (p : x ≡ y) → f p ≡ f (f p)) →
               {x y : A} (p : x ≡ y) → p ≡ f p
idempotentIsId e refl =
               refl =⟨ path-syml! fr ⟩        (fr · fr!)
                    =⟨ (e refl) ·ᵣ fr!  ⟩     (ffr · fr!)
                    =⟨ fIsConcat fr ·ᵣ fr! ⟩  ((fr · fr) · fr!)
                    =⟨ path-assoc fr fr fr! ⟩ (fr · (fr · fr!))
                    =⟨ fr ·ₗ path-syml fr ⟩   (fr · refl)
                    =⟨ refl-unitr fr ⟩        fr ∎ where
      fr  = f refl
      fr! = (f refl) ⁻¹
      ffr = f (f refl)

--this should go elsewhere whenever I actually organize this stuff properly
idtoEquiv : ∀ {i} {X Y : U i} → X ≡ Y → X ≃ Y
idtoEquiv refl = (λ z → z) , (λ b → (b , refl) , {!!})


--  module UARetraction {i} {ua v
