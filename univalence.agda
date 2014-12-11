{-# OPTIONS --without-K #-}
{-# OPTIONS --type-in-type #-}

open import hott
open import UA_implies_FE

module univalence where

{- This needs to go elsewhere! Proof that Σ (y → x ≡ y) is contractible -}
paths : {X : U} (x : X) → U
paths x = Σ λ y → y ≡ x

contractiblePaths : {X : U} (x : X) → isContr (paths x)
contractiblePaths {X} x = ((x , refl) , collapse) where
  pathspace = λ y → y ≡ x
  lemma : {y : X} → {p : y ≡ x} → p ≡ refl [ pathspace ↓ p ]
  lemma {.x} {refl} = refl
  collapse : (y : paths x) → (x , refl) ≡ y
  collapse (y , p) = (pair= p (lemma {y} {p})) ⁻¹

i : {X : U} → isEquiv (id {X})
i = contractiblePaths

--postulate since this is only for testing
postulate gradlemma :
d : {X : U} → isEquiv (δ {X})
d {X} x = {!!}
