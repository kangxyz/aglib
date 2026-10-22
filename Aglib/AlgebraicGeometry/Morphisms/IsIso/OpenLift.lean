/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.IsIso.OpenHomExt

/-!
# Lifting an open on which a morphism is an isomorphism

A lift of the original open inclusion is the actual inverse restricted map
followed by the preimage-open inclusion. In particular that lift is open.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The original open has only one lift through an isomorphic restriction. -/
theorem eq_inv_restrict_comp {A B : Scheme.{u}}
    (f : A ⟶ B) (U : B.Opens) [IsIso (f ∣_ U)]
    (s : U.toScheme ⟶ A) (hs : s ≫ f = U.ι) :
    s = inv (f ∣_ U) ≫ (f ⁻¹ᵁ U).ι := by
  apply f.ext_of_isIso_restriction U (𝟙 _) s _
  · simpa only [Category.id_comp] using hs
  · rw [Category.assoc, ← AlgebraicGeometry.morphismRestrict_ι f U, IsIso.inv_hom_id_assoc]
    simp

/-- A lift of the protected open inclusion is an open immersion. No global
monomorphism or properness of the structure map is needed. -/
theorem isOpenImmersion_of_isIso_restriction {A B : Scheme.{u}}
    (f : A ⟶ B) (U : B.Opens) [IsIso (f ∣_ U)]
    (s : U.toScheme ⟶ A) (hs : s ≫ f = U.ι) : IsOpenImmersion s := by
  rw [f.eq_inv_restrict_comp U s hs]
  infer_instance

end AlgebraicGeometry.Scheme.Hom
