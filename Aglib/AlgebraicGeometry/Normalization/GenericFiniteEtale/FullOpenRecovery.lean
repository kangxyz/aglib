/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.OpenEtaleLocus

/-! # Original normalization over a full cover open -/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery

universe u

/-- If the original cover open covers the whole target, the unchanged
normalization is etale everywhere. No Noetherian hypothesis is needed. -/
theorem fromNormalization_etale_of_surjective_open
    {X U E : Scheme.{u}} [IsIntegral X] [Nonempty U]
    [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)]
    (j : U ⟶ X) [IsOpenImmersion j] (p : E ⟶ U) [IsFinite p] [Etale p]
    (hj : Function.Surjective j) : Etale (genericMap j p).fromNormalization := by
  apply Hom.etale_of_forall_etaleAt
  intro x
  exact fromNormalization_etaleAt_of_image_mem j p x (hj _)

end AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery
