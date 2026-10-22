/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.AffineCenter
public import Aglib.AlgebraicGeometry.IdealSheaf.LocallyClosed
public import Aglib.AlgebraicGeometry.IdealSheaf.Closed.SpecKernel

/-! # The actual centre ideal on an affine open -/

@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry
universe u

namespace AlgebraicGeometry.Scheme.Blowup

/-- On an affine open, the original ideal sheaf pulls back to the ideal of its
actual sections, not merely an ideal with the same vanishing set. -/
lemma comap_fromSpec_eq_affineCenter {X : Scheme.{u}} (I : X.IdealSheafData)
    (U : X.affineOpens) :
    I.comap U.2.fromSpec = affineCenter Γ(X, U) (I.ideal U) := by
  apply Scheme.IdealSheafData.ext_of_isAffine
  have ht : (⊤ : (Spec Γ(X, U)).Opens) ≤ U.2.fromSpec ⁻¹ᵁ U.1 := by
    rw [U.2.fromSpec_preimage_self]
  rw [Scheme.IdealSheafData.ideal_comap_eq_map_appLE I U.2.fromSpec U
    ⟨⊤, isAffineOpen_top _⟩ ht]
  change (I.ideal U).map (U.2.fromSpec.appLE U ⊤ ht).hom =
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal U)))).ker.ideal
      ⟨⊤, isAffineOpen_top (Spec (.of Γ(X, U)))⟩
  rw [Scheme.IdealSheafData.specMap_kernel_top, Ideal.mk_ker]
  have happ : U.2.fromSpec.appLE U ⊤ ht = (Scheme.ΓSpecIso Γ(X, U)).inv := by
    simp only [Scheme.Hom.appLE, U.2.fromSpec_app_self, Category.assoc,
      ← Functor.map_comp]
    simp
  rw [happ]
  exact Ideal.map_symm (I := I.ideal U)
    (Scheme.ΓSpecIso Γ(X, U)).commRingCatIsoToRingEquiv

end AlgebraicGeometry.Scheme.Blowup
