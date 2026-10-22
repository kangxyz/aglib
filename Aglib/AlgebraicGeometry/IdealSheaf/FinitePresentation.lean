/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.IdealSheaf.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-!
# Finite presentation of closed immersions

A closed immersion is locally of finite presentation exactly when its native
kernel ideal is finitely generated on every affine open. In particular, this
characterizes finite presentation of the canonical immersion of an ideal-sheaf
datum. Quasi-compactness and quasi-separatedness are automatic for closed
immersions; no Noetherian hypothesis is imposed.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

/-- A closed immersion is locally of finite presentation exactly when its
actual kernel ideal is finitely generated on every affine open. -/
theorem locallyOfFinitePresentation_iff_ker_affineLocallyFG
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f] :
    LocallyOfFinitePresentation f ↔ f.ker.AffineLocallyFG := by
  constructor
  · intro hf
    let := hf
    intro U
    rw [f.ker_apply U]
    have hfp : (f.app U).hom.FinitePresentation := by
      simpa only [Scheme.Hom.app_eq_appLE] using
        f.finitePresentation_appLE U.2 (U.2.preimage f) le_rfl
    let A := Γ(Y, U)
    let B := Γ(X, f ⁻¹ᵁ U)
    let φ : A →+* B := (f.app U).hom
    let : Algebra A B := φ.toAlgebra
    have : Algebra.FinitePresentation A A := Algebra.FinitePresentation.self A
    have : Algebra.FinitePresentation A B := hfp
    let ψ : A →ₐ[A] B := { φ with commutes' := fun _ ↦ rfl }
    exact Algebra.FinitePresentation.ker_fG_of_surjective ψ (f.app_surjective U U.2)
  · intro h
    apply IsZariskiLocalAtTarget.of_iSup_eq_top (P := @LocallyOfFinitePresentation)
      (fun U : Y.affineOpens ↦ U.1) (iSup_affineOpens_eq_top Y)
    intro U
    have : IsAffine U.1.toScheme := U.2
    have : IsAffine (f ⁻¹ᵁ U.1).toScheme := U.2.preimage f
    rw [HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFinitePresentation),
      morphismRestrict_appTop, CommRingCat.hom_comp,
      RingHom.finitePresentation_respectsIso.cancel_right_isIso]
    change (f.app (U.1.ι ''ᵁ ⊤)).hom.FinitePresentation
    rw [Scheme.Opens.ι_image_top]
    apply RingHom.FinitePresentation.of_surjective (f.app U).hom (f.app_surjective U U.2)
    rw [← f.ker_apply U]
    exact h U

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- The canonical closed immersion of an ideal-sheaf datum is locally of
finite presentation exactly when the datum is affine-locally finitely generated. -/
theorem locallyOfFinitePresentation_subschemeι_iff
    {X : Scheme.{u}} (I : X.IdealSheafData) :
    LocallyOfFinitePresentation I.subschemeι ↔ I.AffineLocallyFG := by
  rw [Scheme.Hom.locallyOfFinitePresentation_iff_ker_affineLocallyFG,
    I.ker_subschemeι]

end AlgebraicGeometry.Scheme.IdealSheafData
