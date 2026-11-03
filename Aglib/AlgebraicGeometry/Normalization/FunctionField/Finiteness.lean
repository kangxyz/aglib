/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Normalization.FunctionField

/-! # Finiteness of the original generic normalization -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme

universe u

variable (W : Scheme.{u}) [IsIntegral W]

local notation "γ" => W.fromSpecStalk (genericPoint W)

/-- The actual coefficient ring used by relative normalization is a
fraction ring of the actual affine chart, through its original structural
map. The algebra-equivalence compatibility is the original germ equation. -/
theorem genericSection_isFractionRing
    (U : W.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    letI := ((γ).app U).hom.toAlgebra
    IsFractionRing Γ(W, U) Γ(Spec W.functionField, γ ⁻¹ᵁ U) := by
  let := ((γ).app U).hom.toAlgebra
  let : IsFractionRing Γ(W, U) W.functionField :=
    AlgebraicGeometry.functionField_isFractionRing_of_isAffineOpen W U hU
  let e : Γ(Spec W.functionField, γ ⁻¹ᵁ U) ≃ₐ[Γ(W, U)] W.functionField :=
    { (Scheme.functionFieldSectionsIso W U).commRingCatIsoToRingEquiv with
      commutes' r := by
        exact congr($(Scheme.fromSpecStalk_genericPoint_app_functionFieldSectionsIso W U) r) }
  exact IsFractionRing.of_algEquiv e.symm

/-- Finiteness of the literal integral closure gives finiteness of the
original affine normalization map, with its original coefficient action. -/
theorem genericNormalization_finite_app_of_finite
    (U : W.Opens) (hU : IsAffineOpen U)
    (hfinite : letI := ((γ).app U).hom.toAlgebra
      Module.Finite Γ(W, U)
        (integralClosure Γ(W, U) Γ(Spec W.functionField, γ ⁻¹ᵁ U))) :
    (((γ).fromNormalization).app U).hom.Finite := by
  let := ((γ).app U).hom.toAlgebra
  let : Module.Finite Γ(W, U)
      (integralClosure Γ(W, U) Γ(Spec W.functionField, γ ⁻¹ᵁ U)) := hfinite
  rw [Scheme.Hom.fromNormalization_app _ hU]
  exact (RingHom.Finite.of_surjective _
    (ConcreteCategory.bijective_of_isIso ((γ).normalizationObjIso hU).inv).2).comp
      (RingHom.finite_algebraMap.mpr
        (inferInstanceAs (Module.Finite Γ(W, U)
          (integralClosure Γ(W, U) Γ(Spec W.functionField, γ ⁻¹ᵁ U)))))

/-- A nonempty actual affine chart contributes a finite original
normalization map on sections. No replacement closure or scalar action is
introduced. -/
theorem genericNormalization_finite_app
    (U : W.Opens) (hU : IsAffineOpen U) [Nonempty U]
    (hB : IsNagataRing.{u, 0} Γ(W, U)) :
    (((γ).fromNormalization).app U).hom.Finite := by
  let := ((γ).app U).hom.toAlgebra
  let : IsFractionRing Γ(W, U) Γ(Spec W.functionField, γ ⁻¹ᵁ U) :=
    genericSection_isFractionRing W U hU
  let : Module.Finite Γ(W, U)
      (integralClosure Γ(W, U) Γ(Spec W.functionField, γ ⁻¹ᵁ U)) :=
    integralClosure.finite_of_isNagataRing Γ(W, U) hB
      Γ(Spec W.functionField, γ ⁻¹ᵁ U)
  exact genericNormalization_finite_app_of_finite W U hU inferInstance

/-- Finiteness of the original normalization can be checked on the
nonempty affine charts. Empty charts use their actual zero-ring section map. -/
theorem genericNormalization_isFinite_of_finite_app
    (hfinite : ∀ U : W.affineOpens, Nonempty U.1 →
      (((γ).fromNormalization).app U.1).hom.Finite) :
    IsFinite (γ).fromNormalization := by
  refine { toIsAffineHom := inferInstance, finite_app := ?_ }
  intro U hU
  by_cases hne : Nonempty U
  · let := hne
    exact hfinite ⟨U, hU⟩ hne
  · have hbot : U = ⊥ := by
      apply le_antisymm
      · intro x hx
        exact (hne ⟨⟨x, hx⟩⟩).elim
      · exact bot_le
    subst U
    let : Subsingleton Γ((γ).normalization, (γ).fromNormalization ⁻¹ᵁ ⊥) := by
      simpa only [Scheme.Hom.preimage_bot] using
        (inferInstanceAs (Subsingleton Γ((γ).normalization, ⊥)))
    exact RingHom.Finite.of_surjective _ (Function.surjective_to_subsingleton _)

end AlgebraicGeometry.Scheme
