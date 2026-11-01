/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.Basic
public import Aglib.RingTheory.Nagata.FiniteEtale

/-! # Finite generic-etale normalization over Nagata affine charts

Normality of the original base is unnecessary when its original affine
section rings are Nagata. Split and empty generic covers remain allowed.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization

variable (X : Scheme.{u}) [IsIntegral X]
  (C : Scheme.FiniteEtale (Spec X.functionField))

/-- The actual structural morphism of relative normalization is finite when
the original affine charts are Nagata. No normality of X is imposed. -/
theorem isFinite_of_isNagataRing
    (hNagata : ∀ U : X.affineOpens, Nonempty U.1 → IsNagataRing.{u, 0} Γ(X, U.1)) :
    IsFinite (C.obj.hom ≫ X.fromSpecStalk (genericPoint X)).fromNormalization := by
  refine { toIsAffineHom := inferInstance, finite_app := ?_ }
  intro U hU
  by_cases hne : Nonempty U
  · let := hne
    have hN := hNagata ⟨U, hU⟩ hne
    let : IsNoetherianRing Γ(X, U) := hN.isNoetherianRing
    let : IsFractionRing Γ(X, U) X.functionField :=
      functionField_isFractionRing_of_isAffineOpen X U hU
    let : Module.Finite Γ(X, U)
        (integralClosure Γ(X, U)
          Γ(C.obj.left, (C.obj.hom ≫ X.fromSpecStalk (genericPoint X)) ⁻¹ᵁ U)) :=
      _root_.integralClosure.finite_of_etale_of_isJapaneseRing Γ(X, U) X.functionField
        Γ(C.obj.left, (C.obj.hom ≫ X.fromSpecStalk (genericPoint X)) ⁻¹ᵁ U)
        hN.isJapaneseRing
    rw [Scheme.Hom.fromNormalization_app _ hU]
    exact (RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso
        ((C.obj.hom ≫ X.fromSpecStalk (genericPoint X)).normalizationObjIso hU).inv).2).comp
          (RingHom.finite_algebraMap.mpr inferInstance)
  · have hbot : U = ⊥ := by
      apply bot_unique
      intro x hx
      exact (hne ⟨⟨x, hx⟩⟩).elim
    subst U
    let : Subsingleton
        Γ((C.obj.hom ≫ X.fromSpecStalk (genericPoint X)).normalization,
          (C.obj.hom ≫ X.fromSpecStalk (genericPoint X)).fromNormalization ⁻¹ᵁ ⊥) := by
      rw [Scheme.Hom.preimage_bot]
      infer_instance
    exact RingHom.Finite.of_surjective _ (Function.surjective_to_subsingleton _)

end AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization
