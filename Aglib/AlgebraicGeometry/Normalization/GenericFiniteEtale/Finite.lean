/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.Basic
public import Aglib.AlgebraicGeometry.Properties.Normal.Affine

/-!
# Finiteness of generic finite-etale relative normalization

Under integral, locally Noetherian base and integrally closed actual stalks, affine
integral closures and then the actual normalization structural morphism are finite.
The generic-fibre recovery in Basic has no normality or local Noetherianity premise.

## Extraction basis

Existing declarations from
`R5Lab/AlgebraicGeometry/FiniteEtale/Normalization/GenericNormalization.lean`, source revision
`79307ff88f07d34fd5c3edb859f799c55e38f290`, SHA-256
`d4e8c371f13557079b4051530de44bc742dcd1d9c6850e9a5788477b95c26601`.
The source statements, binder universes, hypotheses and chosen maps are retained.
Direct Mathlib carriers/maps replace the recorded source wrappers; source-token correspondence
and those definitional substitutions are separate from native Lean validation.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open scoped TensorProduct nonZeroDivisors

namespace AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization

universe u

variable (X : Scheme.{u}) [IsIntegral X]
  (C : Scheme.FiniteEtale (Spec X.functionField))
  [IsLocallyNoetherian X] [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)]

/-- The actual integral-closure sections over each nonempty affine chart
are finite. Normality and local Noetherianity enter HERE, separately from
generic-fibre recovery. Separability comes from the original finite-etale C. -/
theorem finite_app (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    (((C.obj.hom ≫ (X.fromSpecStalk (genericPoint X))).fromNormalization).app U).hom.Finite := by
  letI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  letI : IsIntegrallyClosed Γ(X, U) := isIntegrallyClosed_sections_of_isAffineOpen X U hU
  letI : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  haveI : Module.Finite Γ(X, U) (integralClosure Γ(X, U) (Γ(C.obj.left, (C.obj.hom ≫
      (X.fromSpecStalk (genericPoint X))) ⁻¹ᵁ U))) :=
    _root_.integralClosure.finite_of_etale Γ(X, U) X.functionField (Γ(C.obj.left, (C.obj.hom ≫
        (X.fromSpecStalk (genericPoint X))) ⁻¹ᵁ U))
  rw [Scheme.Hom.fromNormalization_app _ hU]
  exact (RingHom.Finite.of_surjective _
    (ConcreteCategory.bijective_of_isIso ((C.obj.hom ≫ (X.fromSpecStalk (genericPoint
        X))).normalizationObjIso hU).inv).2).comp
      (inferInstanceAs (Module.Finite Γ(X, U)
        (integralClosure Γ(X, U) (Γ(C.obj.left, (C.obj.hom ≫ (X.fromSpecStalk (genericPoint X))) ⁻¹ᵁ
            U)))))

/-- The canonical global normalization is FINITE over a normal integral
locally Noetherian base, for the original finite-etale generic cover.
This constructs finiteness from actual affine closures; no excellence,
characteristic-zero or supplied global finite-model premise is used. -/
instance instIsFinite : IsFinite ((C.obj.hom ≫ (X.fromSpecStalk (genericPoint
    X))).fromNormalization) := by
  refine { toIsAffineHom := inferInstance, finite_app := ?_ }
  intro U hU
  by_cases hne : Nonempty U
  · letI := hne
    exact finite_app X C U hU
  · have hbot : U = ⊥ := by
      apply le_antisymm
      · intro x hx
        exact (hne ⟨⟨x, hx⟩⟩).elim
      · exact bot_le
    subst U
    haveI : Subsingleton Γ((C.obj.hom ≫ (X.fromSpecStalk (genericPoint X))).normalization,
        (C.obj.hom ≫ (X.fromSpecStalk (genericPoint X))).fromNormalization ⁻¹ᵁ ⊥) := by
      simpa only [Scheme.Hom.preimage_bot] using
        (inferInstanceAs (Subsingleton Γ((C.obj.hom ≫ (X.fromSpecStalk (genericPoint
            X))).normalization, ⊥)))
    exact RingHom.Finite.of_surjective _ (Function.surjective_to_subsingleton _)

end AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization
