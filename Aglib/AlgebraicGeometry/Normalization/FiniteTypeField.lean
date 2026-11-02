/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Normalization.FunctionField
public import Aglib.RingTheory.Nagata.FiniteTypeField
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Finite normalization over a field

The actual affine chart Nagata proof is lowered from curve compactification.
The original generic normalization is finite, without any external Nagata input.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

/-- The original affine chart of a locally finite-type field scheme is Nagata. -/
theorem affineChart_nagata_of_finiteType_field
    (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (W : X.affineOpens) : IsNagataRing.{u, 0} Γ(X, W.1) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : IsNoetherianRing Γ(X, W.1) := IsLocallyNoetherian.component_noetherian W
  let φ : k →+* Γ(X, W.1) :=
    ((ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ W.1 (by simp)).hom
  let : Algebra k Γ(X, W.1) := φ.toAlgebra
  have hf : (f.appLE ⊤ W.1 (by simp)).hom.FiniteType :=
    f.finiteType_appLE (isAffineOpen_top _) W.2 _
  have hφ : φ.FiniteType := hf.comp
    (RingHom.FiniteType.of_surjective _
      (ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv.surjective)
  let : Algebra.FiniteType k Γ(X, W.1) := hφ
  refine ⟨inferInstance, ?_⟩
  intro P hP
  let : P.IsPrime := hP
  exact IsJapaneseRing.of_finiteType_field k (Γ(X, W.1) ⧸ P)

/-- The actual generic normalization of an integral field scheme is finite. -/
theorem genericNormalization_isFinite_of_finiteType_field
    (k : Type u) [Field k] (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] :
    IsFinite (X.fromSpecStalk (genericPoint X)).fromNormalization := by
  apply genericNormalization_isFinite X
  intro U _
  exact affineChart_nagata_of_finiteType_field k f U

end AlgebraicGeometry.Scheme
