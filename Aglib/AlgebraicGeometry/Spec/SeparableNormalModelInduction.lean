/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Nagata.FiniteFaithfulRank
public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.SeparableBaseSquare
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

/-! # The literal separable normal model satisfies the induction inputs

Trace-dual finiteness is obtained for the actual integral closure in the
specified finite separable field. The original fraction-field tower proves
faithfulness. The general finite-faithful theorem then supplies Nagata,
lying over, and coefficient rank control for exactly this model. Neither
finite normalization nor surjectivity is an additional premise.
-/

@[expose] public noncomputable section

namespace AlgebraicGeometry.Scheme.SeparableBaseSquare

universe u

/-- The same literal normal model is finite, normal, Nagata, of bounded
rank, and surjective over the original base. Its original fraction field
and structural map are retained, with no change of algebra dictionary. -/
theorem normal_finite_model_induction
    (R k F : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Field k] [Field F] [Algebra R k] [IsFractionRing R k]
    [Algebra k F] [Algebra R F] [IsScalarTower R k F]
    [Module.Finite k F] [Algebra.IsSeparable k F]
    (hR : IsNagataRing.{u, 0} R) :
    Module.Finite R (integralClosure R F) ∧
      IsNoetherianRing (integralClosure R F) ∧
      IsIntegrallyClosed (integralClosure R F) ∧
      IsFractionRing (integralClosure R F) F ∧
      IsNagataRing.{u, 0} (integralClosure R F) ∧
      ringKrullDim (integralClosure R F) ≤ ringKrullDim R ∧
      IsFinite (Spec.algebraMap R (integralClosure R F)) ∧
      Surjective (Spec.algebraMap R (integralClosure R F)) := by
  let : IsNoetherianRing R := hR.isNoetherianRing
  obtain ⟨hfin, hnoeth, hnormal, hfrac, hspec⟩ := normal_finite_model R k F
  let : Module.Finite R (integralClosure R F) := hfin
  let : FaithfulSMul R (integralClosure R F) :=
    (faithfulSMul_iff_algebraMap_injective R (integralClosure R F)).mpr
      (closure_algebraMap_injective R k F)
  obtain ⟨hnagata, hsurj, hrank⟩ :=
    hR.finite_faithful_rank (S := integralClosure R F)
  refine ⟨hfin, hnoeth, hnormal, hfrac, hnagata, hrank, hspec, ?_⟩
  exact ⟨hsurj⟩

end AlgebraicGeometry.Scheme.SeparableBaseSquare
