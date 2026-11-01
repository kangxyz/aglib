/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Spec.IntegralPointLift
public import Aglib.RingTheory.IntegralClosure.ChangeBaseMap
public import Aglib.RingTheory.IntegralClosure.FiniteEtale
public import Aglib.RingTheory.Kummer.RegularParameter
public import Aglib.RingTheory.RegularLocalRing.Normal

/-! # The original normalization point on the normalized root cover

The original tensor inclusion induces an injective finite map between the
literal integral closures. Lying over lifts the specified original point,
and integrality of the literal local root algebra identifies its root-base
image with the actual closed point. No normalization/base-change isomorphism
or residue-field embedding is assumed.
-/

@[expose] public noncomputable section

open scoped TensorProduct
open Algebra.Kummer

namespace AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.RootCancellation

universe u

/-- Lift a specified closed-base point of the original normalization to the
literal normalized root cover, retaining its original closure-map image and
its exact closed root-base point. All normality and finiteness are derived. -/
theorem exists_normalizedRootPoint
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (f : R) (hf : f ∈ IsLocalRing.maximalIdeal R)
    [IsRegularLocalRing (R ⧸ Ideal.span {f})]
    (N : ℕ) (hN : 0 < N) (hreg : IsSMulRegular R f)
    (K F L : Type u) [Field K] [Field F] [Field L]
    [Algebra K F] [Algebra K L] [Algebra.Etale K L]
    [Algebra R K] [Algebra R F] [Algebra R L]
    [IsScalarTower R K F] [IsScalarTower R K L]
    [Algebra (RootAlgebra N f) F] [IsFractionRing (RootAlgebra N f) F]
    [IsScalarTower R (RootAlgebra N f) F] :
    letI : IsLocalRing (RootAlgebra N f) := parameterRoot_isLocalRing R f hf N hN
    ∀ (x : Spec (.of (integralClosure R L))),
    Spec.algebraMap R (integralClosure R L) x = IsLocalRing.closedPoint R →
    ∃ y : Spec (.of (integralClosure (RootAlgebra N f) (F ⊗[K] L))),
      Spec.map (CommRingCat.ofHom
        (integralClosure.tensorChangeBaseMap R (RootAlgebra N f) K F L).toRingHom) y = x ∧
      Spec.algebraMap (RootAlgebra N f) (integralClosure (RootAlgebra N f) (F ⊗[K] L)) y =
        IsLocalRing.closedPoint (RootAlgebra N f) := by
  let T := RootAlgebra N f
  let A := F ⊗[K] L
  let C := integralClosure R L
  let B := integralClosure T A
  let : IsLocalRing T := parameterRoot_isLocalRing R f hf N hN
  let : Module.Finite R T := root_finite N hN f
  let : IsNoetherianRing T := IsNoetherianRing.of_finite R T
  let : IsRegularLocalRing T := parameterRoot_isRegularLocalRing R f hf N hN hreg
  let : IsDomain T := IsRegularLocalRing.isDomain_of_regularLocal T
  let : IsIntegrallyClosed T := IsRegularLocalRing.isIntegrallyClosed_of_regularLocal T
  let : Module.Finite T B := integralClosure.finite_of_etale T F A
  let i : L →ₐ[R] A := (Algebra.TensorProduct.includeRight : L →ₐ[K] A).restrictScalars R
  let : Algebra C B := integralClosure.changeBaseMapAlgebra R T L A i
  let : IsScalarTower R C B := integralClosure.changeBaseMap_isScalarTower R T L A i
  let : Module.Finite C B := integralClosure.changeBaseMap_finite R T L A i
  have hint : (integralClosure.tensorChangeBaseMap R T K F L).toRingHom.IsIntegral := by
    change (algebraMap C B).IsIntegral
    exact algebraMap_isIntegral_iff.mpr inferInstance
  intro x hx
  exact Spec.exists_point_lift_over_closedPoint R T C B
    (integralClosure.tensorChangeBaseMap R T K F L) hint
    (integralClosure.tensorChangeBaseMap_injective R T K F L) x hx

end AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.RootCancellation
