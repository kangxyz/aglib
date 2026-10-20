/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

import Aglib.AlgebraicGeometry.Normalization.InertiaTorsor.Basic

/-!
The public constructors use native finite-etale covers and torsor actions.
Transport is tested on an arbitrary scheme over the base, and the normalization
action uses the actual H1 input and supplied Hopf coefficient structure.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.MonObj
open Algebra.FiniteEtale.TorsorExtension
open AlgebraicGeometry.Scheme.FiniteEtale.InertiaTorsor
open GroupCohomology.ContinuousH1

attribute [local instance] Over.cartesianMonoidalCategory Over.braidedCategory

universe u v

section GeneralTestObject

variable (R B H : Type u) [CommRing R] [CommRing B] [Algebra R B]
  [CommRing H] [HopfAlgebra R H] [Coalgebra.IsCocomm R H]
  (T : AlgebraicTorsorData R B H (Bialgebra.counitAlgHom R H) (Bialgebra.comulAlgHom R H))

example (X : Over (Spec (.of R))) (x y : X ⟶ affine R B) :
    ∃! a : X ⟶ (coefficientGroup R H).X, (schemeTorsorAction R B H T).act a x = y :=
  (schemeTorsorAction R B H T).transport x y (toUnit_unique _ _)

example [Module.Finite R B] [Algebra.Etale R B] :
    (cover R B).obj.left = Spec (.of B) := rfl

end GeneralTestObject

section ActualNormalization

variable (R K Ω A H : Type u) (Lambda : Type v)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω]
  [IsGalois K Ω] [IsAlgClosed Ω]
  [CommRing A] [Algebra K A] [Algebra R A] [IsScalarTower R K A]
  [Algebra.Etale K A] [CommRing H] [HopfAlgebra R H] [Coalgebra.IsCocomm R H]
  [Module.Finite R H] [Algebra.Etale R H]
  [AddCommGroup Lambda] [TopologicalSpace Lambda] [IsTopologicalAddGroup Lambda]
  [DistribMulAction (Ω ≃ₐ[K] Ω) Lambda] [ContinuousSMul (Ω ≃ₐ[K] Ω) Lambda]
  (tau : OriginalTorsorData R K A H
    (Bialgebra.counitAlgHom R H) (Bialgebra.comulAlgHom R H))
  (coords : Algebra.FiniteEtale.TorsorCoordinates.CoefficientPointCoordinates R K Ω H Lambda
    (Bialgebra.counitAlgHom R H) (Bialgebra.comulAlgHom R H))
  (f : A →ₐ[K] Ω) (Q : Ideal (integralClosure R Ω)) [Q.IsPrime]
  [Q.LiesOver (IsLocalRing.maximalIdeal R)]
  (hvan : Algebra.FiniteEtale.TorsorCoordinates.inertiaClass
    R K Ω A H Lambda tau coords f Q = 0)

example : CategoryTheory.TorsorAction (coefficientGroup R H)
    (toUnit (normalizationCover R K Ω A H Lambda tau coords f Q hvan).obj) :=
  normalizationSchemeAction R K Ω A H Lambda tau coords f Q hvan

example : Over.mk (structureMap R Ω) ⟶
    (normalizationCover R K Ω A H Lambda tau coords f Q hvan).obj :=
  normalizationGenericPoint R K Ω A H Lambda tau coords f Q hvan

example (q : H1 (Ω ≃ₐ[K] Ω) Lambda)
    (hclass : q =
      Algebra.FiniteEtale.TorsorCoordinates.genericClass R K Ω A H Lambda tau coords f)
    (hzero :
      letI := restrictedAction Lambda
        (Algebra.FiniteEtale.TorsorCocycle.subgroupInclusion K Ω (Q.inertia (Ω ≃ₐ[K] Ω)))
      letI := restrictedAction_continuous Lambda
        (Algebra.FiniteEtale.TorsorCocycle.subgroupInclusion K Ω (Q.inertia (Ω ≃ₐ[K] Ω)))
      restriction Lambda
        (Algebra.FiniteEtale.TorsorCocycle.subgroupInclusion K Ω (Q.inertia (Ω ≃ₐ[K] Ω))) q = 0) :
    CategoryTheory.TorsorAction (coefficientGroup R H)
      (toUnit (affine R (integralClosure R A))) :=
  schemeTorsorAction R (integralClosure R A) H
    (Algebra.FiniteEtale.InertiaTorsor.ofIdentifiedClass
      R K Ω A H Lambda tau coords f Q q hclass hzero)

end ActualNormalization
