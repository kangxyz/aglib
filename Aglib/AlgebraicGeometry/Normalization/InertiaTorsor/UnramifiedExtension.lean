/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Normalization.InertiaTorsor.OriginalRepresentation
public import Aglib.AlgebraicGeometry.Normalization.InertiaTorsor.ClassExtension

/-!
# Unique model extension of an original inertia-zero class

An original continuous Galois H¹ class whose restriction to the actual inertia
of the same chosen integral-closure prime is zero extends uniquely to an
actual model Ext-H¹ class over the DVR. Realization constructs its generic
torsor and point; normalization and the literal modelToGaloisH1 give extension
and uniqueness. Hopf coordinates, Ext/descent, Galois-category/fibre-functor,
positive annihilator and invertibility premises remain explicit.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.PreGaloisCategory FintypeCatDiscrete
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (fiberToFinite)
open _root_.AlgebraicGeometry.Scheme.EtaleFundamentalGroups
open _root_.GroupCohomology.ContinuousH1
open _root_.AlgebraicGeometry.Scheme.EtaleCohomology _root_.CategoryTheory.Abelian
open _root_.CategoryTheory.Functor.LargePresheaf
open AlgebraicGeometry.Scheme.FiniteEtale
open _root_.AlgebraicGeometry.Scheme.FiniteEtale.GenericRestriction
  (genericInclusion genericPoint_compat genericFibreMap)
open Algebra.FiniteEtale.TorsorCoordinates Algebra.FiniteEtale.TorsorExtension
open AlgebraicGeometry.Scheme.FiniteEtale.FieldGalois.OverRing
open AlgebraicGeometry.Scheme.FiniteEtale.InertiaTorsor.SheafClass
open AlgebraicGeometry.Scheme.FiniteEtale.InertiaTorsor.ClassExtension
open AlgebraicGeometry.Scheme.FiniteEtale.InertiaTorsor.OriginalRepresentation

namespace AlgebraicGeometry.Scheme.FiniteEtale.InertiaTorsor.UnramifiedExtension

universe u wR wK

variable (R K Ω H Lambda : Type u)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω]
  [IsGalois K Ω] [IsAlgClosed Ω]
  [CommRing H] [HopfAlgebra R H] [Coalgebra.IsCocomm R H]
  [Module.Finite R H] [Algebra.Etale R H]
  [AddCommGroup Lambda] [TopologicalSpace Lambda] [DiscreteTopology Lambda]
  [IsTopologicalAddGroup Lambda] [DistribMulAction (Ω ≃ₐ[K] Ω) Lambda]
  [ContinuousSMul (Ω ≃ₐ[K] Ω) Lambda]
  (coords : CoefficientPointCoordinates R K Ω H Lambda
    (Bialgebra.counitAlgHom R H) (Bialgebra.comulAlgHom R H))
  [GaloisCategory (Scheme.FiniteEtale (Spec (.of R)))]
  [PreGaloisCategory.FiberFunctor (fiberToFinite (basePoint R Ω))]
  [GaloisCategory (Scheme.FiniteEtale (Spec (.of K)))]
  [PreGaloisCategory.FiberFunctor (fiberToFinite (basePoint K Ω))]
  [HasExt.{wR} (AbelianSheaf.{u, u + 1} (Spec (.of R)))]
  [HasExt.{wK} (AbelianSheaf.{u, u + 1} (Spec (.of K)))]
  (hAK : Stacks03AJ.{u, wK} (Spec (.of K))) (hRK : Stacks03RV (Spec (.of K)))
  (n : ℕ) (hpos : 0 < n) (hkill : ∀ a : Lambda, n • a = 0)
  (hunit : LevelInvertible (Spec (.of R)) n)
  (hAR : Stacks03AJ.{u, wR} (Spec (.of R))) (hRR : Stacks03RV (Spec (.of R)))
  (Q : Ideal (integralClosure R Ω)) [Q.IsPrime]
  [Q.LiesOver (IsLocalRing.maximalIdeal R)]

include hAR hRR in
/-- Source K2-018#prop:k2018-arithmetic-characters, revision
e73d98b1b5c1e5abcdebf7d058e436d792b87982: every ORIGINAL native continuous
Galois H1 class whose literal restriction to the SAME Q.inertia is zero has
a unique ACTUAL model Ext-H1 class under the existing literal modelToGaloisH1.
No generic algebra A, OriginalTorsorData tau, point f, representative equality,
final-map injection or extension theorem is supplied as a hypothesis.
This local deduction retains the explicit inputs above and the independently
accepted field-realization dependency closure. -/
theorem existsUnique_modelClass_of_inertia_zero (ξ : H1 (Ω ≃ₐ[K] Ω) Lambda)
    (hξ :
      letI := restrictedAction Lambda
        (Algebra.FiniteEtale.TorsorCocycle.subgroupInclusion K Ω (Q.inertia (Ω ≃ₐ[K] Ω)))
      letI := restrictedAction_continuous Lambda
        (Algebra.FiniteEtale.TorsorCocycle.subgroupInclusion K Ω (Q.inertia (Ω ≃ₐ[K] Ω)))
      restriction Lambda
        (Algebra.FiniteEtale.TorsorCocycle.subgroupInclusion K Ω (Q.inertia (Ω ≃ₐ[K] Ω))) ξ = 0) :
    ∃! a : H1Etale (Spec (.of R)) (normalizationCoefficientSheaf R H),
      modelToGaloisH1 R K Ω H Lambda coords hAK hRK n hpos hkill hunit a = ξ := by
  obtain ⟨A, hfinite, hetale, tau, f, hclass⟩ :=
    exists_original_torsor R K Ω H Lambda coords ξ
  let := originalScalarAlgebra R K A
  let := originalScalarTower R K A
  let := hfinite
  let := hetale
  have hvan : inertiaClass R K Ω A H Lambda tau coords f Q = 0 := by
    unfold inertiaClass
    rw [hclass]
    exact hξ
  rw [← hclass]
  exact existsUnique_modelClass R K Ω H Lambda coords hAK hRK n hpos hkill hunit
    hAR hRR A tau f Q hvan

end AlgebraicGeometry.Scheme.FiniteEtale.InertiaTorsor.UnramifiedExtension
