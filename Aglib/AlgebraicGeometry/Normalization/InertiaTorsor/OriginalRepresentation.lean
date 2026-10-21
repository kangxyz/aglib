/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Normalization.InertiaTorsor.FieldRealization
public import Aglib.RingTheory.FiniteEtale.TensorHopf

/-!
# Realization with the literal generic coefficient tensor

Specializing field realization to the literal Hopf algebra K ⊗[R] H gives
actual original torsor data and a point with the prescribed genericClass.
The R-algebra on the resulting K-algebra is the structural composite, with
its scalar tower. No coefficient Hopf realization or inertia condition is inferred.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct CategoryTheory.PreGaloisCategory FintypeCatDiscrete
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (fiberToFinite)
open _root_.AlgebraicGeometry.Scheme.EtaleFundamentalGroups
open _root_.GroupCohomology.ContinuousH1
open AlgebraicGeometry.Scheme.FiniteEtale
open AlgebraicGeometry.Scheme.FiniteEtale.FieldGalois.OverRing Algebra.FiniteEtale.TorsorCoordinates
open Algebra.FiniteEtale.TorsorExtension
open Algebra.FiniteEtale.TensorHopf

namespace AlgebraicGeometry.Scheme.FiniteEtale.InertiaTorsor.OriginalRepresentation
universe u

/-- The R-algebra on the constructed K-algebra is the actual composite R -> K -> A. -/
abbrev originalScalarAlgebra (R K : Type u) [CommRing R] [Field K] [Algebra R K]
    (A : CommAlgCat.{u} K) : Algebra R A :=
  Algebra.compHom A (algebraMap R K)

theorem originalScalarTower (R K : Type u) [CommRing R] [Field K] [Algebra R K]
    (A : CommAlgCat.{u} K) :
    letI := originalScalarAlgebra R K A
    IsScalarTower R K A := by
  let := originalScalarAlgebra R K A
  exact IsScalarTower.of_algebraMap_eq' rfl

variable (R K Ω H Lambda : Type u)
  [CommRing R] [hDomain : IsDomain R] [hDvr : IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [hFraction : IsFractionRing R K]
  [Field Ω] [Algebra K Ω] [hAlgebraOmega : Algebra R Ω] [hTower : IsScalarTower R K Ω]
  [IsGalois K Ω] [IsAlgClosed Ω]
  [CommRing H] [HopfAlgebra R H] [Coalgebra.IsCocomm R H]
  [Module.Finite R H] [Algebra.Etale R H]
  [AddCommGroup Lambda] [TopologicalSpace Lambda] [DiscreteTopology Lambda]
  [IsTopologicalAddGroup Lambda] [DistribMulAction (Ω ≃ₐ[K] Ω) Lambda]
  [ContinuousSMul (Ω ≃ₐ[K] Ω) Lambda]
  (coords : CoefficientPointCoordinates R K Ω H Lambda
    (Bialgebra.counitAlgHom R H) (Bialgebra.comulAlgHom R H))
  [GaloisCategory (Scheme.FiniteEtale (Spec (.of K)))]
  [PreGaloisCategory.FiberFunctor (fiberToFinite (basePoint K Ω))]

omit hDomain hDvr hFraction hAlgebraOmega hTower in
/-- Source K2-018#prop:k2018-arithmetic-characters, revision
e73d98b1b5c1e5abcdebf7d058e436d792b87982: every ORIGINAL native continuous
class has an ACTUAL finite-etale K-algebra A, the exact algebraic OriginalTorsorData,
and an actual Ω-point whose ORIGINAL positive-transporter genericClass is that class.
Coefficient Hopf/marking and field GC/FF inputs remain explicit. Inertia is not required. -/
theorem exists_original_torsor
    [_hDomain : IsDomain R] [_hDvr : IsDiscreteValuationRing R]
    [_hFraction : IsFractionRing R K] [_hAlgebraOmega : Algebra R Ω]
    [_hTower : IsScalarTower R K Ω]
    (ξ : H1 (Ω ≃ₐ[K] Ω) Lambda) :
    ∃ (A : CommAlgCat.{u} K),
      letI := originalScalarAlgebra R K A
      letI := originalScalarTower R K A
      ∃ (hfinite : Module.Finite K A) (hetale : Algebra.Etale K A),
        letI := hfinite
        letI := hetale
        ∃ (tau : OriginalTorsorData R K A H
          (Bialgebra.counitAlgHom R H) (Bialgebra.comulAlgHom R H)) (f : A →ₐ[K] Ω),
          genericClass R K Ω A H Lambda tau coords f = ξ := by
  let : Module.Finite K (K ⊗[R] H) := inferInstance
  let : Algebra.Etale K (K ⊗[R] H) := inferInstance
  have hadd : ∀ a b : Lambda, coords.mark (a + b) =
      (Algebra.TensorProduct.lift (coords.mark a) (coords.mark b) (fun _ _ => .all _ _)).comp
        (Bialgebra.comulAlgHom K (K ⊗[R] H)) := by
    intro a b
    rw [tensor_comul_eq_generic R K H]
    exact coords.mark_add a b
  obtain ⟨A, hfinite, hetale, α, hT, f, hA, hclass⟩ :=
    FieldRealization.exists_algebraic_field_torsor K Ω (K ⊗[R] H) Lambda
      coords.mark hadd coords.mark_galois ξ
  let := hfinite
  let := hetale
  let := originalScalarAlgebra R K A
  let := originalScalarTower R K A
  let tau := originalTorsorOfField R K H A α hA hT
  refine ⟨A, hfinite, hetale, tau, f, ?_⟩
  calc
    genericClass R K Ω A H Lambda tau coords f =
      classOf (Ω ≃ₐ[K] Ω) Lambda
        (Algebra.FiniteEtale.TorsorCocycle.basedCocycle K Ω A (K ⊗[R] H) α Lambda coords.mark hadd
          coords.mark_galois hT f) := by
      apply congrArg (classOf (Ω ≃ₐ[K] Ω) Lambda)
      apply _root_.GroupCohomology.ContinuousH1.Cocycle.ext
      intro σ
      rfl
    _ = ξ := hclass

end AlgebraicGeometry.Scheme.FiniteEtale.InertiaTorsor.OriginalRepresentation
