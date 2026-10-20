/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.FiniteEtale.TorsorCocycle

/-!
# Coefficient coordinates and inertia restriction of an algebraic torsor

A supplied mark identifies the coefficient group with the points of the actual
coefficient algebra and respects its counit, comultiplication, and Galois action.
The actual coaction and bijective transporter construct a continuous cocycle.
Its class is independent of the chosen point. Vanishing of its restriction to
the specified inertia subgroup gives a fixed point of the same generic algebra.
The reverse-normalization and external-class identification endpoints remain
with the algebraic-geometry consumers.
Those consumers supply the DVR, prime, lies-over, and finite etale coefficient
hypotheses separately; this module extracts a fixed point from the restriction
to the actual inertia subgroup of the specified ideal.
-/

/-!
Extraction source: `R5Lab.Aglib.RingTheory.IntegralClosure.FiniteEtale.H1NormalizationTorsor`,
R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`934d2e7be47770da69403bc31a32308a7492ad8fdb0b170eaadbd42ec2f9246b`.
Historical source locators retain their original basis. -/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false

open scoped TensorProduct
open Algebra.TensorProduct

namespace Algebra.FiniteEtale.TorsorCoordinates

open integralClosure Algebra.FiniteEtale.GenericMaps Algebra.FiniteEtale.TorsorExtension
open _root_.GroupCohomology.ContinuousH1

universe u v

/-- Ordinary actual-coefficient coordinates, not a replacement H1 or torsor. -/
structure CoefficientPointCoordinates
    (R K Ω H : Type u) (Lambda : Type v)
    [CommRing R] [Field K] [Algebra R K] [Field Ω] [Algebra K Ω]
    [CommRing H] [Algebra R H] [AddCommGroup Lambda]
    [DistribMulAction (Ω ≃ₐ[K] Ω) Lambda]
    (epsilon : H →ₐ[R] R) (delta : H →ₐ[R] H ⊗[R] H) where
  mark : Lambda ≃ ((K ⊗[R] H) →ₐ[K] Ω)
  mark_zero : mark 0 = (Algebra.ofId K Ω).comp (BaseChange.counit R K epsilon)
  mark_add (a b : Lambda) : mark (a + b) =
    (Algebra.TensorProduct.lift (mark a) (mark b) (fun _ _ => .all _ _)).comp
      (BaseChange.comul R K delta)
  mark_galois (sigma : Ω ≃ₐ[K] Ω) (a : Lambda) :
    sigma.toAlgHom.comp (mark a) = mark (sigma • a)

variable (R K Ω A H : Type u) (Lambda : Type v)
  [CommRing R]
  [Field K] [Algebra R K]
  [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω]
  [CommRing A] [Algebra K A] [Algebra R A] [IsScalarTower R K A]
  [Algebra.Etale K A]
  [CommRing H] [Algebra R H]
  [AddCommGroup Lambda] [TopologicalSpace Lambda]
  [IsTopologicalAddGroup Lambda] [DistribMulAction (Ω ≃ₐ[K] Ω) Lambda]
  [ContinuousSMul (Ω ≃ₐ[K] Ω) Lambda]
local instance : Module.Finite K A := Algebra.FormallyUnramified.finite_of_free K A

variable {epsilon : H →ₐ[R] R} {delta : H →ₐ[R] H ⊗[R] H}
variable (tau : OriginalTorsorData R K A H epsilon delta)
  (coords : CoefficientPointCoordinates R K Ω H Lambda epsilon delta)
  (f : A →ₐ[K] Ω)

/-- The genuine continuous cocycle of this actual tau, chosen point and mark. -/
def cocycle : Cocycle (Ω ≃ₐ[K] Ω) Lambda :=
  TorsorCocycle.basedCocycle K Ω A (K ⊗[R] H) tau.coaction Lambda
    coords.mark coords.mark_add coords.mark_galois tau.transporter_bijective f

/-- Its class lies in the retained common continuous H1. -/
def genericClass : H1 (Ω ≃ₐ[K] Ω) Lambda :=
  classOf (Ω ≃ₐ[K] Ω) Lambda (cocycle R K Ω A H Lambda tau coords f)

omit [Algebra R Ω] [IsScalarTower R K Ω] in
/-- The actual generic class does not depend on the internal point choice. -/
theorem genericClass_independent (g : A →ₐ[K] Ω) :
    genericClass R K Ω A H Lambda tau coords f =
      genericClass R K Ω A H Lambda tau coords g :=
  TorsorCocycle.basedCocycle_class_independent K Ω A (K ⊗[R] H) tau.coaction Lambda
    coords.mark coords.mark_add coords.mark_galois tau.transporter_bijective g f

variable (Q : Ideal (integralClosure R Ω))

/-- Literal restriction of the constructed class to this SAME inertia group. -/
def inertiaClass :
    letI := restrictedAction Lambda (TorsorCocycle.subgroupInclusion K Ω (Q.inertia (Ω ≃ₐ[K] Ω)))
    letI := restrictedAction_continuous Lambda
      (TorsorCocycle.subgroupInclusion K Ω (Q.inertia (Ω ≃ₐ[K] Ω)))
    H1 (Q.inertia (Ω ≃ₐ[K] Ω)) Lambda :=
  restriction Lambda (TorsorCocycle.subgroupInclusion K Ω (Q.inertia (Ω ≃ₐ[K] Ω)))
    (genericClass R K Ω A H Lambda tau coords f)

/-- Zero restriction gives a concrete shifted point of the original A. -/
theorem exists_fixed_point
    (hvan : inertiaClass R K Ω A H Lambda tau coords f Q = 0) :
    ∃ g : A →ₐ[K] Ω, ∀ sigma : Q.inertia (Ω ≃ₐ[K] Ω),
      sigma.val.toAlgHom.comp g = g :=
  TorsorCocycle.fixed_point_of_restriction_zero K Ω A (K ⊗[R] H) tau.coaction Lambda
    coords.mark coords.mark_add coords.mark_galois tau.transporter_bijective f
    (Q.inertia (Ω ≃ₐ[K] Ω)) hvan

/-- Select the proved actual point; the selection is internal and not a fixed-point premise. -/
def fixedPoint (hvan : inertiaClass R K Ω A H Lambda tau coords f Q = 0) : A →ₐ[K] Ω :=
  Classical.choose (exists_fixed_point R K Ω A H Lambda tau coords f Q hvan)

theorem fixedPoint_fixed (hvan : inertiaClass R K Ω A H Lambda tau coords f Q = 0)
    (sigma : Ω ≃ₐ[K] Ω) (hsigma : sigma ∈ Q.inertia (Ω ≃ₐ[K] Ω)) :
    sigma.toAlgHom.comp (fixedPoint R K Ω A H Lambda tau coords f Q hvan) =
      fixedPoint R K Ω A H Lambda tau coords f Q hvan :=
  Classical.choose_spec (exists_fixed_point R K Ω A H Lambda tau coords f Q hvan) ⟨sigma, hsigma⟩

end Algebra.FiniteEtale.TorsorCoordinates
