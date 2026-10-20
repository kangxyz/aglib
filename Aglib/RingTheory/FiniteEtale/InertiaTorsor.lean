/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.FiniteEtale.CoefficientInertia
public import Aglib.RingTheory.FiniteEtale.TorsorCoordinates
public import Aglib.RingTheory.IntegralClosure.Inertia.Etale

/-!
# Inertia extension of supplied algebraic torsors

The actual coefficient algebra is finite etale. Its inertia fixedness, together
with one fixed point of the supplied generic torsor, gives fixedness of every
original embedding. The arbitrary-residue normalization theorem then supplies
etaleness of the literal integral closure. Its coaction and transporter are the
frozen algebraic torsor extension constructions.

The H1 constructors retain the actual original torsor, coefficient coordinates,
chosen point, class-vanishing hypothesis, and any external-class identification.

Source: the five reserved tails of
`R5Lab.Aglib.RingTheory.IntegralClosure.FiniteEtale.CoefficientInertia` and
`H1NormalizationTorsor`, with the arbitrary-residue constructor in
`R5Lab.Aglib.AlgebraicGeometry.Normalization.InertiaTorsor`, at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`. The action-evaluation helper is the
pure algebra slice of `Normalization.H1SchemeTorsor:213–250`.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct
open Algebra.TensorProduct

namespace Algebra.FiniteEtale.GenericMaps

universe u
variable (R B H : Type u) [CommRing R] [CommRing B] [Algebra R B]
  [CommRing H] [Algebra R H]

/-- Evaluate a coaction map on a coefficient point and an algebra point. -/
def evaluateCoaction (alpha : B →ₐ[R] B ⊗[R] H)
    {D : Type u} [CommRing D] [Algebra R D] (a : H →ₐ[R] D) (x : B →ₐ[R] D) :
    B →ₐ[R] D :=
  (Algebra.TensorProduct.lift x a (fun _ _ => .all _ _)).comp alpha

/-- Coassociativity gives the action law on ordinary algebra-valued points. -/
theorem evaluateCoaction_mul {epsilon : H →ₐ[R] R} {delta : H →ₐ[R] H ⊗[R] H}
    (alpha : AlgebraCoaction R B H epsilon delta)
    {D : Type u} [CommRing D] [Algebra R D] (a b : H →ₐ[R] D) (x : B →ₐ[R] D) :
    evaluateCoaction R B H alpha.coact
        ((Algebra.TensorProduct.lift a b (fun _ _ => .all _ _)).comp delta) x =
      evaluateCoaction R B H alpha.coact b (evaluateCoaction R B H alpha.coact a x) := by
  let psi : (B ⊗[R] (H ⊗[R] H)) →ₐ[R] D :=
    Algebra.TensorProduct.lift x (Algebra.TensorProduct.lift a b (fun _ _ => .all _ _))
      (fun _ _ => .all _ _)
  have hleft : Algebra.TensorProduct.lift x
      ((Algebra.TensorProduct.lift a b (fun _ _ => .all _ _)).comp delta)
      (fun _ _ => .all _ _) =
      psi.comp (Algebra.TensorProduct.map (AlgHom.id R B) delta) := by
    apply Algebra.TensorProduct.ext'
    intro c h
    simp [psi]
  have hright : Algebra.TensorProduct.lift
      (evaluateCoaction R B H alpha.coact a x) b (fun _ _ => .all _ _) =
      (psi.comp (Algebra.TensorProduct.assoc R R R B H H).toAlgHom).comp
        (Algebra.TensorProduct.map alpha.coact (AlgHom.id R H)) := by
    apply Algebra.TensorProduct.ext'
    intro c h
    change (Algebra.TensorProduct.lift x a (fun _ _ => .all _ _) (alpha.coact c)) * b h =
      psi ((Algebra.TensorProduct.assoc R R R B H H) ((alpha.coact c) ⊗ₜ[R] h))
    generalize alpha.coact c = z
    induction z using TensorProduct.inductionOn with
    | tmul c k => simp [psi, _root_.mul_assoc]
    | add z w hz hw => simp only [TensorProduct.add_tmul, map_add, add_mul, hz, hw]
  ext c
  have hc := congrArg psi (DFunLike.congr_fun alpha.coassoc c)
  simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom] at hc
  exact (DFunLike.congr_fun hleft (alpha.coact c)).trans
    (hc.trans (DFunLike.congr_fun hright (alpha.coact c)).symm)

end Algebra.FiniteEtale.GenericMaps

namespace Algebra.FiniteEtale.InertiaTorsor

open GenericMaps TorsorExtension
open GroupCohomology.ContinuousH1

universe u v
variable (R K Ω A H : Type u)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω]
  [IsGalois K Ω] [IsAlgClosed Ω]
  [CommRing A] [Algebra K A] [Algebra R A] [IsScalarTower R K A]
  [Algebra.Etale K A]
  [CommRing H] [Algebra R H] [Module.Finite R H] [Algebra.Etale R H]

local instance : Module.Finite K A := Algebra.FormallyUnramified.finite_of_free K A

variable {epsilon : H →ₐ[R] R} {delta : H →ₐ[R] H ⊗[R] H}

section FixedPoint

variable (Q : Ideal (integralClosure R Ω)) [Q.IsPrime]
  [Q.LiesOver (IsLocalRing.maximalIdeal R)]

/-- The coefficient theorem and a common fixed point supply the complete
every-embedding inertia premise for the literal normalization. -/
theorem model_etale_of_fixedPoint
    (tau : OriginalTorsorData R K A H epsilon delta) (f : A →ₐ[K] Ω)
    (hf : ∀ sigma ∈ Q.inertia (Ω ≃ₐ[K] Ω), sigma.toAlgHom.comp f = f) :
    Algebra.Etale R (integralClosure R A) :=
  integralClosure.Inertia.Algebra.model_etale_of_absolute_inertia_trivial_on_generic_fiber
    R K Ω A Q (inertia_trivial_of_fixed_point R K Ω A H Q tau
      (fun sigma hsigma h =>
        CoefficientInertia.coefficients_fixed_by_absolute_inertia R K Ω H Q sigma hsigma h)
      f hf)

/-- Extend the supplied generic torsor from its common inertia-fixed point.
Coefficient inertia and finite etaleness of the normalization are derived. -/
def ofFixedPoint
    (tau : OriginalTorsorData R K A H epsilon delta) (f : A →ₐ[K] Ω)
    (hf : ∀ sigma ∈ Q.inertia (Ω ≃ₐ[K] Ω), sigma.toAlgHom.comp f = f) :
    AlgebraicTorsorData R (integralClosure R A) H epsilon delta := by
  haveI := integralClosure.finite_of_etale R K A
  haveI := model_etale_of_fixedPoint R K Ω A H Q tau f hf
  exact normalizationTorsor R K A H tau

/-- The extension has the same canonical original-algebra generic square. -/
theorem ofFixedPoint_square
    (tau : OriginalTorsorData R K A H epsilon delta) (f : A →ₐ[K] Ω)
    (hf : ∀ sigma ∈ Q.inertia (Ω ≃ₐ[K] Ω), sigma.toAlgHom.comp f = f) :
    (actualTensorEquiv R K A H).toAlgHom.comp
        (BaseChange.map R K (ofFixedPoint R K Ω A H Q tau f hf).coaction.coact) =
      tau.coaction.coact.comp (integralClosure.genericFiberEquiv R K A).toAlgHom := by
  have := integralClosure.finite_of_etale R K A
  have := model_etale_of_fixedPoint R K Ω A H Q tau f hf
  exact normalizationTorsor_square R K A H tau

end FixedPoint

section H1

variable (Lambda : Type v) [AddCommGroup Lambda] [TopologicalSpace Lambda]
  [IsTopologicalAddGroup Lambda] [DistribMulAction (Ω ≃ₐ[K] Ω) Lambda]
  [ContinuousSMul (Ω ≃ₐ[K] Ω) Lambda]
  (tau : OriginalTorsorData R K A H epsilon delta)
  (coords : TorsorCoordinates.CoefficientPointCoordinates R K Ω H Lambda epsilon delta)
  (f : A →ₐ[K] Ω)
  (Q : Ideal (integralClosure R Ω)) [Q.IsPrime]
  [Q.LiesOver (IsLocalRing.maximalIdeal R)]

/-- The actual class's zero inertia restriction gives the algebraic torsor on
the same normalization, using the fixed point derived in the lower H1 layer. -/
def ofH1 (hvan : TorsorCoordinates.inertiaClass R K Ω A H Lambda tau coords f Q = 0) :
    AlgebraicTorsorData R (integralClosure R A) H epsilon delta :=
  ofFixedPoint R K Ω A H Q tau
    (TorsorCoordinates.fixedPoint R K Ω A H Lambda tau coords f Q hvan)
    (TorsorCoordinates.fixedPoint_fixed R K Ω A H Lambda tau coords f Q hvan)

/-- Finite etaleness of the literal model follows from the same class vanishing. -/
theorem model_etale_of_H1
    (hvan : TorsorCoordinates.inertiaClass R K Ω A H Lambda tau coords f Q = 0) :
    Algebra.Etale R (integralClosure R A) :=
  model_etale_of_fixedPoint R K Ω A H Q tau
    (TorsorCoordinates.fixedPoint R K Ω A H Lambda tau coords f Q hvan)
    (TorsorCoordinates.fixedPoint_fixed R K Ω A H Lambda tau coords f Q hvan)

/-- The H1 construction retains the canonical original-algebra generic square. -/
theorem ofH1_square
    (hvan : TorsorCoordinates.inertiaClass R K Ω A H Lambda tau coords f Q = 0) :
    (actualTensorEquiv R K A H).toAlgHom.comp
        (BaseChange.map R K (ofH1 R K Ω A H Lambda tau coords f Q hvan).coaction.coact) =
      tau.coaction.coact.comp (integralClosure.genericFiberEquiv R K A).toAlgHom :=
  ofFixedPoint_square R K Ω A H Q tau
    (TorsorCoordinates.fixedPoint R K Ω A H Lambda tau coords f Q hvan)
    (TorsorCoordinates.fixedPoint_fixed R K Ω A H Lambda tau coords f Q hvan)

/-- An external class is usable only with its explicit identification with the
class constructed from this original torsor and these coefficient coordinates. -/
def ofIdentifiedClass (q : H1 (Ω ≃ₐ[K] Ω) Lambda)
    (hclass : q = TorsorCoordinates.genericClass R K Ω A H Lambda tau coords f)
    (hvan :
      letI := restrictedAction Lambda
        (TorsorCocycle.subgroupInclusion K Ω (Q.inertia (Ω ≃ₐ[K] Ω)))
      letI := restrictedAction_continuous Lambda
        (TorsorCocycle.subgroupInclusion K Ω (Q.inertia (Ω ≃ₐ[K] Ω)))
      restriction Lambda (TorsorCocycle.subgroupInclusion K Ω (Q.inertia (Ω ≃ₐ[K] Ω))) q = 0) :
    AlgebraicTorsorData R (integralClosure R A) H epsilon delta :=
  ofH1 R K Ω A H Lambda tau coords f Q (by
    unfold TorsorCoordinates.inertiaClass
    rw [← hclass]
    exact hvan)

end H1
end Algebra.FiniteEtale.InertiaTorsor
