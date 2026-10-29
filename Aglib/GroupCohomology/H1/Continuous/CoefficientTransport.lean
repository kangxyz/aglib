/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.GroupCohomology.H1.Continuous

/-! # Coefficient equivalences and the original continuous H¹ maps

Equivariant additive equivalences act on the existing continuous cocycle
quotient. Their transport commutes with the native coefficient maps, group
restriction and combined relative pullback. All coefficient universes remain
independent, and every cocycle function is the original literal one.
-/

@[expose] public noncomputable section

namespace GroupCohomology.ContinuousH1.CoefficientTransport

universe u₁ u₂ v₁ v₂ w₁ w₂

section EquivariantInverse

variable {G : Type u₁} [Group G] {B : Type v₁} {D : Type v₂}
  [AddCommGroup B] [AddCommGroup D] [DistribMulAction G B] [DistribMulAction G D]
  (e : B ≃+ D) (he : ∀ (γ : G) b, e (γ • b) = γ • e b)

include he in
/-- The inverse of the supplied equivariant additive equivalence is equivariant. -/
theorem coefficientEquiv_symm_equivariant (γ : G) (d : D) :
    e.symm (γ • d) = γ • e.symm d := by
  apply e.injective
  rw [AddEquiv.apply_symm_apply, he, AddEquiv.apply_symm_apply]

end EquivariantInverse

section Equivalences
variable {G : Type u₁} [Group G] [TopologicalSpace G]
variable {B : Type v₁} {D : Type v₂} [AddCommGroup B] [AddCommGroup D]
variable [TopologicalSpace B] [DiscreteTopology B] [TopologicalSpace D] [DiscreteTopology D]
variable [DistribMulAction G B] [ContinuousSMul G B] [DistribMulAction G D] [ContinuousSMul G D]
variable (e : B ≃+ D) (he : ∀ (γ : G) b, e (γ • b) = γ • e b)

/-- The original equivariant additive equivalence as a discrete continuous coefficient map. -/
def coefficientMapOfEquiv : CoefficientMap G B D where
  toContinuousAddMonoidHom := { e.toAddMonoidHom with continuous_toFun :=
    continuous_of_discreteTopology }
  map_smul' := he

/-- An equivariant additive equivalence acts on the original continuous H¹ quotient.
The cocycle map is literal postcomposition with the supplied equivalence. -/
def coefficientH1Equiv : H1 G B ≃+ H1 G D where
  toFun := (coefficientMapOfEquiv e he).onH1
  invFun := (coefficientMapOfEquiv e.symm (coefficientEquiv_symm_equivariant e he)).onH1
  left_inv a := by
    obtain ⟨c, rfl⟩ := classOf_surjective G B a
    simp only [CoefficientMap.onH1_classOf]
    congr 1
    apply Cocycle.ext
    intro γ
    exact e.symm_apply_apply _
  right_inv a := by
    obtain ⟨c, rfl⟩ := classOf_surjective G D a
    simp only [CoefficientMap.onH1_classOf]
    congr 1
    apply Cocycle.ext
    intro γ
    exact e.apply_symm_apply _
  map_add' := (coefficientMapOfEquiv e he).onH1.map_add

/-- The induced equivalence retains the original cocycle postcomposition map. -/
theorem coefficientH1Equiv_classOf (c : Cocycle G B) :
    coefficientH1Equiv e he (classOf G B c) =
      classOf G D ((coefficientMapOfEquiv e he).onCocycles c) := rfl

end Equivalences

section CoefficientTransport
variable {G : Type u₁} {H : Type u₂} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]
variable {B₀ : Type v₁} {B : Type v₂} {D₀ : Type w₁} {D : Type w₂}
variable [AddCommGroup B₀] [AddCommGroup B] [AddCommGroup D₀] [AddCommGroup D]
variable [TopologicalSpace B₀] [DiscreteTopology B₀] [TopologicalSpace B] [DiscreteTopology B]
variable [TopologicalSpace D₀] [DiscreteTopology D₀] [TopologicalSpace D] [DiscreteTopology D]
variable [DistribMulAction G B₀] [ContinuousSMul G B₀] [DistribMulAction G B] [ContinuousSMul G B]
variable [DistribMulAction H D₀] [ContinuousSMul H D₀] [DistribMulAction H D] [ContinuousSMul H D]
variable (φ : ContinuousMonoidHom H G)
variable (e : B₀ ≃+ B) (he : ∀ (g : G) b, e (g • b) = g • e b)
variable (d : D₀ ≃+ D) (hd : ∀ (h : H) a, d (h • a) = h • d a)
variable (q : PullbackMap (A := B) (B := D) φ)

/-- Transport the original relative coefficient map by the literal function d⁻¹ ∘ q ∘ e. -/
def transportedPullbackMap : PullbackMap (A := B₀) (B := D₀) φ where
  toFun b := d.symm (q (e b))
  map_zero' := by
    change d.symm (q (e 0)) = 0
    rw [e.map_zero]
    exact (congrArg d.symm q.toAddMonoidHom.map_zero).trans d.symm.map_zero
  map_add' a b := by simp only [map_add, q.map_add]
  continuous_toFun := continuous_of_discreteTopology
  map_smul' h b := by
    rw [he, q.map_smul]
    exact coefficientEquiv_symm_equivariant d hd h _

/-- Coefficient equivalences commute with the original relative pullback on H¹. -/
theorem coefficientH1Equiv_pullback (a : H1 G B₀) :
    coefficientH1Equiv d hd ((transportedPullbackMap φ e he d hd q).onH1 a) =
      q.onH1 (coefficientH1Equiv e he a) := by
  obtain ⟨c, rfl⟩ := classOf_surjective G B₀ a
  rw [PullbackMap.onH1_classOf, coefficientH1Equiv_classOf,
    coefficientH1Equiv_classOf, PullbackMap.onH1_classOf]
  congr 1
  apply Cocycle.ext
  intro h
  exact d.apply_symm_apply _

end CoefficientTransport

section OrdinaryCoefficientTransport
variable {G : Type u₁} [Group G] [TopologicalSpace G]
variable {B₀ : Type v₁} {B : Type v₂} {D₀ : Type w₁} {D : Type w₂}
variable [AddCommGroup B₀] [AddCommGroup B] [AddCommGroup D₀] [AddCommGroup D]
variable [TopologicalSpace B₀] [DiscreteTopology B₀] [TopologicalSpace B] [DiscreteTopology B]
variable [TopologicalSpace D₀] [DiscreteTopology D₀] [TopologicalSpace D] [DiscreteTopology D]
variable [DistribMulAction G B₀] [ContinuousSMul G B₀] [DistribMulAction G B] [ContinuousSMul G B]
variable [DistribMulAction G D₀] [ContinuousSMul G D₀] [DistribMulAction G D] [ContinuousSMul G D]
variable (e : B₀ ≃+ B) (he : ∀ (g : G) b, e (g • b) = g • e b)
variable (d : D₀ ≃+ D) (hd : ∀ (g : G) a, d (g • a) = g • d a)
variable (q : CoefficientMap G B D)

/-- Transport the original coefficient map by the two equivariant additive equivalences. -/
def transportedCoefficientMap : CoefficientMap G B₀ D₀ :=
  (coefficientMapOfEquiv d.symm (coefficientEquiv_symm_equivariant d hd)).comp
    (q.comp (coefficientMapOfEquiv e he))

/-- Ordinary coefficient change commutes with equivalences on the same H¹ quotient. -/
theorem coefficientH1Equiv_coefficient (a : H1 G B₀) :
    coefficientH1Equiv d hd ((transportedCoefficientMap e he d hd q).onH1 a) =
      q.onH1 (coefficientH1Equiv e he a) := by
  obtain ⟨c, rfl⟩ := classOf_surjective G B₀ a
  rw [CoefficientMap.onH1_classOf, coefficientH1Equiv_classOf,
    coefficientH1Equiv_classOf, CoefficientMap.onH1_classOf]
  congr 1
  apply Cocycle.ext
  intro g
  exact d.apply_symm_apply _

end OrdinaryCoefficientTransport

section RestrictionTransport
variable {G : Type u₁} {H : Type u₂} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]
variable {B : Type v₁} {D : Type v₂} [AddCommGroup B] [AddCommGroup D]
variable [TopologicalSpace B] [DiscreteTopology B] [TopologicalSpace D] [DiscreteTopology D]
variable [DistribMulAction G B] [ContinuousSMul G B] [DistribMulAction G D] [ContinuousSMul G D]
variable (φ : ContinuousMonoidHom H G)
variable (e : B ≃+ D) (he : ∀ (g : G) b, e (g • b) = g • e b)

/-- Original group restriction commutes with coefficient equivalence across universes. -/
theorem restriction_coefficientH1Equiv (a : H1 G B) :
    letI := restrictedAction B φ
    letI := restrictedAction_continuous B φ
    letI := restrictedAction D φ
    letI := restrictedAction_continuous D φ
    coefficientH1Equiv e (fun h b => he (φ h) b) (restriction B φ a) =
      restriction D φ (coefficientH1Equiv e he a) := by
  let := restrictedAction B φ
  let := restrictedAction_continuous B φ
  let := restrictedAction D φ
  let := restrictedAction_continuous D φ
  obtain ⟨c, rfl⟩ := classOf_surjective G B a
  rw [restriction_classOf, coefficientH1Equiv_classOf,
    coefficientH1Equiv_classOf, restriction_classOf]
  congr 1

end RestrictionTransport
section RelativeCoefficient
variable {G : Type u₁} {H : Type u₂} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]
variable {B : Type v₁} {D : Type v₂} [AddCommGroup B] [AddCommGroup D]
variable [TopologicalSpace B] [DiscreteTopology B] [TopologicalSpace D] [DiscreteTopology D]
variable [DistribMulAction G B] [ContinuousSMul G B] [DistribMulAction H D] [ContinuousSMul H D]
variable (φ : ContinuousMonoidHom H G) (q : PullbackMap (A := B) (B := D) φ)

/-- A relative coefficient map is an ordinary coefficient map after the
explicit restricted action, with no action identification assumed. -/
def pullbackCoefficientMap :
    letI := restrictedAction B φ
    letI := restrictedAction_continuous B φ
    CoefficientMap H B D := by
  letI := restrictedAction B φ
  letI := restrictedAction_continuous B φ
  exact { q.toContinuousAddMonoidHom with map_smul' := q.map_smul }

/-- The two-step restriction/coefficient map is the existing single combined
PullbackMap on the same common cohomology quotient. -/
theorem pullbackCoefficientMap_restriction (a : H1 G B) :
    letI := restrictedAction B φ
    letI := restrictedAction_continuous B φ
    (pullbackCoefficientMap φ q).onH1 (restriction B φ a) = q.onH1 a := by
  let := restrictedAction B φ
  let := restrictedAction_continuous B φ
  obtain ⟨c, rfl⟩ := classOf_surjective G B a
  rw [restriction_classOf, CoefficientMap.onH1_classOf, PullbackMap.onH1_classOf]
  rfl

end RelativeCoefficient

end GroupCohomology.ContinuousH1.CoefficientTransport
