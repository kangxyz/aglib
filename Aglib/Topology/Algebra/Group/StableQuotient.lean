/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.GroupCohomology.H1.Continuous
public import Mathlib.Topology.Algebra.Group.Quotient

/-!
# Continuous actions on stable additive subgroup quotients

For an arbitrary group G acting additively on M and an actual additive subgroup R, the supplied
  condition that every g maps R into R constructs the quotient action. The quotient has the
  usual topology. Joint continuity descends along its open quotient projection, and that same
  projection is a continuous equivariant coefficient map. No closedness, Hausdorffness, or
  automatic stability statement is assumed.

Extraction source: `R5Lab.Aglib.TopologicalGroup.StableQuotient`, R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`82647b23bac6372af9ada37107ddbd65bd4833d5d14b290b3e030677686f3e1f`.
The exact source hypotheses, actual objects and forward maps are retained under native names.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace AddSubgroup.StableQuotient

variable {G M : Type*} [Group G] [AddCommGroup M] [DistribMulAction G M]
  (R : AddSubgroup M)
  (hstable : ∀ (g : G) (k : M), k ∈ R → g • k ∈ R)

/-- The inherited action on the actual subgroup quotient, when its relation
subgroup is stable. -/
@[instance_reducible] def action : DistribMulAction G (M ⧸ R) :=
  let f : G → (M ⧸ R →+ M ⧸ R) := fun g =>
    QuotientAddGroup.map R R
      { toFun := fun k => g • k
        map_zero' := smul_zero g
        map_add' := smul_add g }
      (by intro k hk; exact hstable g k hk)
  { smul g q := f g q
    one_smul q := by
      obtain ⟨k, rfl⟩ := QuotientAddGroup.mk'_surjective R q
      change QuotientAddGroup.mk' R ((1 : G) • k) = QuotientAddGroup.mk' R k
      rw [one_smul]
    mul_smul g h q := by
      obtain ⟨k, rfl⟩ := QuotientAddGroup.mk'_surjective R q
      change QuotientAddGroup.mk' R ((g * h) • k) = QuotientAddGroup.mk' R (g • h • k)
      rw [mul_smul]
    smul_zero g := (f g).map_zero
    smul_add g q q' := (f g).map_add q q' }

@[simp] theorem action_mk (g : G) (k : M) :
    @SMul.smul G (M ⧸ R) (action R hstable).toSMul g (QuotientAddGroup.mk' R k) =
      QuotientAddGroup.mk' R (g • k) := rfl

variable [TopologicalSpace G] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [ContinuousSMul G M]

/-- Openness of the canonical additive-group quotient descends joint action
continuity. No closedness or Hausdorff assumption on the incoming subgroup is used. -/
theorem continuousAction :
    let := action R hstable
    ContinuousSMul G (M ⧸ R) := by
  let := action R hstable
  refine ⟨?_⟩
  rw [← (IsOpenQuotientMap.id.prodMap
    (QuotientAddGroup.isOpenQuotientMap_mk (N := R))).continuous_comp_iff]
  exact continuous_quot_mk.comp continuous_smul

/-- The actual quotient projector is a continuous equivariant coefficient map
for the inherited action, rather than an assumed target-comparison map. -/
def coefficientProjection :
    let := action R hstable
    let := continuousAction R hstable
    _root_.GroupCohomology.ContinuousH1.CoefficientMap G M (M ⧸ R) := by
  let := action R hstable
  let := continuousAction R hstable
  exact
    { toContinuousAddMonoidHom :=
        { toAddMonoidHom := QuotientAddGroup.mk' R
          continuous_toFun := continuous_quot_mk }
      map_smul' := fun _ _ => rfl }

end AddSubgroup.StableQuotient
