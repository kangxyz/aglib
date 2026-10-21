/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.GroupCohomology.H1.Continuous

/-!
# Inner conjugacy on continuous first cohomology

Inner conjugation on the group, together with the inverse action on coefficients, changes a
continuous cocycle by the explicit principal cocycle of -(g⁻¹ • c(g)). The action and group
operations have their stated continuity hypotheses. This proves identity of the resulting map
on the actual continuous H1 quotient.

Extraction source: `R5Lab.Aglib.GroupCohomology.H1.InnerConjugacy`, R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`7a0e28f3f63a56979b8c06d362956695198ffeb969e72a42536a324b64ceb75d`.
The source conditions, actual objects and canonical maps are retained under native names.
-/

@[expose] public section

/-!
# Inner-conjugacy invariance of continuous first cohomology

For a topological group acting continuously on an additive topological group,
conjugating the group by `g` and acting on coefficients by `g⁻¹` induces the
identity on continuous `H¹`. The proof exhibits the difference of the transformed
cocycle and the original cocycle as an explicit principal cocycle.

This is a theorem about genuine continuous group/coefficient maps. It is not,
by itself, an algebraic-closure embedding comparison or a proof that all choices
of those embeddings give the same restriction map.
-/

namespace GroupCohomology.ContinuousH1.InnerConjugacy

open _root_.GroupCohomology.ContinuousH1

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Inner conjugation as a genuine continuous group homomorphism. -/
def conjugation (g : G) : ContinuousMonoidHom G G where
  toFun h := g * h * g⁻¹
  map_one' := by simp
  map_mul' h k := by simp [mul_assoc]
  continuous_toFun := (continuous_const.mul continuous_id).mul continuous_const

@[simp] theorem conjugation_apply (g h : G) : conjugation G g h = g * h * g⁻¹ := rfl

variable (A : Type*) [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [DistribMulAction G A] [ContinuousSMul G A]

/-- The coefficient map `a ↦ g⁻¹ • a` is equivariant relative to conjugation by `g`.
Together these maps give the usual inner-conjugacy action on continuous cohomology. -/
def conjugacyMap (g : G) : PullbackMap (A := A) (B := A) (conjugation G g) where
  toFun a := g⁻¹ • a
  map_zero' := smul_zero _
  map_add' a b := smul_add _ a b
  continuous_toFun := continuous_const.smul continuous_id
  map_smul' h a := by
    change g⁻¹ • ((g * h * g⁻¹) • a) = h • (g⁻¹ • a)
    simp only [← mul_smul, mul_assoc, inv_mul_cancel_left]

omit [IsTopologicalAddGroup A] in
theorem conjugacyMap_apply (g : G) (a : A) : conjugacyMap G A g a = g⁻¹ • a := rfl

omit [IsTopologicalGroup G] [ContinuousSMul G A] in
/-- The cocycle inverse formula needed for the explicit principal difference. -/
theorem cocycle_inv (c : Cocycle G A) (g : G) : c.val g⁻¹ = -(g⁻¹ • c.val g) := by
  apply eq_neg_of_add_eq_zero_left
  have h := (_root_.GroupCohomology.ContinuousH1.Cocycle.map_mul c g⁻¹ g).symm
  simpa using h

/-- Inner conjugacy changes a continuous cocycle by this explicit coboundary. -/
theorem conjugacyMap_sub (g : G) (c : Cocycle G A) :
    (conjugacyMap G A g).onCocycles c - c =
      principal G A (-(g⁻¹ • c.val g)) := by
  ext h
  change g⁻¹ • c.val (g * h * g⁻¹) - c.val h =
    h • (-(g⁻¹ • c.val g)) - (-(g⁻¹ • c.val g))
  rw [_root_.GroupCohomology.ContinuousH1.Cocycle.map_mul,
    _root_.GroupCohomology.ContinuousH1.Cocycle.map_mul, cocycle_inv]
  simp only [smul_add, smul_neg, ← mul_smul, mul_assoc, inv_mul_cancel_left,
    inv_mul_cancel, one_smul]
  abel

/-- The class of every continuous cocycle is fixed by the combined conjugacy map. -/
theorem conjugacyMap_classOf (g : G) (c : Cocycle G A) :
    (conjugacyMap G A g).onH1 (classOf G A c) = classOf G A c := by
  rw [_root_.GroupCohomology.ContinuousH1.PullbackMap.onH1_classOf, classOf_eq_iff]
  exact ⟨-(g⁻¹ • c.val g), (conjugacyMap_sub G A g c).symm⟩

/-- The actual continuous first-cohomology map induced by inner conjugacy is
    the identity, with no invariance assumption. -/
@[simp] theorem conjugacyMap_onH1 (g : G) :
    (conjugacyMap G A g).onH1 = AddMonoidHom.id (H1 G A) := by
  apply AddMonoidHom.ext
  intro x
  obtain ⟨c, rfl⟩ := classOf_surjective G A x
  exact conjugacyMap_classOf G A g c

end GroupCohomology.ContinuousH1.InnerConjugacy
