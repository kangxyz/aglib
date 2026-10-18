/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-! # The original top-homology chain projection

For a complex that is strictly zero above degree `n`, its actual cycles in
that degree identify with its original term. The original homology quotient
therefore defines a native chain map to the degree-`n` single of its homology.
Its top component and homology normalization retain those original maps.
Only the strict upper bound is required; no lower concentration, resolution,
flatness or derived-category assumption is imposed. Category universes remain
independent.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace CochainComplex
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]
  (K : CochainComplex C ℤ) (n : ℤ) [K.IsStrictlyLE n]

/-- The original cycles and homology quotient give a chain projection onto top homology. -/
def topHomologyProjection :
    K ⟶ (CochainComplex.singleFunctor C n).obj (K.homology n) := by
  let e := K.iCyclesIso n (n + 1) (by simp)
    (by exact (K.isZero_of_isStrictlyLE n (n + 1) (by omega)).eq_of_tgt _ _)
  refine HomologicalComplex.mkHomToSingle (e.inv ≫ K.homologyπ n) ?_
  intro i hi
  have he : K.iCycles n ≫ e.inv = 𝟙 _ := e.hom_inv_id
  rw [← K.toCycles_i i n]
  simp only [Category.assoc]
  rw [← Category.assoc (K.iCycles n), he, Category.id_comp, K.toCycles_comp_homologyπ]

/-- The top component retains the original cycle inclusion inverse and homology quotient. -/
theorem topHomologyProjection_f :
    (topHomologyProjection K n).f n =
      (K.iCyclesIso n (n + 1) (by simp)
        (by exact (K.isZero_of_isStrictlyLE n (n + 1) (by omega)).eq_of_tgt _ _)).inv ≫
        K.homologyπ n ≫ (singleObjXSelf (.up ℤ) n (K.homology n)).inv := by
  simp only [topHomologyProjection, HomologicalComplex.mkHomToSingle_f, Category.assoc]

/-- Original top homology identifies the projection with the identity. -/
@[reassoc]
theorem topHomologyProjection_homology :
    homologyMap (topHomologyProjection K n) n ≫
      (singleObjHomologySelfIso (.up ℤ) n (K.homology n)).hom = 𝟙 _ := by
  apply (cancel_epi (K.homologyπ n)).mp
  rw [← Category.assoc, HomologicalComplex.homologyπ_naturality, Category.assoc,
    HomologicalComplex.homologyπ_singleObjHomologySelfIso_hom,
    HomologicalComplex.singleObjCyclesSelfIso_hom, ← Category.assoc,
    HomologicalComplex.cyclesMap_i, Category.assoc, topHomologyProjection_f]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← Category.assoc, K.iCyclesIso_hom_inv_id, Category.id_comp]

end CochainComplex
