/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-!
# The original bottom-homology chain inclusion

If a complex is strictly zero below degree `n`, its original term in that
degree identifies with its opcycles. The original homology inclusion
therefore defines a native chain map from its degree-`n` homology single.
Its bottom component and homology normalization retain those original maps.

Only the strict lower bound is required. No upper concentration,
projectivity, flatness, injective resolution or derived category is assumed;
category object and morphism universes remain independent. The actual
positive-twist Cech model uses this inclusion before coefficient tensoring.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace CochainComplex
variable {C : Type u} [Category.{v} C] [Abelian C]
  (K : CochainComplex C ℤ) (n : ℤ) [K.IsStrictlyGE n]

/-- Original homology and the opcycle projection inverse give a bottom chain inclusion. -/
def bottomHomologyInclusion :
    (CochainComplex.singleFunctor C n).obj (K.homology n) ⟶ K := by
  let e := K.pOpcyclesIso (n - 1) n (by simp)
    (by exact (K.isZero_of_isStrictlyGE n (n - 1) (by omega)).eq_of_src _ _)
  refine HomologicalComplex.mkHomFromSingle (K.homologyι n ≫ e.inv) ?_
  intro i hi
  have he : e.inv ≫ K.pOpcycles n = 𝟙 _ := e.inv_hom_id
  rw [← K.p_fromOpcycles n i]
  simp only [Category.assoc]
  rw [← Category.assoc e.inv, he, Category.id_comp, K.homologyι_comp_fromOpcycles]

/-- The bottom component retains the original homology and opcycle morphisms. -/
theorem bottomHomologyInclusion_f :
    (bottomHomologyInclusion K n).f n =
      (singleObjXSelf (.up ℤ) n (K.homology n)).hom ≫ K.homologyι n ≫
        (K.pOpcyclesIso (n - 1) n (by simp)
          (by exact (K.isZero_of_isStrictlyGE n (n - 1) (by omega)).eq_of_src _ _)).inv := by
  simp only [bottomHomologyInclusion, HomologicalComplex.mkHomFromSingle_f]

/-- Original bottom homology identifies the chain inclusion with the identity. -/
@[reassoc]
theorem bottomHomologyInclusion_homology :
    (singleObjHomologySelfIso (.up ℤ) n (K.homology n)).inv ≫
      homologyMap (bottomHomologyInclusion K n) n = 𝟙 _ := by
  apply (cancel_mono (K.homologyι n)).mp
  rw [Category.assoc, HomologicalComplex.homologyι_naturality, ← Category.assoc,
    HomologicalComplex.singleObjHomologySelfIso_inv_homologyι,
    HomologicalComplex.singleObjOpcyclesSelfIso_hom, Category.assoc,
    HomologicalComplex.p_opcyclesMap, ← Category.assoc, bottomHomologyInclusion_f]
  simp only [Category.assoc, Category.id_comp]
  rw [K.pOpcyclesIso_inv_hom_id, Category.comp_id]
  exact (singleObjXSelf (.up ℤ) n (K.homology n)).inv_hom_id_assoc (K.homologyι n)

end CochainComplex
