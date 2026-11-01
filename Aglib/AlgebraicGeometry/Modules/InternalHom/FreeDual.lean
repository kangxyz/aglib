/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.InternalHom.DualFunctor
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products

/-! # The original dual of a finite free module sheaf

The canonical finite product–coproduct comparison identifies the original
contravariant dual of a free sheaf with that same free sheaf. Its coefficients
are precomposition with the original coproduct injections.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules.InternalHom

universe u

open _root_.AlgebraicGeometry.Scheme.Modules.Invertible

attribute [local instance] Abelian.hasFiniteBiproducts

variable (X : Scheme.{u}) (I : Type u) [Finite I]

/-- The canonical coefficient projection of the original finite free sheaf. -/
def freeProjection (i : I) :
    SheafOfModules.free (R := X.ringCatSheaf) I ⟶
      SheafOfModules.unit X.ringCatSheaf :=
  (biproduct.isoCoproduct (fun _ : I => SheafOfModules.unit X.ringCatSheaf)).inv ≫
    biproduct.π _ i

/-- Duality of the original finite free sheaf, without a choice of basis or realization. -/
def dualFreeIso :
    dualSheaf X (SheafOfModules.free (R := X.ringCatSheaf) I) ≅
      SheafOfModules.free (R := X.ringCatSheaf) I :=
  (dualFunctor X).mapIso
      (opCoproductIsoProduct (fun _ : I => SheafOfModules.unit X.ringCatSheaf)) ≪≫
    PreservesProduct.iso (dualFunctor X)
      (fun _ : I => op (SheafOfModules.unit X.ringCatSheaf)) ≪≫
    Pi.mapIso (fun _ : I => unitSourceIso X (SheafOfModules.unit X.ringCatSheaf)) ≪≫
    (biproduct.isoProduct (fun _ : I => SheafOfModules.unit X.ringCatSheaf)).symm ≪≫
    biproduct.isoCoproduct (fun _ : I => SheafOfModules.unit X.ringCatSheaf)

/-- Each coefficient of the canonical dual is precomposition with the original injection. -/
@[reassoc]
theorem dualFreeIso_hom_projection (i : I) :
    (dualFreeIso X I).hom ≫ freeProjection X I i =
      (dualFunctor X).map (SheafOfModules.ιFree (R := X.ringCatSheaf) i).op ≫
        (unitSourceIso X (SheafOfModules.unit X.ringCatSheaf)).hom := by
  simp only [dualFreeIso, freeProjection, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Category.assoc, Iso.hom_inv_id_assoc,
    biproduct.isoProduct_inv, biproduct.lift_π, Pi.mapIso_hom_π,
    PreservesProduct.iso_hom, piComparison_comp_π_assoc]
  rw [← Category.assoc, ← Functor.map_comp,
    opCoproductIsoProduct_hom_comp_π]
  rfl

open Classical in
/-- Original injections and coefficient projections have Kronecker coefficients. -/
@[reassoc]
theorem ιFree_freeProjection (i j : I) :
    SheafOfModules.ιFree (R := X.ringCatSheaf) i ≫ freeProjection X I j =
      if i = j then 𝟙 _ else 0 := by
  classical
  simp only [freeProjection, SheafOfModules.ιFree, biproduct.isoCoproduct_inv,
    ← Category.assoc, Sigma.ι_comp_desc]
  by_cases h : i = j
  · subst j
    simp
  · simp [h]

open Classical in
/-- The inverse sends each original injection to the dual vector with the same coefficients. -/
@[reassoc]
theorem ιFree_dualFreeIso_inv_coefficient (i j : I) :
    SheafOfModules.ιFree (R := X.ringCatSheaf) i ≫ (dualFreeIso X I).inv ≫
      (dualFunctor X).map (SheafOfModules.ιFree (R := X.ringCatSheaf) j).op ≫
        (unitSourceIso X (SheafOfModules.unit X.ringCatSheaf)).hom =
      if i = j then 𝟙 _ else 0 := by
  classical
  rw [← dualFreeIso_hom_projection X I j, Iso.inv_hom_id_assoc]
  exact ιFree_freeProjection X I i j

end AlgebraicGeometry.Scheme.Modules.InternalHom
