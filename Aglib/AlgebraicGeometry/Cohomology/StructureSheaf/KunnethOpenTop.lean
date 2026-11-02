/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.StructureSheaf.KunnethOpen

/-!
# The whole-space mixed map is the original global Künneth map

Both source and target comparisons are the original native H'-top maps.
The actual top-open source/unit triangle identifies every bidegree before
taking the original finite antidiagonal. No affine hypothesis or change of
ambient scheme enters this identification.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.OverField AlgebraicGeometry.Scheme.Modules
open scoped TensorProduct DirectSum

universe u v w

namespace CategoryTheory.Abelian.Ext

private theorem unit_source_conjugation {C : Type u} [Category.{v} C] [Abelian C]
    [HasExt.{w} C] {A B U : C} (e : A ≅ B) (a : U ⟶ A) (b : U ⟶ B)
    (hab : a ≫ e.hom = b) {n : ℕ} (z : Ext A A n) :
    ((Ext.mk₀ a).comp z (Nat.zero_add n)).comp (Ext.mk₀ e.hom) (Nat.add_zero n) =
      (Ext.mk₀ b).comp
        (((Ext.mk₀ e.inv).comp z (Nat.zero_add n)).comp
          (Ext.mk₀ e.hom) (Nat.add_zero n)) (Nat.zero_add n) := by
  have hba : b ≫ e.inv = a := by
    rw [← hab, Category.assoc, e.hom_inv_id, Category.comp_id]
  rw [← Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀_assoc, hba]

end CategoryTheory.Abelian.Ext

namespace AlgebraicGeometry.Scheme.Cohomology

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k]

/-- The original native whole-space comparison with the unchanged structural action. -/
def structureOpenTopLinearEquiv (T : FScheme k) (n : ℕ) :
    structureOpenCohomology T ⊤ n ≃ₗ[k] structureCohomology k T n :=
  (moduleHPrimeTopLinearEquivOfHom T.left (constants T)
    (SheafOfModules.unit T.left.ringCatSheaf) n).trans (structureModuleCohomologyEquiv T n)

/-- The top comparison retains the original source map on one, in every degree. -/
theorem structureOpenTopLinearEquiv_ext (T : FScheme k) (n : ℕ)
    (x : Ext.{u + 1} (C := T.left.Modules) (SheafOfModules.unit T.left.ringCatSheaf)
      (SheafOfModules.unit T.left.ringCatSheaf) n) :
    structureOpenTopLinearEquiv T n
        (structureOpenExtLinearEquiv T ⊤ n
          ((Ext.mk₀ (moduleOpenTopUnitMap T.left)).comp x (Nat.zero_add n))) =
      structureExtLinearEquiv T n x := by
  exact moduleOpenExtCohomologyMap_top T.left (SheafOfModules.unit T.left.ringCatSheaf) n x

variable (X Y : FScheme k)

private theorem structureExternalOpenExt_top (p q n : ℕ) (h : p + q = n)
    (x : Ext.{u + 1} (C := X.left.Modules) (SheafOfModules.unit X.left.ringCatSheaf)
      (SheafOfModules.unit X.left.ringCatSheaf) p)
    (y : Ext.{u + 1} (C := Y.left.Modules) (SheafOfModules.unit Y.left.ringCatSheaf)
      (SheafOfModules.unit Y.left.ringCatSheaf) q) :
    let e := externalTensorUnitIso X.hom Y.hom
    structureExternalOpenExt X Y ⊤ h x
        ((Ext.mk₀ (moduleOpenTopUnitMap Y.left)).comp y (Nat.zero_add q)) =
      (Ext.mk₀ (moduleOpenTopUnitMap (X ⊗ Y).left)).comp
        (((Ext.mk₀ e.inv).comp ((externalTensor X.hom Y.hom).extBifunctor x y h)
          (Nat.zero_add n)).comp (Ext.mk₀ e.hom) (Nat.add_zero n)) (Nat.zero_add n) := by
  let F : X.left.Modules ⥤ Y.left.Modules ⥤ (X ⊗ Y).left.Modules :=
    externalTensor X.hom Y.hom
  let : F.Additive := externalTensor_additive X.hom Y.hom
  let (M : X.left.Modules) : (F.obj M).Additive :=
    externalTensor_obj_additive X.hom Y.hom M
  let (N : Y.left.Modules) : (F.flip.obj N).Additive :=
    externalTensor_flip_obj_additive X.hom Y.hom N
  let (M : X.left.Modules) : PreservesFiniteLimits (F.obj M) :=
    externalTensor_obj_preservesFiniteLimits X.hom Y.hom M
  let (M : X.left.Modules) : PreservesFiniteColimits (F.obj M) :=
    externalTensor_obj_preservesFiniteColimits X.hom Y.hom M
  let (N : Y.left.Modules) : PreservesFiniteLimits (F.flip.obj N) :=
    externalTensor_flip_obj_preservesFiniteLimits X.hom Y.hom N
  let (N : Y.left.Modules) : PreservesFiniteColimits (F.flip.obj N) :=
    externalTensor_flip_obj_preservesFiniteColimits X.hom Y.hom N
  let A := (F.obj (SheafOfModules.unit X.left.ringCatSheaf)).obj
    (SheafOfModules.unit Y.left.ringCatSheaf)
  let A' := (F.obj (SheafOfModules.unit X.left.ringCatSheaf)).obj (openFree Y.left ⊤)
  let s := ((structureExternalOpenSourceIso X Y).app ⊤).inv
  let e : A ≅ SheafOfModules.unit (X ⊗ Y).left.ringCatSheaf :=
    externalTensorUnitIso X.hom Y.hom
  let tY := moduleOpenTopUnitMap Y.left
  let tZ := moduleOpenTopUnitMap (X ⊗ Y).left
  let a := s ≫ (F.obj (SheafOfModules.unit X.left.ringCatSheaf)).map tY
  have hab : a ≫ e.hom = tZ := by
    simpa only [a, Category.assoc] using structureExternalOpenSourceIso_top_unit X Y
  have hStart := F.extBifunctorWithMaps_apply s e.hom h x
    ((Ext.mk₀ tY).comp y (Nat.zero_add q))
  have hBif := F.extBifunctor_mk₀_comp_right tY x y h
  have hMap := congrArg
    (fun z : Ext.{u + 1} (C := (X ⊗ Y).left.Modules) A' A n =>
      ((Ext.mk₀ s).comp z (Nat.zero_add n)).comp (Ext.mk₀ e.hom) (Nat.add_zero n)) hBif
  have hAssoc := Ext.mk₀_comp_mk₀_assoc s
    ((F.obj (SheafOfModules.unit X.left.ringCatSheaf)).map tY) (F.extBifunctor x y h)
  have hAssocMap := congrArg
    (fun z : Ext.{u + 1} (C := (X ⊗ Y).left.Modules)
        (openFree (X ⊗ Y).left ⊤) A n => z.comp (Ext.mk₀ e.hom) (Nat.add_zero n)) hAssoc
  have hUnit := Ext.unit_source_conjugation e a tZ hab (F.extBifunctor x y h)
  have hFinal := hStart.trans (hMap.trans (hAssocMap.trans hUnit))
  exact hFinal

/-- Every original pair of unit Ext classes has the literal global external-cup value. -/
private theorem structureExternalOpenCup_top_ext (p q n : ℕ) (h : p + q = n)
    (x : Ext.{u + 1} (C := X.left.Modules) (SheafOfModules.unit X.left.ringCatSheaf)
      (SheafOfModules.unit X.left.ringCatSheaf) p)
    (y : Ext.{u + 1} (C := Y.left.Modules) (SheafOfModules.unit Y.left.ringCatSheaf)
      (SheafOfModules.unit Y.left.ringCatSheaf) q) :
    structureOpenTopLinearEquiv (X ⊗ Y) n
        (structureExternalOpenCup X Y ⊤ h (structureExtLinearEquiv X p x)
          (structureOpenExtLinearEquiv Y ⊤ q
            ((Ext.mk₀ (moduleOpenTopUnitMap Y.left)).comp y (Nat.zero_add q)))) =
      structureExternalCup X Y h (structureExtLinearEquiv X p x)
        (structureExtLinearEquiv Y q y) := by
  let e := externalTensorUnitIso X.hom Y.hom
  let z := ((Ext.mk₀ e.inv).comp ((externalTensor X.hom Y.hom).extBifunctor x y h)
    (Nat.zero_add n)).comp (Ext.mk₀ e.hom) (Nat.add_zero n)
  have hCup := structureExternalOpenCup_apply X Y ⊤ h (structureExtLinearEquiv X p x)
    (structureOpenExtLinearEquiv Y ⊤ q
      ((Ext.mk₀ (moduleOpenTopUnitMap Y.left)).comp y (Nat.zero_add q)))
  simp only [LinearEquiv.symm_apply_apply] at hCup
  have hLeft := congrArg (structureOpenTopLinearEquiv (X ⊗ Y) n) hCup
  have hRaw := structureExternalOpenExt_top X Y p q n h x y
  have hMiddle := congrArg
    (fun a => structureOpenTopLinearEquiv (X ⊗ Y) n
      (moduleOpenExtCohomologyMap (X ⊗ Y).left ⊤
        (SheafOfModules.unit (X ⊗ Y).left.ringCatSheaf) n a)) hRaw
  have hTop := structureOpenTopLinearEquiv_ext (X ⊗ Y) n z
  have hGlobal := structureExternalCup_eq_extBifunctor X Y h x y
  have hFinal := hLeft.trans (hMiddle.trans hTop)
  exact hFinal.trans hGlobal.symm

/-- The whole-space mixed cup is the original external cup under the original top maps. -/
theorem structureExternalOpenCup_top {p q n : ℕ} (h : p + q = n)
    (x : structureCohomology k X p) (y : structureOpenCohomology Y ⊤ q) :
    structureOpenTopLinearEquiv (X ⊗ Y) n (structureExternalOpenCup X Y ⊤ h x y) =
      structureExternalCup X Y h x (structureOpenTopLinearEquiv Y q y) := by
  let xE := (structureExtLinearEquiv X p).symm x
  let yE := (structureExtLinearEquiv Y q).symm (structureOpenTopLinearEquiv Y q y)
  have hx : structureExtLinearEquiv X p xE = x := LinearEquiv.apply_symm_apply _ _
  have hy : structureExtLinearEquiv Y q yE = structureOpenTopLinearEquiv Y q y :=
    LinearEquiv.apply_symm_apply _ _
  have hTop := structureOpenTopLinearEquiv_ext Y q yE
  have hy' : structureOpenExtLinearEquiv Y ⊤ q
      ((Ext.mk₀ (moduleOpenTopUnitMap Y.left)).comp yE (Nat.zero_add q)) = y := by
    apply (structureOpenTopLinearEquiv Y q).injective
    exact hTop.trans hy
  have hFinal := structureExternalOpenCup_top_ext X Y p q n h xE yE
  rw [hx, hy', hy] at hFinal
  exact hFinal

/-- Whole homogeneous tensor correspondence at the original top open. -/
theorem structureExternalOpenTensor_top {p q n : ℕ} (h : p + q = n) :
    (structureOpenTopLinearEquiv (X ⊗ Y) n).toLinearMap ∘ₗ
        structureExternalOpenTensor X Y ⊤ h =
      structureExternalTensor X Y h ∘ₗ
        TensorProduct.map LinearMap.id (structureOpenTopLinearEquiv Y q).toLinearMap := by
  apply TensorProduct.ext'
  intro x y
  simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply,
    structureExternalTensor_tmul]
  exact structureExternalOpenCup_top X Y h x y

/-- The canonical whole-space source comparison retains each original antidiagonal summand. -/
def structureOpenTopSourceEquiv (n : ℕ) : structureOpenKunnethSum X Y ⊤ n ≃ₗ[k]
    structureKunnethSum X Y n :=
  DirectSum.congrLinearEquiv (fun s : HomologicalComplex₂.TotalDegree n =>
    TensorProduct.congr (LinearEquiv.refl k (structureCohomology k X s.val.1))
      (structureOpenTopLinearEquiv Y s.val.2))

/-- The whole original global kappa is exactly the mixed TOP map under canonical top comparisons. -/
theorem structureOpenKunnethMap_top (n : ℕ) :
    (structureOpenTopLinearEquiv (X ⊗ Y) n).toLinearMap ∘ₗ structureOpenKunnethMap X Y ⊤ n =
      structureKunnethMap X Y n ∘ₗ (structureOpenTopSourceEquiv X Y n).toLinearMap := by
  apply DirectSum.linearMap_ext
  intro s
  apply LinearMap.ext
  intro z
  have hTensor := LinearMap.congr_fun (structureExternalOpenTensor_top X Y s.property) z
  have hOpen := structureOpenKunnethMap_lof X Y ⊤ n s z
  have hOpenMap := congrArg (structureOpenTopLinearEquiv (X ⊗ Y) n) hOpen
  have hFinal := hOpenMap.trans hTensor
  simp only [LinearMap.comp_apply, structureOpenTopSourceEquiv,
    DirectSum.congrLinearEquiv_toLinearMap, DirectSum.lmap_lof,
    structureKunnethMap_lof, TensorProduct.toLinearMap_congr,
    LinearEquiv.refl_toLinearMap] at hFinal ⊢
  exact hFinal

/-- Bijectivity of the actual mixed top map discharges the actual original global map. -/
theorem structureKunnethMap_bijective_of_openTop (n : ℕ)
    (h : Function.Bijective (structureOpenKunnethMap X Y ⊤ n)) :
    Function.Bijective (structureKunnethMap X Y n) := by
  apply (Function.Bijective.of_comp_iff (structureKunnethMap X Y n)
    (structureOpenTopSourceEquiv X Y n).bijective).mp
  change Function.Bijective
    (structureKunnethMap X Y n ∘ₗ (structureOpenTopSourceEquiv X Y n).toLinearMap)
  rw [← structureOpenKunnethMap_top]
  exact (structureOpenTopLinearEquiv (X ⊗ Y) n).bijective.comp h

end AlgebraicGeometry.Scheme.Cohomology
