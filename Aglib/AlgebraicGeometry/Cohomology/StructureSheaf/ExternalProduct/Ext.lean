/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.StructureSheaf.ExternalProduct
public import Aglib.AlgebraicGeometry.Modules.Tensor.External
public import Aglib.Algebra.Homology.DerivedCategory.Ext.Bifunctor

/-!
# The original external cup and the biexact external Ext product

The canonical external-tensor unit comparison identifies both partial
external Ext maps with the original projection pullbacks. The genuine
biexact interchange theorem therefore gives the Koszul commutation law
between these two pullbacks, on the original structure-sheaf cohomology.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian MonoidalCategory
open CartesianMonoidalCategory AlgebraicGeometry AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.Modules

universe u v₁ v₂ w₁ w₂ u₁ u₂

namespace AlgebraicGeometry.Scheme.Cohomology

private def extUnitConj {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasExt.{w₁} C]
    {A B : C} (e : A ≅ B) (n : ℕ) : Ext A A n →+ Ext B B n :=
  ((Ext.mk₀ e.hom).postcomp B (Nat.add_zero n)).comp
    ((Ext.mk₀ e.inv).precomp A (Nat.zero_add n))

private theorem extUnitConj_apply
    {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasExt.{w₁} C]
    {A B : C} (e : A ≅ B) {n : ℕ} (x : Ext A A n) :
    extUnitConj e n x = ((Ext.mk₀ e.inv).comp x (Nat.zero_add n)).comp
      (Ext.mk₀ e.hom) (Nat.add_zero n) := rfl

private theorem extUnitConj_trans
    {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasExt.{w₁} C]
    {A B D : C} (e : A ≅ B) (f : B ≅ D) {n : ℕ} (x : Ext A A n) :
    extUnitConj (e ≪≫ f) n x = extUnitConj f n (extUnitConj e n x) := by
  simp only [extUnitConj_apply, Iso.trans_hom, Iso.trans_inv,
    ← Ext.mk₀_comp_mk₀, Ext.comp_assoc_of_second_deg_zero,
    Ext.comp_assoc_of_third_deg_zero]

private theorem extUnitConj_map_natIso
    {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasExt.{w₁} C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasExt.{w₂} D]
    {F G : C ⥤ D} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (e : F ≅ G) {A : C} {n : ℕ} (x : Ext A A n) :
    extUnitConj (e.app A) n (x.mapExactFunctor F) = x.mapExactFunctor G := by
  rw [extUnitConj_apply, Ext.comp_assoc_of_third_deg_zero]
  change (Ext.mk₀ (e.inv.app A)).comp
    ((x.mapExactFunctor F).comp (Ext.mk₀ (e.hom.app A)) (Nat.add_zero n))
      (Nat.zero_add n) = x.mapExactFunctor G
  rw [Ext.mapExactFunctor_comp_mk₀_natTransApp x e.hom,
    ← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀,
    Iso.inv_hom_id_app, Ext.mk₀_id_comp]

private theorem extUnitConj_comp
    {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasExt.{w₁} C]
    {A B : C} (e : A ≅ B) {p q n : ℕ} (h : p + q = n)
    (x : Ext A A p) (y : Ext A A q) :
    extUnitConj e n (x.comp y h) =
      (extUnitConj e p x).comp (extUnitConj e q y) h := by
  have hcancel : (Ext.mk₀ e.hom).comp
      (((Ext.mk₀ e.inv).comp y (Nat.zero_add q)).comp
        (Ext.mk₀ e.hom) (Nat.add_zero q)) (Nat.zero_add q) =
      y.comp (Ext.mk₀ e.hom) (Nat.add_zero q) := by
    rw [← Ext.comp_assoc_of_third_deg_zero, ← Ext.comp_assoc_of_second_deg_zero,
      Ext.mk₀_comp_mk₀, e.hom_inv_id, Ext.mk₀_id_comp]
  simp only [extUnitConj_apply]
  symm
  rw [Ext.comp_assoc_of_second_deg_zero, hcancel, ← Ext.comp_assoc_of_third_deg_zero]
  exact congrArg (fun z : Ext B A n => z.comp (Ext.mk₀ e.hom) (Nat.add_zero n))
    (Ext.comp_assoc (Ext.mk₀ e.inv) x y (Nat.zero_add p) h (by omega))

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k] (X Y : FScheme k)

/-- The first projection is the first partial external Ext map, through
exactly the canonical external-tensor unit comparison. -/
theorem structureExtLinearEquiv_fst_external (n : ℕ)
    (x : Ext.{u + 1} (C := X.left.Modules) (SheafOfModules.unit X.left.ringCatSheaf)
      (SheafOfModules.unit X.left.ringCatSheaf) n) :
    let e := externalTensorUnitIso X.hom Y.hom
    structureCohomologyPullbackLinear (fst X Y) n (structureExtLinearEquiv X n x) =
      structureExtLinearEquiv (X ⊗ Y) n
        (((Ext.mk₀ e.inv).comp
          (x.mapExactFunctor ((externalTensor X.hom Y.hom).flip.obj
            (SheafOfModules.unit Y.left.ringCatSheaf))) (Nat.zero_add n)).comp
              (Ext.mk₀ e.hom) (Nat.add_zero n)) := by
  let r := externalTensorRightUnitIso X.hom Y.hom
  let a := SheafOfModules.unit X.left.ringCatSheaf
  let b := pullbackUnitIso (fst X Y).left
  have he : externalTensorUnitIso X.hom Y.hom = r.app a ≪≫ b :=
    Iso.ext (externalTensorUnitIso_hom_eq_right X.hom Y.hom)
  have : Flat (fst X Y).left := structureProduct_fst_flat X Y
  rw [structureExtLinearEquiv_pullback_of_flat]
  change structureExtLinearEquiv (X ⊗ Y) n (extUnitConj b n
      (x.mapExactFunctor (Scheme.Modules.pullback (fst X Y).left))) =
    structureExtLinearEquiv (X ⊗ Y) n (extUnitConj (externalTensorUnitIso X.hom Y.hom) n _)
  rw [he, extUnitConj_trans]
  apply congrArg (structureExtLinearEquiv (X ⊗ Y) n)
  exact congrArg (extUnitConj b n) (extUnitConj_map_natIso r x).symm

/-- The second projection uses the same canonical external-tensor unit comparison. -/
theorem structureExtLinearEquiv_snd_external (n : ℕ)
    (y : Ext.{u + 1} (C := Y.left.Modules) (SheafOfModules.unit Y.left.ringCatSheaf)
      (SheafOfModules.unit Y.left.ringCatSheaf) n) :
    let e := externalTensorUnitIso X.hom Y.hom
    structureCohomologyPullbackLinear (snd X Y) n (structureExtLinearEquiv Y n y) =
      structureExtLinearEquiv (X ⊗ Y) n
        (((Ext.mk₀ e.inv).comp
          (y.mapExactFunctor ((externalTensor X.hom Y.hom).obj
            (SheafOfModules.unit X.left.ringCatSheaf))) (Nat.zero_add n)).comp
              (Ext.mk₀ e.hom) (Nat.add_zero n)) := by
  let l := externalTensorLeftUnitIso X.hom Y.hom
  let b := pullbackUnitIso (snd X Y).left
  have : Flat (snd X Y).left := structureProduct_snd_flat X Y
  rw [structureExtLinearEquiv_pullback_of_flat]
  change structureExtLinearEquiv (X ⊗ Y) n (extUnitConj b n
      (y.mapExactFunctor (Scheme.Modules.pullback (snd X Y).left))) =
    structureExtLinearEquiv (X ⊗ Y) n
      (extUnitConj (l.app (SheafOfModules.unit Y.left.ringCatSheaf) ≪≫ b) n _)
  rw [extUnitConj_trans, extUnitConj_map_natIso]
  rfl

/-- The literal pullback-then-cup product is the genuine biexact external Ext
product, through the original unit and cohomology comparisons. -/
theorem structureExternalCup_eq_extBifunctor {p q n : ℕ} (h : p + q = n)
    (x : Ext.{u + 1} (C := X.left.Modules) (SheafOfModules.unit X.left.ringCatSheaf)
      (SheafOfModules.unit X.left.ringCatSheaf) p)
    (y : Ext.{u + 1} (C := Y.left.Modules) (SheafOfModules.unit Y.left.ringCatSheaf)
      (SheafOfModules.unit Y.left.ringCatSheaf) q) :
    let e := externalTensorUnitIso X.hom Y.hom
    structureExternalCup X Y h (structureExtLinearEquiv X p x)
        (structureExtLinearEquiv Y q y) =
      structureExtLinearEquiv (X ⊗ Y) n
        (((Ext.mk₀ e.inv).comp ((externalTensor X.hom Y.hom).extBifunctor x y h)
          (Nat.zero_add n)).comp (Ext.mk₀ e.hom) (Nat.add_zero n)) := by
  rw [structureExternalCup_apply, structureExtLinearEquiv_fst_external,
    structureExtLinearEquiv_snd_external, structureCup_apply,
    LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
  exact congrArg (structureExtLinearEquiv (X ⊗ Y) n)
    (extUnitConj_comp (externalTensorUnitIso X.hom Y.hom) h _ _).symm

/-- Pullbacks from the two factors commute with the actual Koszul sign,
over every field, including characteristic two. -/
theorem structureCup_fst_snd_comm {p q n : ℕ} (h : p + q = n)
    (x : structureCohomology k X p) (y : structureCohomology k Y q) :
    structureCup (X ⊗ Y) h
        (structureCohomologyPullbackLinear (fst X Y) p x)
        (structureCohomologyPullbackLinear (snd X Y) q y) =
      ((-1 : ℤ) ^ (p * q)) • structureCup (X ⊗ Y) ((Nat.add_comm q p).trans h)
        (structureCohomologyPullbackLinear (snd X Y) q y)
        (structureCohomologyPullbackLinear (fst X Y) p x) := by
  obtain ⟨x, rfl⟩ := (structureExtLinearEquiv X p).surjective x
  obtain ⟨y, rfl⟩ := (structureExtLinearEquiv Y q).surjective y
  rw [structureExtLinearEquiv_fst_external, structureExtLinearEquiv_snd_external]
  simp only [structureCup_apply, LinearEquiv.symm_apply_apply]
  let e := externalTensorUnitIso X.hom Y.hom
  change structureExtLinearEquiv (X ⊗ Y) n
      ((extUnitConj e p _).comp (extUnitConj e q _) h) =
    ((-1 : ℤ) ^ (p * q)) • structureExtLinearEquiv (X ⊗ Y) n
      ((extUnitConj e q _).comp (extUnitConj e p _) ((Nat.add_comm q p).trans h))
  rw [← extUnitConj_comp, ← extUnitConj_comp]
  have hc := (externalTensor X.hom Y.hom).extBifunctor_comm x y h
  dsimp only [Functor.extBifunctor] at hc
  rw [hc, map_zsmul, map_zsmul]

end AlgebraicGeometry.Scheme.Cohomology
