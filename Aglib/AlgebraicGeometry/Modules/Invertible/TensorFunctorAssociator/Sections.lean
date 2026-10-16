/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.TensorFunctorAssociator
public import Aglib.AlgebraicGeometry.Modules.Tensor.Sections
public import Aglib.Algebra.Category.ModuleCat.Sheaf.Tensor.RightUnit

/-!
# Original pure sections of line-tensor associators and units

The original module-sheafification unit determines the pure-section
formulas for the installed tensor units and line-tensor associator.
All comparisons retain their actual maps; no new tensor or associator is
constructed. The coefficient module is arbitrary.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  AlgebraicGeometry Opposite SheafOfModulesOfCommRing
open scoped TensorProduct

universe u v

namespace AlgebraicGeometry.Scheme.Modules

private theorem associatedSheaf_map_unit_apply (X : Scheme.{u})
    {P Q : PresheafOfModulesOfCommRing.{u} X.sheaf.obj} (f : P ⟶ Q)
    (U : X.Opens) (x : P.obj (op U)) :
    ((associatedSheaf X.sheaf).map f).val.app (op U)
        (((associatedSheafUnit X.sheaf).app P).app (op U) x) =
      ((associatedSheafUnit X.sheaf).app Q).app (op U) (f.app (op U) x) := by
  have h := (associatedSheafUnit X.sheaf).naturality f
  exact (congrArg (fun q => q.app (op U) x) h).symm

/-- The original right tensor unitor sends its original pure section to scalar multiplication. -/
theorem tensorRightUnitIso_hom_section (X : Scheme.{u}) (M : X.Modules) (U : X.Opens)
    (m : Γ(M, U)) (a : Γ(X, U)) :
    ((tensorRightUnitIso X.sheaf).hom.app M).val.app (op U)
        (moduleTensorSection X M (SheafOfModules.unit X.ringCatSheaf) U m a) = a • m := by
  let P := (SheafOfModulesOfCommRing.toPresheaf X.sheaf).obj M
  let adj := PresheafOfModules.sheafificationAdjunction (R := X.ringCatSheaf) (𝟙 _)
  have hunit : (associatedSheafUnit X.sheaf).app P ≫
      (SheafOfModulesOfCommRing.toPresheaf X.sheaf).map (adj.counit.app M) = 𝟙 P := by
    exact adj.right_triangle_components M
  have hn := (associatedSheafUnit X.sheaf).naturality (ρ_ P).hom
  have hfac : (associatedSheafUnit X.sheaf).app (P ⊗ 𝟙_ _) ≫
      (SheafOfModulesOfCommRing.toPresheaf X.sheaf).map
        ((tensorRightUnitIso X.sheaf).hom.app M) = (ρ_ P).hom := by
    erw [tensorRightUnitIso_hom_app X.sheaf M, Functor.map_comp, ← Category.assoc, ← hn,
      Category.assoc, hunit, Category.comp_id]
    rfl
  have hv := congrArg (fun q => q.app (op U) (m ⊗ₜ[Γ(X, U)] a)) hfac
  change ((tensorRightUnitIso X.sheaf).hom.app M).val.app (op U)
      (moduleTensorSection X M (SheafOfModules.unit X.ringCatSheaf) U m a) =
    (ρ_ P).hom.app (op U) (m ⊗ₜ[Γ(X, U)] a) at hv
  have hρ : (ρ_ P).hom.app (op U) (m ⊗ₜ[Γ(X, U)] a) = a • m := by
    let : CommRing (X.ringCatSheaf.obj.obj (op U)) := inferInstanceAs (CommRing Γ(X, U))
    exact ModuleCat.MonoidalCategory.rightUnitor_hom_apply m a
  exact hv.trans hρ

/-- The original left tensor unitor sends its original pure section to scalar multiplication. -/
theorem tensorLeftUnitIso_hom_section (X : Scheme.{u}) (M : X.Modules) (U : X.Opens)
    (a : Γ(X, U)) (m : Γ(M, U)) :
    ((tensorLeftUnitIso X.sheaf).hom.app M).val.app (op U)
        (moduleTensorSection X (SheafOfModules.unit X.ringCatSheaf) M U a m) = a • m := by
  let P := (SheafOfModulesOfCommRing.toPresheaf X.sheaf).obj M
  let adj := PresheafOfModules.sheafificationAdjunction (R := X.ringCatSheaf) (𝟙 _)
  have hunit : (associatedSheafUnit X.sheaf).app P ≫
      (SheafOfModulesOfCommRing.toPresheaf X.sheaf).map (adj.counit.app M) = 𝟙 P := by
    exact adj.right_triangle_components M
  have hn := (associatedSheafUnit X.sheaf).naturality (λ_ P).hom
  have hfac : (associatedSheafUnit X.sheaf).app (𝟙_ _ ⊗ P) ≫
      (SheafOfModulesOfCommRing.toPresheaf X.sheaf).map
        ((tensorLeftUnitIso X.sheaf).hom.app M) = (λ_ P).hom := by
    erw [tensorLeftUnitIso_hom_app X.sheaf M, Functor.map_comp, ← Category.assoc, ← hn,
      Category.assoc, hunit, Category.comp_id]
    rfl
  have hv := congrArg (fun q => q.app (op U) (a ⊗ₜ[Γ(X, U)] m)) hfac
  change ((tensorLeftUnitIso X.sheaf).hom.app M).val.app (op U)
      (moduleTensorSection X (SheafOfModules.unit X.ringCatSheaf) M U a m) =
    (λ_ P).hom.app (op U) (a ⊗ₜ[Γ(X, U)] m) at hv
  have hleft : (λ_ P).hom.app (op U) (a ⊗ₜ[Γ(X, U)] m) = a • m := by
    let : CommRing (X.ringCatSheaf.obj.obj (op U)) := inferInstanceAs (CommRing Γ(X, U))
    exact ModuleCat.MonoidalCategory.leftUnitor_hom_apply a m
  exact hv.trans hleft

private theorem lineTensorLeftUnitComparison_section {X : Scheme.{u}} (L M N : X.Modules)
    (U : X.Opens) (l : Γ(L, U)) (m : Γ(M, U)) (n : Γ(N, U)) :
    ((lineTensorLeftUnitComparison X L M).app N).val.app (op U)
        (((associatedSheafUnit X.sheaf).app
          ((SheafOfModulesOfCommRing.toPresheaf X.sheaf).obj L ⊗
            ((SheafOfModulesOfCommRing.toPresheaf X.sheaf).obj M ⊗
              (SheafOfModulesOfCommRing.toPresheaf X.sheaf).obj N))).app (op U)
                (l ⊗ₜ[Γ(X, U)] (m ⊗ₜ[Γ(X, U)] n))) =
      moduleTensorSection X L ((moduleTensorLeftFunctor X M).obj N) U l
        (moduleTensorSection X M N U m n) := by
  let A := (SheafOfModulesOfCommRing.toPresheaf X.sheaf).obj L
  let B := (SheafOfModulesOfCommRing.toPresheaf X.sheaf).obj M
  let C := (SheafOfModulesOfCommRing.toPresheaf X.sheaf).obj N
  let η := associatedSheafUnit X.sheaf
  change ((associatedSheaf X.sheaf).map (𝟙 A ⊗ₘ η.app (B ⊗ C))).val.app (op U)
      ((η.app (A ⊗ (B ⊗ C))).app (op U) (l ⊗ₜ[Γ(X, U)] (m ⊗ₜ[Γ(X, U)] n))) = _
  erw [associatedSheaf_map_unit_apply X (𝟙 A ⊗ₘ η.app (B ⊗ C)) U
    (l ⊗ₜ[Γ(X, U)] (m ⊗ₜ[Γ(X, U)] n))]
  rfl

private theorem lineTensorRightUnitComparison_section {X : Scheme.{u}} (L M N : X.Modules)
    (U : X.Opens) (l : Γ(L, U)) (m : Γ(M, U)) (n : Γ(N, U)) :
    ((lineTensorRightUnitComparison X L M).app N).val.app (op U)
        (((associatedSheafUnit X.sheaf).app
          (((SheafOfModulesOfCommRing.toPresheaf X.sheaf).obj L ⊗
            (SheafOfModulesOfCommRing.toPresheaf X.sheaf).obj M) ⊗
              (SheafOfModulesOfCommRing.toPresheaf X.sheaf).obj N)).app (op U)
                ((l ⊗ₜ[Γ(X, U)] m) ⊗ₜ[Γ(X, U)] n)) =
      moduleTensorSection X ((moduleTensorLeftFunctor X L).obj M) N U
        (moduleTensorSection X L M U l m) n := by
  let A := (SheafOfModulesOfCommRing.toPresheaf X.sheaf).obj L
  let B := (SheafOfModulesOfCommRing.toPresheaf X.sheaf).obj M
  let C := (SheafOfModulesOfCommRing.toPresheaf X.sheaf).obj N
  let η := associatedSheafUnit X.sheaf
  change ((associatedSheaf X.sheaf).map (η.app (A ⊗ B) ⊗ₘ 𝟙 C)).val.app (op U)
      ((η.app ((A ⊗ B) ⊗ C)).app (op U) ((l ⊗ₜ[Γ(X, U)] m) ⊗ₜ[Γ(X, U)] n)) = _
  erw [associatedSheaf_map_unit_apply X (η.app (A ⊗ B) ⊗ₘ 𝟙 C) U
    ((l ⊗ₜ[Γ(X, U)] m) ⊗ₜ[Γ(X, U)] n)]
  rfl

private theorem lineTensorPresheafAssociator_inv_section
    {X : Scheme.{u}} (L M N : X.Modules)
    (U : X.Opens) (l : Γ(L, U)) (m : Γ(M, U)) (n : Γ(N, U)) :
    ((lineTensorPresheafAssociator X L M).inv.app N).val.app (op U)
        (((associatedSheafUnit X.sheaf).app
          ((SheafOfModulesOfCommRing.toPresheaf X.sheaf).obj L ⊗
            ((SheafOfModulesOfCommRing.toPresheaf X.sheaf).obj M ⊗
              (SheafOfModulesOfCommRing.toPresheaf X.sheaf).obj N))).app (op U)
                (l ⊗ₜ[Γ(X, U)] (m ⊗ₜ[Γ(X, U)] n))) =
      ((associatedSheafUnit X.sheaf).app
        (((SheafOfModulesOfCommRing.toPresheaf X.sheaf).obj L ⊗
          (SheafOfModulesOfCommRing.toPresheaf X.sheaf).obj M) ⊗
            (SheafOfModulesOfCommRing.toPresheaf X.sheaf).obj N)).app (op U)
              ((l ⊗ₜ[Γ(X, U)] m) ⊗ₜ[Γ(X, U)] n) := by
  let A := (SheafOfModulesOfCommRing.toPresheaf X.sheaf).obj L
  let B := (SheafOfModulesOfCommRing.toPresheaf X.sheaf).obj M
  let C := (SheafOfModulesOfCommRing.toPresheaf X.sheaf).obj N
  let η := associatedSheafUnit X.sheaf
  change ((associatedSheaf X.sheaf).map (α_ A B C).inv).val.app (op U)
      ((η.app (A ⊗ (B ⊗ C))).app (op U) (l ⊗ₜ[Γ(X, U)] (m ⊗ₜ[Γ(X, U)] n))) = _
  rw [associatedSheaf_map_unit_apply]
  rfl

variable {X : Scheme.{u}} (L M : X.Modules)
  {ι : Type v} (Y : ι → Scheme.{u}) (j : ∀ i, Y i ⟶ X)
  [∀ i, IsOpenImmersion (j i)] (hc : ∀ x : X, ∃ i y, j i y = x)
  (eL : ∀ i, L.restrict (j i) ≅ SheafOfModules.unit (Y i).ringCatSheaf)
  (eM : ∀ i, M.restrict (j i) ≅ SheafOfModules.unit (Y i).ringCatSheaf)

private theorem moduleLineTensorAssociator_hom_unit (N : X.Modules) :
    (lineTensorLeftUnitComparison X L M).app N ≫
        (moduleLineTensorAssociator L M Y j hc eL eM).hom.app N =
      (lineTensorPresheafAssociator X L M).inv.app N ≫
        (lineTensorRightUnitComparison X L M).app N := by
  let : IsIso (lineTensorLeftUnitComparison X L M) := by
    apply (NatTrans.isIso_iff_isIso_app _).mpr
    intro E
    exact isIso_line_tensor_sheafificationUnit L Y j hc eL
      ((SheafOfModulesOfCommRing.toPresheaf X.sheaf).obj M ⊗
        (SheafOfModulesOfCommRing.toPresheaf X.sheaf).obj E)
  dsimp only [moduleLineTensorAssociator, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  change (asIso (lineTensorLeftUnitComparison X L M)).hom.app N ≫
      (asIso (lineTensorLeftUnitComparison X L M)).inv.app N ≫
      (lineTensorPresheafAssociator X L M).inv.app N ≫
      (lineTensorRightUnitComparison X L M).app N = _
  rw [Iso.hom_inv_id_app_assoc]

/-- The original line-tensor associator carries nested pure sections to the original
pure section of their tensor. The third coefficient module is arbitrary. -/
theorem moduleLineTensorAssociator_hom_section (N : X.Modules) (U : X.Opens)
    (l : Γ(L, U)) (m : Γ(M, U)) (n : Γ(N, U)) :
    ((moduleLineTensorAssociator L M Y j hc eL eM).hom.app N).val.app (op U)
        (moduleTensorSection X L ((moduleTensorLeftFunctor X M).obj N) U l
          (moduleTensorSection X M N U m n)) =
      moduleTensorSection X ((moduleTensorLeftFunctor X L).obj M) N U
        (moduleTensorSection X L M U l m) n := by
  let z := ((associatedSheafUnit X.sheaf).app
    ((SheafOfModulesOfCommRing.toPresheaf X.sheaf).obj L ⊗
      ((SheafOfModulesOfCommRing.toPresheaf X.sheaf).obj M ⊗
        (SheafOfModulesOfCommRing.toPresheaf X.sheaf).obj N))).app (op U)
          (l ⊗ₜ[Γ(X, U)] (m ⊗ₜ[Γ(X, U)] n))
  have h := congrArg (fun f => f.val.app (op U) z)
    (moduleLineTensorAssociator_hom_unit L M Y j hc eL eM N)
  change ((moduleLineTensorAssociator L M Y j hc eL eM).hom.app N).val.app (op U)
      (((lineTensorLeftUnitComparison X L M).app N).val.app (op U) z) =
    ((lineTensorRightUnitComparison X L M).app N).val.app (op U)
      (((lineTensorPresheafAssociator X L M).inv.app N).val.app (op U) z) at h
  dsimp only [z] at h
  rw [lineTensorLeftUnitComparison_section, lineTensorPresheafAssociator_inv_section,
    lineTensorRightUnitComparison_section] at h
  exact h

/-- The inverse original associator carries an original pure tensor of two pure factors
back to the original nested pure section. -/
theorem moduleLineTensorAssociator_inv_section (N : X.Modules) (U : X.Opens)
    (l : Γ(L, U)) (m : Γ(M, U)) (n : Γ(N, U)) :
    ((moduleLineTensorAssociator L M Y j hc eL eM).inv.app N).val.app (op U)
        (moduleTensorSection X ((moduleTensorLeftFunctor X L).obj M) N U
          (moduleTensorSection X L M U l m) n) =
      moduleTensorSection X L ((moduleTensorLeftFunctor X M).obj N) U l
        (moduleTensorSection X M N U m n) := by
  let e := moduleLineTensorAssociator L M Y j hc eL eM
  let z := moduleTensorSection X L ((moduleTensorLeftFunctor X M).obj N) U l
    (moduleTensorSection X M N U m n)
  have h := moduleLineTensorAssociator_hom_section L M Y j hc eL eM N U l m n
  have hh := congrArg (fun f => f.val.app (op U) z) (Iso.hom_inv_id_app e N)
  change (e.inv.app N).val.app (op U) ((e.hom.app N).val.app (op U) z) = z at hh
  rw [← h]
  exact hh

end AlgebraicGeometry.Scheme.Modules
