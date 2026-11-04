/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Ext.CompositeComparison
public import Aglib.Algebra.Homology.DerivedCategory.Ext.ExactFunctorSquare
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kunneth.DerivedPullback
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.DerivedPullback
public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.PointPurity.Finite
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kunneth.ConstantMap

/-! Composition of the original constant module-unit cohomology pullback. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

private theorem prePostcomp_compFunctor
    {A B C : Type*} [Category* A] [Category* B] [Category* C]
    [Abelian A] [Abelian B] [Abelian C] [HasExt A] [HasExt B] [HasExt C]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (G : B ⥤ C) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    {U : A} {V : B} {W : C} (a : V ⟶ F.obj U) (c : F.obj U ⟶ V)
    (b : W ⟶ G.obj V) (d : G.obj V ⟶ W) (p : ℕ) (x : Ext U U p) :
    ((F ⋙ G).extPrecompMap (b ≫ G.map a) U p x).comp
        (Ext.mk₀ (G.map c ≫ d)) (add_zero p) =
      (G.extPrecompMap b V p
        ((F.extPrecompMap a U p x).comp (Ext.mk₀ c) (add_zero p))).comp
          (Ext.mk₀ d) (add_zero p) := by
  rw [F.extPrecompMap_compFunctor G a b U p x]
  simp only [Functor.extPrecompMap_apply, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_mk₀, Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀]

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

universe u wX wY wZ

attribute [local instance] hasSheafifyLarge hasSheafifyModules
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

variable (n : ℕ) {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
  [HasExt.{wX} (ModuleSheaf X (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wY} (ModuleSheaf Y (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wZ} (ModuleSheaf Z (ULift.{u + 1} (ZMod n)))]

/-- Pulling an original constant-unit Ext class back twice is pullback along
the composite, with both original unit identifications. -/
theorem constantModuleExtPullback_comp (p : ℕ) (x : constantModuleExt.{u, wX} n X p) :
    constantModuleExtPullback.{u, wX, wZ} n (g ≫ f) p x =
      constantModuleExtPullback.{u, wY, wZ} n g p
        (constantModuleExtPullback.{u, wX, wY} n f p x) := by
  let Λ := ULift.{u + 1} (ZMod n)
  let U := moduleUnit X Λ
  let F := moduleInverseImage f Λ
  let G := moduleInverseImage g Λ
  let i := moduleUnitInverseImageIso f n
  let j := moduleUnitInverseImageIso g n
  let t := moduleUnitInverseImageIso (g ≫ f) n
  let e := G.mapIso i ≪≫ j
  let α := (moduleInverseImageCompIso Λ f g).hom
  have ht : α.app U ≫ e.hom = t.hom := by
    simp only [e, Iso.trans_hom, Functor.mapIso_hom]
    exact moduleUnitInverseImageIso_comp f g n
  have hs : t.inv ≫ α.app U = e.inv := by
    apply (cancel_mono e.hom).mp
    rw [Category.assoc, ht, t.inv_hom_id, e.inv_hom_id]
  have h₁ := Functor.extPrecompMap_postcomp_eq_of_natTrans α t.inv e.inv t.hom e.hom hs ht p x
  have h₂ := prePostcomp_compFunctor F G i.inv i.hom j.inv j.hom p x
  have hi : e.inv = j.inv ≫ G.map i.inv := rfl
  have hh : e.hom = G.map i.hom ≫ j.hom := rfl
  rw [hi, hh] at h₁
  simp only [constantModuleExtPullback_apply]
  exact (h₁.trans h₂)

end AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

section

open CategoryTheory

namespace CategoryTheory.ShiftedHom

variable {D : Type*} [Category* D] [HasShift D ℤ]

/-- Transporting the original middle object on both sides preserves the
original ordered shifted composition. -/
private theorem comp_of_iso_transports
    {A B C A' B' C' : D} (a : A ≅ A') (b : B ≅ B') (c : C ≅ C')
    {p q d : ℤ} (x : ShiftedHom A B p) (y : ShiftedHom B C q) (h : q + p = d) :
    ShiftedHom.comp (a.inv ≫ x ≫ b.hom⟦p⟧' : ShiftedHom A' B' p)
        (b.inv ≫ y ≫ c.hom⟦q⟧' : ShiftedHom B' C' q) h =
      a.inv ≫ x.comp y h ≫ c.hom⟦d⟧' := by
  let H := shiftFunctor D p
  let T := shiftFunctorAdd' D q p d h
  have hn : H.map (c.hom⟦q⟧') ≫ T.inv.app C' =
      T.inv.app C ≫ c.hom⟦d⟧' := T.inv.naturality c.hom
  simp only [ShiftedHom.comp, Functor.map_comp, Category.assoc]
  change a.inv ≫ x ≫ H.map b.hom ≫ H.map b.inv ≫ H.map y ≫
    H.map (c.hom⟦q⟧') ≫ T.inv.app C' =
      a.inv ≫ x ≫ H.map y ≫ T.inv.app C ≫ c.hom⟦d⟧'
  rw [← H.map_comp_assoc b.hom b.inv, b.hom_inv_id, H.map_id, Category.id_comp, hn]

end CategoryTheory.ShiftedHom

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Kummer

open CategoryTheory CategoryTheory.Abelian Coefficients

universe u wX wU wDX wDU

attribute [local instance] hasSheafifyLarge hasSheafifyModules
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

variable {X U : Scheme.{u}} (f : U ⟶ X) (n : ℕ) (hn : 0 < n)
  (hi : IsUnit (n : Γ(X, ⊤)))
  [HasDerivedCategory.{wDX} (ModuleSheaf X (ULift.{u + 1} (ZMod n)))]
  [HasDerivedCategory.{wDU} (ModuleSheaf U (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wX} (ModuleSheaf X (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wU} (ModuleSheaf U (ULift.{u + 1} (ZMod n)))]

/-- Original coefficient pullback preserves the ordered Yoneda composition
of a constant-unit class and a roots class. -/
theorem moduleRootsUnitExtPullback_comp_constant
    (p q d : ℕ) (h : p + q = d) (x : constantModuleExt.{u, wX} n X p)
    (y : Ext.{wX} (moduleUnit X (ULift.{u + 1} (ZMod n))) (moduleRootsOfUnity X n) q) :
    moduleRootsUnitExtPullback.{u, wX, wU} f n hn hi d (x.comp y h) =
      (constantModuleExtPullback.{u, wX, wU} n f p x).comp
        (moduleRootsUnitExtPullback.{u, wX, wU} f n hn hi q y) h := by
  apply (Ext.homPlusAddEquiv (X := moduleUnit U (ULift.{u + 1} (ZMod n)))
    (Y := moduleRootsOfUnity U n) d).injective
  change (moduleRootsUnitExtPullback f n hn hi d (x.comp y h)).homPlus =
    ((constantModuleExtPullback n f p x).comp (moduleRootsUnitExtPullback f n hn hi q y) h).homPlus
  rw [moduleRootsUnitExtPullback_homPlus, Ext.homPlus_comp, Ext.homPlus_comp,
    ShiftedHom.map_comp, constantModuleExtPullback_homPlus_singleTransport,
    moduleRootsUnitExtPullback_homPlus]
  let Λ := ULift.{u + 1} (ZMod n)
  let F := moduleDerivedInverseImage Λ f
  let a := (moduleInverseImage f Λ).rightDerivedFunctorPlusSingleIsoOfIso 0
    (moduleUnitInverseImageIso f n)
  let b := moduleRootsDerivedSinglePullbackIso f n hn hi
  exact (ShiftedHom.comp_of_iso_transports a a b (x.homPlus.map F) (y.homPlus.map F)
    (by omega : (q : ℤ) + (p : ℤ) = (d : ℤ))).symm

end AlgebraicGeometry.Scheme.EtaleCohomology.Kummer

end
