/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.PointDivisor.DiagonalFibre
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.BoundaryNaturality
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.CartierBoundary
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.DerivedPullback
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kunneth.DerivedPullback
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kunneth.PullbackComposition
public import Aglib.AlgebraicGeometry.EtaleCohomology.Localization.SupportFactorization

/-! The original positive diagonal class equalizes the two projection pullbacks. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

private theorem map_eq_of_shifted_transport_eq {C D : Type*} [Category* C] [Category* D]
    [HasShift C ℤ] [HasShift D ℤ] (F : C ⥤ D) [F.CommShift ℤ]
    {A B : C} {A' B' : D} (a : F.obj A ≅ A') (b : F.obj B ≅ B')
    {d : ℤ} {x y : ShiftedHom A B d}
    (h : a.inv ≫ x.map F ≫ b.hom⟦d⟧' = a.inv ≫ y.map F ≫ b.hom⟦d⟧') :
    F.map x = F.map y := by
  have h₁ := (cancel_epi a.inv).mp h
  have h₂ := (cancel_mono (b.hom⟦d⟧')).mp h₁
  exact (cancel_mono ((F.commShiftIso d).hom.app B)).mp h₂

private theorem map_eq_zero_of_shifted_transport_zero {C D : Type*}
    [Category* C] [Category* D] [Preadditive C] [Preadditive D]
    [HasShift C ℤ] [HasShift D ℤ] (F : C ⥤ D) [F.CommShift ℤ] [F.Additive]
    {A B : C} {A' B' : D} (a : F.obj A ≅ A') (b : F.obj B ≅ B')
    {d : ℤ} {x : ShiftedHom A B d}
    (h : a.inv ≫ x.map F ≫ b.hom⟦d⟧' = 0) :
    F.map x = 0 := by
  have e := map_eq_of_shifted_transport_eq F a b (x := x) (y := 0)
  simp only [ShiftedHom.map_zero, Functor.map_zero, zero_comp, comp_zero] at e
  exact e h

private theorem map_shift_eq_zero {C D : Type*} [Category* C] [Category* D]
    [Preadditive D] [HasShift C ℤ] [HasShift D ℤ]
    [∀ d : ℤ, (shiftFunctor D d).Additive] (F : C ⥤ D) [F.CommShift ℤ]
    {A B : C} (x : A ⟶ B) (d : ℤ) (h : F.map x = 0) :
    F.map (x⟦d⟧') = 0 := by
  apply (cancel_mono ((F.commShiftIso d).hom.app B)).mp
  rw [F.commShiftIso_hom_naturality, h, Functor.map_zero, comp_zero, zero_comp]

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Kummer

open Coefficients Scheme.Modules.Invertible

universe u wX wZ wU wAZ wAU wDX wDZ wDU

attribute [local instance] hasSheafifyLarge hasSheafifyModules
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

variable {X S : Scheme.{u}} (p : X ⟶ S) [SmoothOfRelativeDimension 1 p] [IsSeparated p]
  (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(pullback p p, ⊤)))
  [HasExt.{wZ} (ModuleSheaf (pullback p p) (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wAZ} (AbelianSheaf.{u, u + 1} (pullback p p))]

/-- The original positive diagonal boundary in the corresponding module-unit Ext. -/
@[no_expose]
def diagonalModuleKummerClass :
    Ext.{wZ} (moduleUnit (pullback p p) (ULift.{u + 1} (ZMod n)))
      (moduleRootsOfUnity (pullback p p) n) 2 :=
  (moduleRootsUnitExtCohomologyAddEquiv.{u, wZ, wAZ} (pullback p p) n 2).symm
    (picardBoundary (pullback p p) n hn hinv
      (-classOf _ (Hom.diagonalIdealLineBundle Hom.smoothRelativeDivisorIdeal p)))

variable {U : Scheme.{u}} (j : U ⟶ pullback p p) [IsOpenImmersion j]
  (hj : Set.range j = (Set.range (pullback.diagonal p))ᶜ)
  [HasExt.{wU} (ModuleSheaf U (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wAU} (AbelianSheaf.{u, u + 1} U)]

include hj in
/-- The original diagonal class vanishes on the complementary open in the native module Ext. -/
theorem diagonalModuleKummerClass_restrict_zero :
    moduleRootsUnitExtPullback.{u, wZ, wU} j n hn hinv 2
      (diagonalModuleKummerClass p n hn hinv) = 0 := by
  apply (moduleRootsUnitExtCohomologyAddEquiv.{u, wU, wAU} U n 2).injective
  rw [map_zero]
  have h := DFunLike.congr_fun
    (moduleRootsUnitExtCohomologyPullback_square.{u, wZ, wU, wAZ, wAU} j n hn hinv 2)
    (diagonalModuleKummerClass p n hn hinv)
  change moduleRootsUnitExtCohomologyAddEquiv.{u, wU, wAU} U n 2
      (moduleRootsUnitExtPullback j n hn hinv 2 (diagonalModuleKummerClass p n hn hinv)) =
    rootsCohomologyPullback j n hn hinv 2
      (moduleRootsUnitExtCohomologyAddEquiv.{u, wZ, wAZ} (pullback p p) n 2
        (diagonalModuleKummerClass p n hn hinv)) at h
  rw [h, diagonalModuleKummerClass, AddEquiv.apply_symm_apply]
  exact diagonalPicardBoundary_restrict_zero p j (by rw [hj]; exact disjoint_compl_right) n hn hinv

variable [HasExt.{wX} (ModuleSheaf X (ULift.{u + 1} (ZMod n)))]
  [HasDerivedCategory.{wDX} (ModuleSheaf X (ULift.{u + 1} (ZMod n)))]
  [HasDerivedCategory.{wDZ} (ModuleSheaf (pullback p p) (ULift.{u + 1} (ZMod n)))]
  [HasDerivedCategory.{wDU} (ModuleSheaf U (ULift.{u + 1} (ZMod n)))]

include hj in
/-- Composing with the original diagonal boundary gives the same Yoneda class after
pullback along either projection. -/
theorem diagonalModuleKummerClass_projection_comp (r : ℕ)
    (x : constantModuleExt.{u, wX} n X r) :
    (constantModuleExtPullback.{u, wX, wZ} n (pullback.fst p p) r x).comp
        (diagonalModuleKummerClass p n hn hinv) (rfl : r + 2 = r + 2) =
      (constantModuleExtPullback.{u, wX, wZ} n (pullback.snd p p) r x).comp
        (diagonalModuleKummerClass p n hn hinv) rfl := by
  let Λ := ULift.{u + 1} (ZMod n)
  let i := pullback.diagonal p
  let a := constantModuleExtPullback.{u, wX, wZ} n (pullback.fst p p) r x
  let b := constantModuleExtPullback.{u, wX, wZ} n (pullback.snd p p) r x
  let c := diagonalModuleKummerClass p n hn hinv
  have he : constantModuleExtPullback.{u, wZ, wX} n i r a =
      constantModuleExtPullback.{u, wZ, wX} n i r b := by
    dsimp only [a, b, i]
    rw [← constantModuleExtPullback_comp n (pullback.fst p p) (pullback.diagonal p),
      ← constantModuleExtPullback_comp n (pullback.snd p p) (pullback.diagonal p),
      pullback.diagonal_fst, pullback.diagonal_snd]
  have ha := constantModuleExtPullback_homPlus i n r a
  have hb := constantModuleExtPullback_homPlus i n r b
  have hab := map_eq_of_shifted_transport_eq (moduleDerivedInverseImage Λ i)
    (constantModuleDerivedUnitPullbackIso i n) (constantModuleDerivedUnitPullbackIso i n)
    (ha.symm.trans ((congrArg (fun z => z.homPlus) he).trans hb))
  let F := moduleDerivedInverseImage Λ j
  let u := (moduleInverseImage j Λ).rightDerivedFunctorPlusSingleIsoOfIso 0
    (moduleUnitInverseImageIso j n)
  let t := moduleRootsDerivedSinglePullbackIso j n hn hinv
  have hc := moduleRootsUnitExtPullback_homPlus j n hn hinv 2 c
  rw [diagonalModuleKummerClass_restrict_zero p n hn hinv j hj,
    ← Ext.homPlusAddEquiv_apply, map_zero] at hc
  have hzero := map_eq_zero_of_shifted_transport_zero F u t hc.symm
  have hcomp := moduleDerived_comp_eq_of_closed_eq_of_open_zero j Λ i hj a.homPlus b.homPlus
    (c.homPlus⟦(r : ℤ)⟧') hab (map_shift_eq_zero F c.homPlus r hzero)
  apply Ext.homPlus_injective
  change (a.comp c rfl).homPlus = (b.comp c rfl).homPlus
  simp only [Ext.homPlus_comp, ShiftedHom.comp]
  simpa only [Category.assoc] using congrArg (fun z => z ≫ _) hcomp

end AlgebraicGeometry.Scheme.EtaleCohomology.Kummer

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Kummer

open Coefficients Scheme.Modules.Invertible Scheme.OverField.Curve.PointDivisor
open GroupCohomology.Kummer.CoefficientBaseChange

universe u wX wZ wAX wAZ

attribute [local instance] hasSheafifyLarge hasSheafifyModules
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

variable {X S : Scheme.{u}} (p : X ⟶ S) [SmoothOfRelativeDimension 1 p] [IsSeparated p]
  (o : S ⟶ X) (ho : o ≫ p = 𝟙 S)
  (n : ℕ) (hn : 0 < n) (hi : IsUnit (n : Γ(pullback p p, ⊤)))
  [HasExt.{wX} (ModuleSheaf X (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wZ} (ModuleSheaf (pullback p p) (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wAX} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{wAZ} (AbelianSheaf.{u, u + 1} (pullback p p))]

/-- The original diagonal Kummer class restricts to the original positive section class. -/
theorem diagonalModuleKummerClass_pullback_sectionFibre :
    let j := diagonalSectionFibreMap p o ho
    moduleRootsUnitExtPullback.{u, wZ, wX} j n hn hi 2
      (diagonalModuleKummerClass p n hn hi) =
      (moduleRootsUnitExtCohomologyAddEquiv.{u, wX, wAX} X n 2).symm
        (picardBoundary X n hn (levelInvertible j n hi)
          (classOf X (positiveSectionLineBundle p o ho))) := by
  intro j
  apply (moduleRootsUnitExtCohomologyAddEquiv.{u, wX, wAX} X n 2).injective
  rw [AddEquiv.apply_symm_apply]
  have h := DFunLike.congr_fun
    (moduleRootsUnitExtCohomologyPullback_square.{u, wZ, wX, wAZ, wAX} j n hn hi 2)
    (diagonalModuleKummerClass p n hn hi)
  change moduleRootsUnitExtCohomologyAddEquiv.{u, wX, wAX} X n 2
      (moduleRootsUnitExtPullback j n hn hi 2 (diagonalModuleKummerClass p n hn hi)) =
    rootsCohomologyPullback j n hn hi 2
      (moduleRootsUnitExtCohomologyAddEquiv.{u, wZ, wAZ} (pullback p p) n 2
        (diagonalModuleKummerClass p n hn hi)) at h
  rw [h, diagonalModuleKummerClass, AddEquiv.apply_symm_apply, picardBoundary_pullback]
  have hp : pullbackClass j
      (-classOf _ (Hom.diagonalIdealLineBundle Hom.smoothRelativeDivisorIdeal p)) =
      classOf X (positiveSectionLineBundle p o ho) := by
    change _ = -classOf X (sectionIdealLineBundle p o ho)
    rw [pullbackClass_neg moduleTensorPullback, diagonalIdealClass_pullback_sectionFibre]
  rw [hp]

end AlgebraicGeometry.Scheme.EtaleCohomology.Kummer

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Kummer

open Coefficients Scheme.Modules.Invertible Scheme.OverField.Curve.PointDivisor
open GroupCohomology.Kummer.CoefficientBaseChange

universe u wX wZ wAX wAZ

attribute [local instance] hasSheafifyLarge hasSheafifyModules
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

variable {X S : Scheme.{u}} (p : X ⟶ S) [SmoothOfRelativeDimension 1 p] [IsSeparated p]
  (o : S ⟶ X) (ho : o ≫ p = 𝟙 S)
  (n : ℕ) (hn : 0 < n) (hi : IsUnit (n : Γ(X, ⊤)))
  [HasExt.{wX} (ModuleSheaf X (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wZ} (ModuleSheaf (pullback p p) (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wAX} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{wAZ} (AbelianSheaf.{u, u + 1} (pullback p p))]

/-- The original Kummer boundary of the original universal Abel bundle. -/
@[no_expose]
def abelModuleKummerClass :
    Ext.{wZ} (moduleUnit (pullback p p) (ULift.{u + 1} (ZMod n)))
      (moduleRootsOfUnity (pullback p p) n) 2 :=
  (moduleRootsUnitExtCohomologyAddEquiv.{u, wZ, wAZ} (pullback p p) n 2).symm
    (picardBoundary (pullback p p) n hn (levelInvertible (pullback.fst p p) n hi)
      (Hom.abelClass Hom.smoothRelativeDivisorIdeal p o ho p (𝟙 X) (Category.id_comp p)))

omit [HasExt.{wX} (ModuleSheaf X (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wAX} (AbelianSheaf.{u, u + 1} X)] in
/-- Scalar forgetting retains the original Kummer boundary of the Abel family. -/
theorem moduleRootsUnitExtCohomologyAddEquiv_abelModuleKummerClass :
    moduleRootsUnitExtCohomologyAddEquiv.{u, wZ, wAZ} (pullback p p) n 2
        (abelModuleKummerClass p o ho n hn hi) =
      picardBoundary (pullback p p) n hn (levelInvertible (pullback.fst p p) n hi)
        (Hom.abelClass Hom.smoothRelativeDivisorIdeal p o ho p (𝟙 X) (Category.id_comp p)) :=
  AddEquiv.apply_symm_apply _ _

/-- The original Abel boundary is the original diagonal boundary minus the
first pullback of the original point boundary. -/
theorem abelModuleKummerClass_eq :
    let z := (moduleRootsUnitExtCohomologyAddEquiv.{u, wX, wAX} X n 2).symm
      (picardBoundary X n hn hi (classOf X (positiveSectionLineBundle p o ho)))
    abelModuleKummerClass p o ho n hn hi =
      diagonalModuleKummerClass p n hn (levelInvertible (pullback.fst p p) n hi) -
        moduleRootsUnitExtPullback.{u, wX, wZ} (pullback.fst p p) n hn hi 2 z := by
  intro z
  let Z := pullback p p
  let f := pullback.fst p p
  let E := moduleRootsUnitExtCohomologyAddEquiv.{u, wZ, wAZ} Z n 2
  let E₀ := moduleRootsUnitExtCohomologyAddEquiv.{u, wX, wAX} X n 2
  have h := DFunLike.congr_fun
    (moduleRootsUnitExtCohomologyPullback_square.{u, wX, wZ, wAX, wAZ} f n hn hi 2) z
  change E (moduleRootsUnitExtPullback f n hn hi 2 z) =
    rootsCohomologyPullback f n hn hi 2 (E₀ z) at h
  have hz : E₀ z = picardBoundary X n hn hi (classOf X (positiveSectionLineBundle p o ho)) :=
    E₀.apply_symm_apply _
  apply E.injective
  rw [map_sub, h, hz, picardBoundary_pullback]
  change E (E.symm _) = E (E.symm _) - _
  simp only [AddEquiv.apply_symm_apply]
  rw [← map_sub, abelClass_identity_eq_diagonal_sub_origin]

end AlgebraicGeometry.Scheme.EtaleCohomology.Kummer
