/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.DiagonalProduct
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.Shift
public import Aglib.CategoryTheory.Adjunction.ShiftedHom
public import Mathlib.CategoryTheory.Shift.Adjunction
public import Mathlib.CategoryTheory.Shift.ShiftedHom

/-! The original diagonal identity after normalization of the top trace. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

namespace CategoryTheory.ShiftedHom

variable {C : Type*} [Category* C] [HasShift C ℤ]

/-- A normalized degree-opposite trace cancels the original shifted class in a product. -/
private theorem comp_comp_trace_of_normalized {U V : C} {a b c : ℤ}
    (h : b + a = c)
    (x : ShiftedHom U U a) (z : ShiftedHom U V b) (τ : ShiftedHom V U (-b))
    (hz : z.comp τ (by omega : -b + b = 0) = ShiftedHom.mk₀ 0 rfl (𝟙 U)) :
    (x.comp z h).comp τ (by omega : -b + c = a) = x := by
  rw [ShiftedHom.comp_assoc x z τ h (by omega : -b + b = 0) (by omega), hz]
  exact ShiftedHom.comp_mk₀_id x 0 rfl

end CategoryTheory.ShiftedHom

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Kummer

open Coefficients

universe u wX wZ wU wAZ wAU wDX wDZ wDU

attribute [local instance] hasSheafifyLarge hasSheafifyModules
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

variable {X S : Scheme.{u}} (p : X ⟶ S) [SmoothOfRelativeDimension 1 p] [IsSeparated p]
  (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(pullback p p, ⊤)))
  {U : Scheme.{u}} (j : U ⟶ pullback p p) [IsOpenImmersion j]
  (hj : Set.range j = (Set.range (pullback.diagonal p))ᶜ)
  [HasExt.{wX} (ModuleSheaf X (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wZ} (ModuleSheaf (pullback p p) (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wU} (ModuleSheaf U (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wAZ} (AbelianSheaf.{u, u + 1} (pullback p p))]
  [HasExt.{wAU} (AbelianSheaf.{u, u + 1} U)]
  [HasDerivedCategory.{wDX} (ModuleSheaf X (ULift.{u + 1} (ZMod n)))]
  [HasDerivedCategory.{wDZ} (ModuleSheaf (pullback p p) (ULift.{u + 1} (ZMod n)))]
  [HasDerivedCategory.{wDU} (ModuleSheaf U (ULift.{u + 1} (ZMod n)))]

include hj in
/-- A top trace normalized on the original diagonal class evaluates the original
first-projection product as the class on the base. -/
theorem diagonalModuleKummerClass_trace_of_normalized (r : ℕ)
    (x : constantModuleExt.{u, wX} n X r) :
    let Λ := ULift.{u + 1} (ZMod n)
    let Z := pullback p p
    let π := pullback.snd p p
    let I := (DerivedCategory.Plus.singleFunctor (ModuleSheaf X Λ) 0).obj (moduleUnit X Λ)
    let K := (DerivedCategory.Plus.singleFunctor (ModuleSheaf Z Λ) 0).obj (moduleRootsOfUnity Z n)
    let adj := moduleDerivedAdjunction Λ π
    let e := constantModuleDerivedUnitPullbackIso π n
    let c := diagonalModuleKummerClass p n hn hinv
    ∀ τ : ShiftedHom ((moduleDerivedDirectImage Λ π).obj K) I (-2 : ℤ),
    ((adj.shiftedHomEquiv 2 I K (e.hom ≫ c.homPlus)).comp τ (by omega)) =
        ShiftedHom.mk₀ 0 rfl (𝟙 I) →
      (adj.shiftedHomEquiv ((r + 2 : ℕ) : ℤ) I K
          (e.hom ≫ ((constantModuleExtPullback n (pullback.fst p p) r x).comp c rfl).homPlus)).comp
        τ (by omega) = x.homPlus := by
  dsimp only
  let Λ := ULift.{u + 1} (ZMod n)
  let Z := pullback p p
  let π := pullback.snd p p
  let I := (DerivedCategory.Plus.singleFunctor (ModuleSheaf X Λ) 0).obj (moduleUnit X Λ)
  let K := (DerivedCategory.Plus.singleFunctor (ModuleSheaf Z Λ) 0).obj (moduleRootsOfUnity Z n)
  let adj := moduleDerivedAdjunction Λ π
  let e := constantModuleDerivedUnitPullbackIso π n
  let c := diagonalModuleKummerClass p n hn hinv
  let a := constantModuleExtPullback.{u, wX, wZ} n π r x
  let : adj.CommShift ℤ :=
    Adjunction.rightDerivedFunctorPlus_commShift (moduleInverseImageAdjunction π Λ)
  intro τ hτ
  rw [diagonalModuleKummerClass_projection_comp p n hn hinv j hj r x]
  rw [Ext.homPlus_comp]
  have hx := constantModuleExtPullback_homPlus π n r x
  have h := adj.shiftedHomEquiv_comp_map_of_unitIso e x.homPlus c.homPlus a.homPlus hx
    (by omega : (2 : ℤ) + r = ((r + 2 : ℕ) : ℤ))
  change (adj.shiftedHomEquiv ((r + 2 : ℕ) : ℤ) I K
    (e.hom ≫ a.homPlus.comp c.homPlus (by omega))).comp τ (by omega) = x.homPlus
  rw [h]
  exact ShiftedHom.comp_comp_trace_of_normalized
    (by omega : (2 : ℤ) + r = ((r + 2 : ℕ) : ℤ)) x.homPlus
    (adj.shiftedHomEquiv 2 I K (e.hom ≫ c.homPlus)) τ hτ

end AlgebraicGeometry.Scheme.EtaleCohomology.Kummer
