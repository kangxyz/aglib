/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.RootsTensorOnePullback
public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.ConstantCoefficients
public import Aglib.CategoryTheory.Adjunction.ShiftedHom.Contraction
public import Aglib.Algebra.Homology.DerivedCategory.Plus.Postnikov.TraceTransport

/-! The original scalar value of a roots trace contraction. -/

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
@[expose] public noncomputable section

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

open Scheme.OverField

universe u wX wZ dX dZ

attribute [local instance] hasSheafifyLarge hasSheafifyModules
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard moduleSheafExtZModModule

variable {k : Type u} [Field k] [IsAlgClosed k] {X Z : Scheme.{u}}
  (n : ℕ) (hn : 0 < n) (hu : IsUnit (n : k)) (p : X ⟶ Base k) (f π : Z ⟶ X)
  (hi : IsUnit (n : Γ(X, ⊤)))

set_option hygiene false in
local notation "Λ" => ULift.{u + 1} (ZMod n)

variable [HasExt.{wX} (ModuleSheaf X Λ)] [HasExt.{wZ} (ModuleSheaf Z Λ)]
  [HasDerivedCategory.{dX} (ModuleSheaf X Λ)] [HasDerivedCategory.{dZ} (ModuleSheaf Z Λ)]

set_option hygiene false in
local notation "I" => (DerivedCategory.Plus.singleFunctor (ModuleSheaf X Λ) 0).obj (moduleUnit X Λ)
set_option hygiene false in
local notation "M" => (DerivedCategory.Plus.singleFunctor (ModuleSheaf Z Λ) 0).obj
  (moduleRootsOfUnity Z n)
set_option hygiene false in
local notation "R" => moduleDerivedDirectImage Λ π
set_option hygiene false in
local notation "L" => (R).obj M

/-- The scalar value of the original contracted first-pullback roots class. -/
theorem rootsFirstPullback_traceContraction_scalar [NeZero n]
    (u : constantModuleExt.{u, wX} n X 1)
    (v : Ext.{wX} (moduleUnit X Λ) (moduleRootsOfUnity X n) 1)
    (τ : ShiftedHom L I (-2 : ℤ)) (a : L⟦(2 : ℤ)⟧ ⟶ I)
    (hτ : τ = (shiftEquiv' (DerivedCategory.Plus (ModuleSheaf X Λ)) 2 (-2 : ℤ)
      (by omega)).toAdjunction.homEquiv L I a) (s : ZMod n)
    (hs :
      let e := constantModuleDerivedUnitPullbackIso π n
      let w := moduleRootsUnitExtPullback.{u, wX, wZ} f n hn hi 2 (-(u.comp v rfl))
      (moduleDerivedAdjunction Λ π).shiftedHomEquiv 2 I M (e.hom ≫ w.homPlus) ≫ a = s.val • 𝟙 I) :
    let e := constantModuleDerivedUnitPullbackIso π n
    let u₁ := constantModuleExtPullback.{u, wX, wZ} n f 1 u
    let v₁ := moduleRootsUnitExtPullback.{u, wX, wZ} f n hn hi 1 v
    let r : Ext.{wZ} (moduleRootsOfUnity Z n) (moduleRootsOfUnity Z n) 1 :=
      Kummer.moduleRootsExtOneTensor n hn hu (f ≫ p) u₁
    let t : ShiftedHom L I (-1 : ℤ) := (r.homPlus.map R).comp τ
      (by omega : (-2 : ℤ) + 1 = -1)
    ((moduleDerivedAdjunction Λ π).shiftedHomEquiv 1 I M (e.hom ≫ v₁.homPlus)).comp t
      (by omega : (-1 : ℤ) + 1 = 0) = (moduleUnitScalarLinearMap X n s).homPlus := by
  intro e u₁ v₁ r t
  let w := moduleRootsUnitExtPullback.{u, wX, wZ} f n hn hi 2 (-(u.comp v (rfl : 1 + 1 = 2)))
  let adj := moduleDerivedAdjunction Λ π
  let z := adj.shiftedHomEquiv 2 I M (e.hom ≫ w.homPlus)
  let y : Ext.{wX} (moduleUnit X Λ) (moduleUnit X Λ) 0 := moduleUnitScalarLinearMap X n s
  have hw : w.homPlus = v₁.homPlus.comp r.homPlus (by omega : (1 : ℤ) + 1 = 2) :=
    (congrArg (fun a : Ext.{wZ} (moduleUnit Z Λ) (moduleRootsOfUnity Z n) 2 => a.homPlus)
      (Kummer.moduleRootsExtOneTensor_pullback_comp n hn hu p f hi u v).symm).trans
        (Ext.homPlus_comp v₁ r (rfl : 1 + 1 = 2))
  have hcomp : z.comp τ (by omega : (-2 : ℤ) + 2 = 0) = ShiftedHom.mk₀ 0 rfl (z ≫ a) := by
    rw [hτ]
    exact ShiftedHom.comp_shiftAdjunctionHomEquiv 2 z a
  let F := DerivedCategory.Plus.singleFunctor (ModuleSheaf X Λ) 0
  let U := moduleUnit X Λ
  let g := s.val • 𝟙 U
  have hF : F.map g = s.val • 𝟙 I :=
    (F.map_nsmul (f := 𝟙 U) (n := s.val)).trans
      (congrArg (fun f : I ⟶ I => s.val • f) (F.map_id U))
  have hy : y = Ext.mk₀ g := moduleUnitScalarLinearMap_apply_eq_mk₀_nsmul X n s
  have h₀ : y.homPlus = ShiftedHom.mk₀ 0 rfl (s.val • 𝟙 I) :=
    (congrArg (fun z : Ext.{wX} U U 0 => z.homPlus) hy).trans
      ((Ext.homPlus_mk₀ g).trans (congrArg (ShiftedHom.mk₀ 0 rfl) hF))
  have hv := hcomp.trans ((congrArg (ShiftedHom.mk₀ 0 rfl) hs).trans h₀.symm)
  exact adj.shiftedHomEquiv_contraction_value e.hom v₁.homPlus r.homPlus w.homPlus
    (by omega : (1 : ℤ) + 1 = 2) hw τ (by omega : (-2 : ℤ) + 1 = -1)
    (by omega : (-2 : ℤ) + 1 + 1 = 0) y.homPlus hv

end AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
