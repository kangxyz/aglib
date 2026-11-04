/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Plus.ExtContraction
public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.AbelKummerProduct
public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.DiagonalTrace
public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.RootsTensorOne

/-! The original relative trace contraction of the original Abel Kummer class. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Kummer

open Coefficients Scheme.OverField Scheme.OverField.Curve
open GroupCohomology.Kummer.CoefficientBaseChange

universe u wX wZ wU wAX wAZ wAU wDX wDZ wDU

attribute [local instance] hasSheafifyLarge hasSheafifyModules
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

variable {k : Type u} [Field k] [IsAlgClosed k] {X : FScheme k} (hX : Curve.Properties X)
  (o : Base k ⟶ X.left) (ho : o ≫ X.hom = 𝟙 (Base k))
  (n : ℕ) (hn : 0 < n) (hu : IsUnit (n : k)) (hi : IsUnit (n : Γ(X.left, ⊤)))

set_option hygiene false in
local notation "Λ" => ULift.{u + 1} (ZMod n)

variable {U : Scheme.{u}} (j : U ⟶ pullback X.hom X.hom) [IsOpenImmersion j]
  (hj : Set.range j = (Set.range (pullback.diagonal X.hom))ᶜ)
  [HasExt.{wX} (ModuleSheaf X.left Λ)]
  [HasExt.{wZ} (ModuleSheaf (pullback X.hom X.hom) Λ)]
  [HasExt.{wU} (ModuleSheaf U Λ)]
  [HasExt.{wAX} (AbelianSheaf.{u, u + 1} X.left)]
  [HasExt.{wAZ} (AbelianSheaf.{u, u + 1} (pullback X.hom X.hom))]
  [HasExt.{wAU} (AbelianSheaf.{u, u + 1} U)]
  [HasDerivedCategory.{wDX} (ModuleSheaf X.left Λ)]
  [HasDerivedCategory.{wDZ} (ModuleSheaf (pullback X.hom X.hom) Λ)]
  [HasDerivedCategory.{wDU} (ModuleSheaf U Λ)]

/-- The original Abel boundary contracted against the original first pullback
and a trace normalized on the original diagonal returns the original class. -/
abbrev abelModuleKummerClassContractedTraceOfNormalized
    (x : constantModuleExt.{u, wX} n X.left 1) :=
  letI : SmoothOfRelativeDimension 1 X.hom := hX.smooth
  letI : IsProper X.hom := hX.proper
  let Z := pullback X.hom X.hom
  let π := pullback.snd X.hom X.hom
  let f := pullback.fst X.hom X.hom
  let I := (DerivedCategory.Plus.singleFunctor (ModuleSheaf X.left Λ) 0).obj (moduleUnit X.left Λ)
  let K := (DerivedCategory.Plus.singleFunctor (ModuleSheaf Z Λ) 0).obj (moduleRootsOfUnity Z n)
  let adj := moduleDerivedAdjunction Λ π
  let e := constantModuleDerivedUnitPullbackIso π n
  let a := constantModuleExtPullback.{u, wX, wZ} n f 1 x
  let b := diagonalModuleKummerClass X.hom n hn (levelInvertible f n hi)
  let c := abelModuleKummerClass X.hom o ho n hn hi
  let r := moduleRootsExtOneTensor n hn hu (f ≫ X.hom) a
  fun (τ : ShiftedHom ((moduleDerivedDirectImage Λ π).obj K) I (-2 : ℤ))
      (hτ : (adj.shiftedHomEquiv 2 I K (e.hom ≫ b.homPlus)).comp τ (by omega) =
        ShiftedHom.mk₀ 0 rfl (𝟙 I)) =>
    adj.ext_contraction_value e.hom a b c r
      (firstPullback_comp_abelModuleKummerClass hX o ho n hn hu hi x)
      (comp_rootsExtTwo_eq_tensor n hn hu (f ≫ X.hom) a c) τ x.homPlus
      (diagonalModuleKummerClass_trace_of_normalized X.hom n hn
        (levelInvertible f n hi) j hj 1 x τ hτ)

end AlgebraicGeometry.Scheme.EtaleCohomology.Kummer
