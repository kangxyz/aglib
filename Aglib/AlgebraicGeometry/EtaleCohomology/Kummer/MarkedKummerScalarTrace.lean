/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.DerivedRestrictionTrace
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.RootsAdjunctTraceUnderlying
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.ModuleCohomologyPostcomp
public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.ConstantCoefficients
public import Aglib.Algebra.Homology.DerivedCategory.Plus.Postnikov.TraceExtZero

/-! Scalar evaluation on the original marked Kummer kernel. -/

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits CategoryTheory.Pretriangulated
open GroupCohomology.Kummer.Coefficients GroupCohomology.Kummer.CoefficientBaseChange

@[expose] public noncomputable section

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Kummer

open DerivedCategory Picard RepresentedKernel Coefficients
open CategoryTheory.Abelian

universe u dX dS dMX dMS w s e v wMX wMS

attribute [local instance] hasSheafifyLarge hasSheafifyModules Over.cartesianMonoidalCategory
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard moduleSheafExtZModModule

variable {X S : Scheme.{u}} (p : X ⟶ S)
  [HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{dS} (AbelianSheaf.{u, u + 1} S)]
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [∀ U : S.Etale, HasExt.{s} (Sheaf ((Scheme.smallEtaleTopology X).over
    ((siteBaseChange p).obj U)) AddCommGrpCat.{u + 1})]
  [∀ U : S.Etale, HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback U.hom p))]
  (o : S ⟶ X) (ho : o ≫ p = 𝟙 S)
  [IsLocallyNoetherian S] [IsProper p] [Flat p] [GeometricallyIntegral p]
  (n : ℕ) (hn : 0 < n) (hi : IsUnit (n : Γ(S, ⊤)))
  {K G : Grp (Over S)} {q : G ⟶ G} [IsCommMonObj K.X] [IsCommMonObj G.X]
  (m : KernelMarking K G G q) (hpow : representedSheafMap q = n • 𝟙 (representedSheaf G))
  (j : representedSheaf G ⟶ normalizedPicardEtaleSheaf p o ho)

set_option hygiene false in
local notation "A" => AbelianSheaf.{u, u + 1} S
set_option hygiene false in
local notation "B" => AbelianSheaf.{u, u + 1} X
set_option hygiene false in
local notation "H₁" => Plus.homologyFunctor A 1
set_option hygiene false in
local notation "F" => Plus.singleFunctor A 0
set_option hygiene false in
local notation "U" => (constantSheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
  (AddCommGrpCat.of (ULift.{u + 1} ℤ))
set_option hygiene false in
local notation "V₁" => Plus.singleFunctorCompHomologyFunctorIso (C := A) 1


set_option hygiene false in
local notation "Λ" => ULift.{u + 1} (ZMod n)

variable [HasExt.{v} A] [NeZero n]
  [HasExt.{wMX} (ModuleSheaf X Λ)] [HasExt.{wMS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{dMX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{dMS} (ModuleSheaf S Λ)]

set_option hygiene false in
local notation "I" => (Plus.singleFunctor (ModuleSheaf S Λ) 0).obj (moduleUnit S Λ)
set_option hygiene false in
local notation "N" => (Plus.singleFunctor (ModuleSheaf X Λ) 0).obj (moduleRootsOfUnity X n)
set_option hygiene false in
local notation "Q" => SheafOfModules.toSheaf (constantRing S Λ)

/-- The original coefficient functional evaluates the given original marked
point as the scalar root value computed by the original contraction. -/
theorem markedKummerTraceFunctional_value
    (x : Ext.{wMX} (moduleUnit X Λ) (moduleRootsOfUnity X n) 1) (a : U ⟶ representedSheaf K)
    (t : ShiftedHom ((moduleDerivedDirectImage Λ p).obj N) I (-1 : ℤ))
    (b : moduleUnit S Λ ⟶ moduleRootsOfUnity S n) (s₀ : ZMod n)
    (hx :
      let v := moduleRootsUnitExtCohomologyAddEquiv.{u, wMX, w} X n 1 x
      (H₁).map (cohomologyOriginalDerivedAdjunct p (mu X n) v) =
        (V₁).hom.app U ≫ a ≫ markedKummerH1Map p o ho n hn hi m hpow j)
    (hy : let e := constantModuleDerivedUnitPullbackIso p n
      let y : Ext.{wMS} (moduleUnit S Λ) (moduleUnit S Λ) 0 := moduleUnitScalarLinearMap S n s₀
      ((moduleDerivedAdjunction Λ p).shiftedHomEquiv 1 I N (e.hom ≫ x.homPlus)).comp t
        (by omega : (-1 : ℤ) + 1 = 0) = y.homPlus) :
    let r := (Q).map b ≫ (moduleRootsOfUnityUnderlyingIso S n).hom
    let θ := markedKummerTraceFunctional p o ho n hn hi m hpow j
      (moduleRootsShiftedMapUnderlying p n t)
    (Ext.mk₀ (a ≫ θ ≫ r) : Sheaf.H.{v} (mu S n) 0) =
      moduleRootsUnitExtCohomologyAddEquiv.{u, wMS, v} S n 0 (Ext.mk₀ (s₀.val • b)) := by
  intro r θ
  let y : Ext.{wMS} (moduleUnit S Λ) (moduleUnit S Λ) 0 := moduleUnitScalarLinearMap S n s₀
  let y' := etaleModuleExtCohomologyAddEquivLargeScalars.{u, wMS, v}
    S (constantRing S Λ) (moduleUnit S Λ) 0 y
  let t' := moduleRootsShiftedMapUnderlying p n t
  let v := moduleRootsUnitExtCohomologyAddEquiv.{u, wMX, w} X n 1 x
  let x' := cohomologyOriginalDerivedAdjunct p (mu X n) v
  let K₀ := (Plus.singleFunctor B 0).obj (mu X n)
  let B₀ := (derivedDirectImage p).obj K₀
  let eInt := ((inverseImage p).rightDerivedFunctorPlusSingleIso 0).app U ≪≫
    (Plus.singleFunctor B 0).mapIso
      ((inverseImageConstantIso p).app (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
  let z := (derivedImageAdjunction p).shiftedHomEquiv 1 ((F).obj U) K₀ (eInt.hom ≫ v.homPlus)
  let η := (Plus.singleFunctors A).shiftIso (-1) 1 0 (by omega)
  let adj := (shiftEquiv' (Plus A) (-1 : ℤ) (1 : ℤ) (by omega)).toAdjunction
  let z₀ : ShiftedHom ((F).obj U) B₀ (1 : ℤ) :=
    (adj.homEquiv ((F).obj U) B₀) (η.hom.app U ≫ x')
  have hz : z₀ = z := by
    let f := (adj.homEquiv ((F).obj U) B₀).symm z
    have h : η.hom.app U ≫ x' = f := (η.app U).hom_inv_id_assoc f
    exact (congrArg (adj.homEquiv ((F).obj U) B₀) h).trans
      ((adj.homEquiv ((F).obj U) B₀).apply_symm_apply z)
  have hF := moduleRootsAdjunctCompUnderlyingValue p n 1 0
    (by omega : (-1 : ℤ) + 1 = 0) x t y hy
  let φ := a ≫ markedKummerH1Map p o ho n hn hi m hpow j
  have hY : y'.homPlus = z₀.comp t' (by omega : (-1 : ℤ) + 1 = 0) :=
    hF.symm.trans (congrArg (fun z' : ShiftedHom ((F).obj U) B₀ (1 : ℤ) =>
      z'.comp t' (by omega : (-1 : ℤ) + 1 = 0)) hz.symm)
  have hA := Plus.eq_mk₀_of_singleShiftTrace_homologyValue 1 x' t' φ hx y' hY
  let κ := markedKummerH1Map p o ho n hn hi m hpow j
  let V := (Q).obj (moduleUnit S Λ)
  let δ := (H₁).map (t' ≫ η.hom.app V) ≫ (V₁).hom.app V
  have hAssoc : (a ≫ κ) ≫ δ = a ≫ θ := Category.assoc a κ δ
  have hA' : y' = Ext.mk₀ (a ≫ θ) :=
    hA.trans (congrArg (fun f : U ⟶ V => (Ext.mk₀ f : Ext.{v} U V 0)) hAssoc)
  have hP := moduleRootsUnitExtCohomologyAddEquiv_postcomp.{u, wMS, v} S n 0 b y
  change moduleRootsUnitExtCohomologyAddEquiv S n 0 (y.comp (Ext.mk₀ b) (add_zero 0)) =
    y'.comp (Ext.mk₀ r) (add_zero 0) at hP
  have hS : y.comp (Ext.mk₀ b) (add_zero 0) = Ext.mk₀ (s₀.val • b) := by
    change (moduleUnitScalarLinearMap S n s₀).comp (Ext.mk₀ b) (add_zero 0) = _
    rw [moduleUnitScalarLinearMap_apply_eq_mk₀_nsmul, Ext.mk₀_comp_mk₀,
      Preadditive.nsmul_comp, Category.id_comp]
  rw [hS, hA', Ext.mk₀_comp_mk₀] at hP
  exact ((congrArg Ext.mk₀ (Category.assoc a θ r)).symm.trans hP.symm)

end AlgebraicGeometry.Scheme.EtaleCohomology.Kummer
