/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.DerivedRestrictionTrace
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.RootsAdjunctTraceUnderlying
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.ModuleCohomologyPostcomp

/-! The original roots-coefficient value of the signed marked Kummer trace. -/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open GroupCohomology.Kummer.Coefficients GroupCohomology.Kummer.CoefficientBaseChange

@[expose] public noncomputable section

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Kummer

open DerivedCategory Picard RepresentedKernel Coefficients
open CategoryTheory.Abelian

universe u dX dS dMX dMS w s e v wMX wMS

attribute [local instance] hasSheafifyLarge hasSheafifyModules Over.cartesianMonoidalCategory
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

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

variable [HasExt.{v} A] [Epi (n • 𝟙 (representedSheaf G))]
  [HasExt.{wMX} (ModuleSheaf X Λ)] [HasExt.{wMS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{dMX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{dMS} (ModuleSheaf S Λ)]

set_option hygiene false in
local notation "I" => (Plus.singleFunctor (ModuleSheaf S Λ) 0).obj (moduleUnit S Λ)
set_option hygiene false in
local notation "N" => (Plus.singleFunctor (ModuleSheaf X Λ) 0).obj (moduleRootsOfUnity X n)
set_option hygiene false in
local notation "Q" => SheafOfModules.toSheaf (constantRing S Λ)

/-- The original contracted module trace gives the original signed marked cover
class, after changing to the specified original roots coefficient. -/
theorem markedKummer_module_trace_boundary_roots
    (c : Sheaf.H.{w} (gm X) 1) (a : U ⟶ representedSheaf G)
    (t : ShiftedHom ((moduleDerivedDirectImage Λ p).obj N) I (-1 : ℤ))
    (y : Ext.{wMS} (moduleUnit S Λ) (moduleUnit S Λ) 1)
    (x : Ext.{wMX} (moduleUnit X Λ) (moduleRootsOfUnity X n) 2)
    (b : moduleUnit S Λ ⟶ moduleRootsOfUnity S n)
    (hc :
      let ep := ((higherDirectImageIso p 1).app (gm X)).symm ≪≫
        gmHigherDirectImageNormalizedPicardIso.{u, w, s, e} p o ho
      (H₁).map (cohomologyOriginalDerivedAdjunct p (gm X) c) =
        (V₁).hom.app U ≫ a ≫ j ≫ ep.inv)
    (hx : moduleRootsUnitExtCohomologyAddEquiv.{u, wMX, w} X n 2 x =
      boundary X n hn (levelInvertible p n hi) 1 c)
    (hy : let u := constantModuleDerivedUnitPullbackIso p n
      ((moduleDerivedAdjunction Λ p).shiftedHomEquiv 2 I N (u.hom ≫ x.homPlus)).comp t
        (by omega : (-1 : ℤ) + 2 = 1) = y.homPlus) :
    let r := (Q).map b ≫ (moduleRootsOfUnityUnderlyingIso S n).hom
    let θ := markedKummerTraceFunctional p o ho n hn hi m hpow j
      (moduleRootsShiftedMapUnderlying p n t) ≫ r
    (((Ext.mk₀ a).comp (markedPowerKernelSequence_shortExact m n hpow).extClass
      (zero_add 1)).comp (Ext.mk₀ θ) (add_zero 1)) =
      -(moduleRootsUnitExtCohomologyAddEquiv.{u, wMS, v} S n 1
        (y.comp (Ext.mk₀ b) (add_zero 1))) := by
  intro r θ
  let y' := etaleModuleExtCohomologyAddEquivLargeScalars.{u, wMS, v}
    S (constantRing S Λ) (moduleUnit S Λ) 1 y
  let t' := moduleRootsShiftedMapUnderlying p n t
  let Y := (Plus.singleFunctor B 0).obj (mu X n)
  let eInt := ((inverseImage p).rightDerivedFunctorPlusSingleIso 0).app U ≪≫
    (Plus.singleFunctor B 0).mapIso
      ((inverseImageConstantIso p).app (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
  let z := fun x' : Sheaf.H.{w} (mu X n) 2 =>
    ((derivedImageAdjunction p).shiftedHomEquiv 2 ((F).obj U) Y
      (eInt.hom ≫ x'.homPlus)).comp t' (by omega : (-1 : ℤ) + 2 = 1)
  have hY := (moduleRootsAdjunctCompUnderlyingValue p n 2 1
    (by omega : (-1 : ℤ) + (2 : ℤ) = (1 : ℤ)) x t y hy).symm.trans
      (congrArg z hx)
  let φ := markedKummerTraceFunctional p o ho n hn hi m hpow j t'
  let hS := markedPowerKernelSequence_shortExact m n hpow
  let E := (Ext.mk₀ a).comp hS.extClass (zero_add 1)
  have hB : y' = -(E.comp (Ext.mk₀ φ) (add_zero 1)) :=
    markedKummer_trace_boundary p o ho n hn hi m hpow j c a t' y' hc hY
  have hP := moduleRootsUnitExtCohomologyAddEquiv_postcomp.{u, wMS, v} S n 1 b y
  have hP' : moduleRootsUnitExtCohomologyAddEquiv.{u, wMS, v} S n 1
      (y.comp (Ext.mk₀ b) (add_zero 1)) = y'.comp (Ext.mk₀ r) (add_zero 1) := hP
  change E.comp (Ext.mk₀ (φ ≫ r)) (add_zero 1) = _
  rw [hP', hB, Ext.neg_comp, neg_neg]
  have h := Ext.comp_assoc_of_third_deg_zero E (Ext.mk₀ φ) (Ext.mk₀ r) (add_zero 1)
  rw [Ext.mk₀_comp_mk₀] at h
  exact h.symm

end AlgebraicGeometry.Scheme.EtaleCohomology.Kummer
