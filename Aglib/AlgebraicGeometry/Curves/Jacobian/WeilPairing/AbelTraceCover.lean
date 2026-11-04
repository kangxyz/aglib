/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.WeilPairing.AbelPicardH1
public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.AbelContractedTrace
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.MarkedKummerModuleTrace
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.RepresentedMultiplicationBaseChange
public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.Multiplication.GroupMap
public import Aglib.AlgebraicGeometry.Curves.Jacobian.ProjectivityField
public import Aglib.AlgebraicGeometry.Curves.Jacobian.Smooth
public import Aglib.AlgebraicGeometry.Group.MultiplicationSmoothEtale
public import Aglib.AlgebraicGeometry.Group.Kernel.Commutative

/-! The signed original Abel cover value of the original relative trace. -/

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory MonObj
open GroupCohomology.Kummer.Coefficients GroupCohomology.Kummer.CoefficientBaseChange

@[expose] public noncomputable section

namespace AlgebraicGeometry.Scheme.OverField.Curve

open Scheme.RelativePicard Scheme.Group Scheme.Group.BaseChange Scheme.EtaleCohomology
open Scheme.Modules.Invertible Coefficients RepresentedKernel

universe u wM wZ wU wA wAZ wAU dM dZ dU dA dAZ s e

attribute [local instance] hasSheafifyLarge hasSheafifyModules Over.cartesianMonoidalCategory
  groupSchemeBaseChange_isCommMonObj
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

variable {k : Type u} [Field k] [IsAlgClosed k] {X : FScheme k} (hX : Properties X)
  (o : Base k ⟶ X.left) (ho : o ≫ X.hom = 𝟙 (Base k))
  [IsLocallyNoetherian X.left]
  (P : LocallyNoetherianOver (Base k)) [LocallyOfFiniteType P.obj.hom]
  [IsSeparated P.obj.hom]
  (R : ((locallyNoetherianOverInclusion (Base k)).op ⋙ (fppfPicardSheaf X.hom).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
  (n : ℕ) (hn : 0 < n) (hu : IsUnit (n : k)) (hi : IsUnit (n : Γ(X.left, ⊤)))

set_option hygiene false in
local notation "Z" => pullback X.hom X.hom
set_option hygiene false in
local notation "π" => pullback.snd X.hom X.hom
set_option hygiene false in
local notation "f" => pullback.fst X.hom X.hom
set_option hygiene false in
local notation "Λ" => ULift.{u + 1} (ZMod n)

variable (o' : X.left ⟶ Z) (ho' : o' ≫ π = 𝟙 X.left)
  [IsProper π] [Flat π] [GeometricallyIntegral π]
  {U : Scheme.{u}} (j : U ⟶ Z) [IsOpenImmersion j]
  (hj : Set.range j = (Set.range (pullback.diagonal X.hom))ᶜ)
  [HasExt.{wM} (ModuleSheaf X.left Λ)] [HasExt.{wZ} (ModuleSheaf Z Λ)]
  [HasExt.{wU} (ModuleSheaf U Λ)]
  [HasExt.{wA} (AbelianSheaf.{u, u + 1} X.left)] [HasExt.{wAZ} (AbelianSheaf.{u, u + 1} Z)]
  [HasExt.{wAU} (AbelianSheaf.{u, u + 1} U)]
  [HasDerivedCategory.{dM} (ModuleSheaf X.left Λ)]
  [HasDerivedCategory.{dZ} (ModuleSheaf Z Λ)]
  [HasDerivedCategory.{dU} (ModuleSheaf U Λ)]
  [HasDerivedCategory.{dA} (AbelianSheaf.{u, u + 1} X.left)]
  [HasDerivedCategory.{dAZ} (AbelianSheaf.{u, u + 1} Z)]
  [∀ V : X.left.Etale, HasExt.{s} (Sheaf ((Scheme.smallEtaleTopology Z).over
    ((siteBaseChange π).obj V)) AddCommGrpCat.{u + 1})]
  [∀ V : X.left.Etale, HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback V.hom π))]

set_option hygiene false in
local notation "I" => (DerivedCategory.Plus.singleFunctor (ModuleSheaf X.left Λ) 0).obj
  (moduleUnit X.left Λ)
set_option hygiene false in
local notation "N" => (DerivedCategory.Plus.singleFunctor (ModuleSheaf Z Λ) 0).obj
  (moduleRootsOfUnity Z n)

include hj in
/-- The original normalized Abel trace computes the original signed cover with
the traced coefficient map on the original marked multiplication kernel. -/
theorem jacobianAbelTraceCover
    (x : constantModuleExt.{u, wM} n X.left 1)
    (b : moduleUnit X.left Λ ⟶ moduleRootsOfUnity X.left n)
    (τ : ShiftedHom ((moduleDerivedDirectImage Λ π).obj N) I (-2 : ℤ))
    (hτ :
      let := hX.smooth
      let := hX.proper
      let e := constantModuleDerivedUnitPullbackIso π n
      let c := Kummer.diagonalModuleKummerClass X.hom n hn (levelInvertible f n hi)
      ((moduleDerivedAdjunction Λ π).shiftedHomEquiv 2 I N (e.hom ≫ c.homPlus)).comp τ
        (by omega : (-2 : ℤ) + 2 = 0) = ShiftedHom.mk₀ 0 rfl (𝟙 I)) :
    let p := X.hom
    let := hX.smooth
    let := hX.proper
    let := picardCommGrpObj p P R
    let J := picardIdentityComponent p P R
    let : IsCommMonObj J := inferInstanceAs (IsCommMonObj (identityComponentOver P.obj))
    let A : Grp (FScheme k) := Grp.mk J
    let : IsHProjective A.X.hom := isHProjective_identityComponentOver hX P R
    let : GeometricallyIntegral A.X.hom := geometricallyIntegral_identityComponentOver hX P R
    let : Smooth A.X.hom := smooth_identityComponentOver hX P R
    let G := (groupSchemeBaseChange p).functor.obj A
    let q := MultiplicationKernel.multiplicationHom A n
    let K := Kernel.group q
    let : IsCommMonObj K.X := Kernel.isCommMonObj_group q
    let m := kernelMarking p (Kernel.marking q)
    let hpow := (congrArg representedSheafMap (groupSchemeBaseChange_map_identity_pow p A n)).trans
      (RepresentedKernel.Native.representedSheafMap_multiplication G n)
    let hE : Etale q.hom.hom.left := by
      simpa only [q, MultiplicationKernel.multiplicationHom_hom,
        MultiplicationKernel.multiplication]
        using Multiplication.multiplication_etale_of_smooth_of_isUnit A n hu
    let hS := (Multiplication.multiplicationHom_finite_flat_surjective A n hn).2.2
    let : Epi (n • 𝟙 (representedSheaf G)) :=
      epi_nsmul_representedSheaf_groupBaseChange p A n hE hS
    let a := representedIntegerSection G (jacobianAbelTerminalGraph hX o ho P R)
    let j' := picardDegreeZeroEtaleInclusion P R p o' ho'
    let u := constantModuleExtPullback.{u, wM, wZ} n f 1 x
    let r : Ext.{wZ} (moduleRootsOfUnity Z n) (moduleRootsOfUnity Z n) 1 :=
      Kummer.moduleRootsExtOneTensor n hn hu (f ≫ p) u
    let t : ShiftedHom ((moduleDerivedDirectImage Λ π).obj N) I (-1 : ℤ) :=
      (r.homPlus.map (moduleDerivedDirectImage Λ π)).comp τ
      (by omega : (-2 : ℤ) + 1 = -1)
    let coeff := (SheafOfModules.toSheaf (constantRing X.left Λ)).map b ≫
      (moduleRootsOfUnityUnderlyingIso X.left n).hom
    let θ := Kummer.markedKummerTraceFunctional π o' ho' n hn hi m hpow j'
      (Kummer.moduleRootsShiftedMapUnderlying π n t) ≫ coeff
    let hS := Kummer.markedPowerKernelSequence_shortExact m n hpow
    (((Ext.mk₀ a).comp hS.extClass (zero_add 1)).comp (Ext.mk₀ θ) (add_zero 1)) =
      -(moduleRootsUnitExtCohomologyAddEquiv.{u, wM, wA} X.left n 1
        (x.comp (Ext.mk₀ b) (add_zero 1))) := by
  intro p hs hp laws J hJ A hProj hInt hSmooth G q K hK m hpow hE hSurj hEpi
    a j' u r t coeff θ hShort
  let := hs
  let := hp
  let := laws
  let := hJ
  let := hK
  let := hEpi
  let C := Hom.abelClass Hom.smoothRelativeDivisorIdeal p o ho p (𝟙 X.left) (Category.id_comp p)
  let c := Picard.picardCohomologyEquiv.{u, wAZ} Z C
  let xAb := Kummer.abelModuleKummerClass p o ho n hn hi
  let hx := Kummer.moduleRootsUnitExtCohomologyAddEquiv_abelModuleKummerClass p o ho n hn hi
  let hC := jacobianAbelPicardH1 hX o ho P R o' ho'
  let hT := Kummer.abelModuleKummerClassContractedTraceOfNormalized
    hX o ho n hn hu hi j hj x τ hτ
  exact Kummer.markedKummer_module_trace_boundary_roots.{u, dAZ, dA, dZ, dM, wAZ, s, e, wA, wZ, wM}
    π o' ho' n hn hi m hpow j' c a t x xAb b hC hx hT

end AlgebraicGeometry.Scheme.OverField.Curve
