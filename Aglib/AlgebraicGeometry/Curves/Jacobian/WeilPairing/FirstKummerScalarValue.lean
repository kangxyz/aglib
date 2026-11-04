/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.WeilPairing.FirstKummerH1
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.MarkedKummerScalarTrace

/-! # Scalar value of the original marked first Kummer point -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits CategoryTheory.Pretriangulated
open GroupCohomology.Kummer.Coefficients GroupCohomology.Kummer.CoefficientBaseChange


namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wMX wMY wAX wAY
attribute [local instance] hasSheafifyLarge hasSheafifyModules

/-- The original module pullback of the original inverse comparison has its original
roots cohomology value. -/
private theorem moduleRootsUnitExtPullback_inverseValue
    {X Y : Scheme.{u}} (f : Y ⟶ X) (n : ℕ) (hn : 0 < n)
    (hi : IsUnit (n : Γ(X, ⊤)))
    [HasExt.{wMX} (ModuleSheaf X (ULift.{u + 1} (ZMod n)))]
    [HasExt.{wMY} (ModuleSheaf Y (ULift.{u + 1} (ZMod n)))]
    [HasExt.{wAX} (AbelianSheaf.{u, u + 1} X)]
    [HasExt.{wAY} (AbelianSheaf.{u, u + 1} Y)]
    (c : Sheaf.H.{wAX} (mu X n) 1) :
    moduleRootsUnitExtCohomologyAddEquiv.{u, wMY, wAY} Y n 1
        (moduleRootsUnitExtPullback.{u, wMX, wMY} f n hn hi 1
          ((moduleRootsUnitExtCohomologyAddEquiv.{u, wMX, wAX} X n 1).symm c)) =
      Kummer.rootsCohomologyPullback.{u, wAX, wAY} f n hn hi 1 c := by
  let E := moduleRootsUnitExtCohomologyAddEquiv.{u, wMX, wAX} X n 1
  have h := DFunLike.congr_fun
    (moduleRootsUnitExtCohomologyPullback_square.{u, wMX, wMY, wAX, wAY} f n hn hi 1)
    (E.symm c)
  exact h.trans (congrArg (Kummer.rootsCohomologyPullback.{u, wAX, wAY} f n hn hi 1)
    (E.apply_symm_apply c))

end AlgebraicGeometry.Scheme.EtaleCohomology

namespace AlgebraicGeometry.Scheme.OverField.Curve

open Scheme.RelativePicard Scheme.Group Scheme.Group.BaseChange Scheme.EtaleCohomology
open Scheme.Modules.Invertible Scheme.EtaleCohomology.Picard RepresentedKernel Coefficients
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

universe u w wZ w₀ dZ dX s e wMX wMZ dMX dMZ
attribute [local instance] Over.cartesianMonoidalCategory hasSheafifyLarge hasSheafifyModules
  groupSchemeBaseChange_isCommMonObj Kernel.isCommMonObj_group
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard moduleSheafExtZModModule

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [Field k] [IsAlgClosed k] {X : FScheme k} (hX : Properties X)
  [IsLocallyNoetherian X.left]
  (P : LocallyNoetherianOver (Base k)) [LocallyOfFiniteType P.obj.hom]
  [IsSeparated P.obj.hom]
  (R : ((locallyNoetherianOverInclusion (Base k)).op ⋙ (fppfPicardSheaf X.hom).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
  (n : ℕ) (hn : 0 < n) (hu : IsUnit (n : k))
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X.left)]
  [HasExt.{w₀} (AbelianSheaf.{u, u + 1} X.left)]

set_option hygiene false in
local notation "U" => etaleTerminal X.left
set_option hygiene false in
local notation "T" => Kummer.locallyNoetherianEtaleTest U
set_option hygiene false in
local notation "T'" => (LocallyNoetherianOver.map X.hom).obj T
set_option hygiene false in
local notation "Z" => pullback X.hom X.hom
set_option hygiene false in
local notation "π" => pullback.snd X.hom X.hom
set_option hygiene false in
local notation "f" => pullback.fst X.hom X.hom
set_option hygiene false in
local notation "T₀" => (𝟙_ (FScheme k))
set_option hygiene false in
local notation "Λ" => ULift.{u + 1} (ZMod n)

variable (o' : X.left ⟶ Z) (ho' : o' ≫ π = 𝟙 X.left)
  [IsProper π] [Flat π] [GeometricallyIntegral π]
  (hi : IsUnit (n : Γ(X.left, ⊤)))
  [HasExt.{wZ} (AbelianSheaf.{u, u + 1} Z)]
  [HasDerivedCategory.{dZ} (AbelianSheaf.{u, u + 1} Z)]
  [HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} X.left)]
  [∀ V : X.left.Etale, HasExt.{s} (Sheaf ((Scheme.smallEtaleTopology Z).over
    ((siteBaseChange π).obj V)) AddCommGrpCat.{u + 1})]
  [∀ V : X.left.Etale, HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback V.hom π))]
  [HasExt.{wMX} (ModuleSheaf X.left Λ)] [HasExt.{wMZ} (ModuleSheaf Z Λ)]
  [HasDerivedCategory.{dMX} (ModuleSheaf X.left Λ)]
  [HasDerivedCategory.{dMZ} (ModuleSheaf Z Λ)]

set_option hygiene false in
local notation "Iₘ" => (DerivedCategory.Plus.singleFunctor (ModuleSheaf X.left Λ) 0).obj
  (moduleUnit X.left Λ)
set_option hygiene false in
local notation "Nₘ" => (DerivedCategory.Plus.singleFunctor (ModuleSheaf Z Λ) 0).obj
  (moduleRootsOfUnity Z n)

/-- The original marked first point has the scalar coefficient value supplied by the
original module contraction, with no extra H¹ or module/cohomology comparison premise. -/
theorem jacobianFirstKummerTraceFunctional_value
    (x : letI := picardCommGrpObj X.hom P R
      let J := picardIdentityComponent X.hom P R
      letI : IsCommMonObj J := inferInstanceAs (IsCommMonObj (identityComponentOver P.obj))
      (T₀) ⟶ (MultiplicationKernel.kernelGroup (Grp.mk J) n).X)
    (t : ShiftedHom ((moduleDerivedDirectImage Λ π).obj Nₘ) Iₘ (-1 : ℤ))
    (b : moduleUnit X.left Λ ⟶ moduleRootsOfUnity X.left n) (s₀ : ZMod n) :
    letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
    letI := picardCommGrpObj X.hom P R
    let J := picardIdentityComponent X.hom P R
    letI : IsCommMonObj J := inferInstanceAs (IsCommMonObj (identityComponentOver P.obj))
    let A := Grp.mk J
    let q := MultiplicationKernel.multiplicationHom A n
    let K := Kernel.group q
    let G := Group.BaseChange.baseChangedGroup X.hom A
    let Kp := Group.BaseChange.baseChangedGroup X.hom K
    let m := kernelMarking X.hom (Kernel.marking q)
    let j := picardDegreeZeroEtaleInclusion P R X.hom o' ho'
    let E := rootsOneJacobianTorsionAddEquiv.{u, w} hX P R n hn hu
    let α : Sheaf.H.{w} (mu X.left n) 1 :=
      E.symm (jacobianRationalTorsionOfKernelPoint P R n x)
    let v := (moduleRootsUnitExtCohomologyAddEquiv.{u, wMX, w} X.left n 1).symm α
    let v₁ := moduleRootsUnitExtPullback.{u, wMX, wMZ} f n hn hi 1 v
    let d : T' ⟶ locallyNoetherianRationalPoint k := ObjectProperty.homMk
      (Over.homMk (T').obj.hom (Category.comp_id (T').obj.hom))
    let xK := (Over.mapPullbackAdj X.hom).homEquiv (Over.mk (𝟙 X.left)) K.X (d.hom ≫ x)
    let a := representedIntegerSection Kp xK
    let hpow : representedSheafMap ((groupSchemeBaseChange X.hom).functor.map q) =
        n • 𝟙 (representedSheaf G) :=
      (congrArg representedSheafMap (groupSchemeBaseChange_map_identity_pow X.hom A n)).trans
        (RepresentedKernel.Native.representedSheafMap_multiplication G n)
    let r := (SheafOfModules.toSheaf (constantRing X.left Λ)).map b ≫
      (moduleRootsOfUnityUnderlyingIso X.left n).hom
    let θ := Kummer.markedKummerTraceFunctional π o' ho' n hn hi m hpow j
      (Kummer.moduleRootsShiftedMapUnderlying π n t)
    let ep := constantModuleDerivedUnitPullbackIso π n
    let y : Ext.{wMX} (moduleUnit X.left Λ) (moduleUnit X.left Λ) 0 :=
      moduleUnitScalarLinearMap X.left n s₀
    ((moduleDerivedAdjunction Λ π).shiftedHomEquiv 1 Iₘ Nₘ (ep.hom ≫ v₁.homPlus)).comp t
        (by omega : (-1 : ℤ) + 1 = 0) = y.homPlus →
      (Ext.mk₀ (a ≫ θ ≫ r) : Sheaf.H.{w₀} (mu X.left n) 0) =
        moduleRootsUnitExtCohomologyAddEquiv.{u, wMX, w₀} X.left n 0
          (Ext.mk₀ (s₀.val • b)) := by
  intro J A q K G Kp m j E α v v₁ d xK a hpow r θ ep y h
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let := picardCommGrpObj X.hom P R
  let : IsCommMonObj J := inferInstanceAs (IsCommMonObj (identityComponentOver P.obj))
  let ξ := Kummer.rootsCohomologyPullback.{u, w, wZ} f n hn hi 1 α
  let H := DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} X.left) 1
  let V₁ := DerivedCategory.singleFunctorCompHomologyFunctorIso
    (AbelianSheaf.{u, u + 1} X.left) 1
  let I := (constantSheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of (ULift.{u + 1} ℤ))
  have hv₁ : moduleRootsUnitExtCohomologyAddEquiv.{u, wMZ, wZ} Z n 1 v₁ = ξ :=
    moduleRootsUnitExtPullback_inverseValue.{u, wMX, wMZ, w, wZ} f n hn hi α
  have hFirst := jacobianFirstKummerH1.{u, w, wZ, dZ, dX, s, e}
    hX P R n hn hu o' ho' hi x
  have hx : H.map (cohomologyOriginalDerivedAdjunct π (mu Z n)
        (moduleRootsUnitExtCohomologyAddEquiv.{u, wMZ, wZ} Z n 1 v₁)) =
      V₁.hom.app I ≫ a ≫ Kummer.markedKummerH1Map π o' ho' n hn hi m hpow j := by
    have hc := congrArg (fun z : Sheaf.H.{wZ} (mu Z n) 1 =>
      H.map (cohomologyOriginalDerivedAdjunct π (mu Z n) z)) hv₁
    exact hc.trans hFirst
  exact Kummer.markedKummerTraceFunctional_value.{u, dZ, dX, dMZ, dMX, wZ, s, e,
    w₀, wMZ, wMX} π o' ho' n hn hi m hpow j v₁ a t b s₀ hx h

end AlgebraicGeometry.Scheme.OverField.Curve
