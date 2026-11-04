/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.RootsOneFirstPullbackChart
public import Aglib.AlgebraicGeometry.Curves.Jacobian.WeilPairing.AbelKummer
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.DerivedRestrictionTrace
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.DerivedAdjunctNaturality
public import Aglib.AlgebraicGeometry.Group.Kernel.Commutative

/-! # The original first Kummer class in the original marked H¹ kernel -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.Scheme.EtaleCohomology.RepresentedKernel

open Scheme.Group.BaseChange

universe u
attribute [local instance] Over.cartesianMonoidalCategory hasSheafifyLarge
  groupSchemeBaseChange_isCommMonObj

/-- The original adjoint graph commutes with the original represented coefficient map. -/
private theorem representedIntegerSection_adjunct_map
    {S T : Scheme.{u}} (p : S ⟶ T) {K G : Grp (Over T)}
    [IsCommMonObj K.X] [IsCommMonObj G.X] (i : K ⟶ G)
    (x : (Over.map p).obj (Over.mk (𝟙 S)) ⟶ K.X) :
    representedIntegerSection (Group.BaseChange.baseChangedGroup p K)
        ((Over.mapPullbackAdj p).homEquiv (Over.mk (𝟙 S)) K.X x) ≫
      representedSheafMap ((groupSchemeBaseChange p).functor.map i) =
    representedIntegerSection (Group.BaseChange.baseChangedGroup p G)
      ((Over.mapPullbackAdj p).homEquiv (Over.mk (𝟙 S)) G.X (x ≫ i.hom.hom)) := by
  have h :
      (Over.mapPullbackAdj p).homEquiv (Over.mk (𝟙 S)) K.X x ≫
          ((groupSchemeBaseChange p).functor.map i).hom.hom =
        (Over.mapPullbackAdj p).homEquiv (Over.mk (𝟙 S)) G.X (x ≫ i.hom.hom) :=
    ((Over.mapPullbackAdj p).homEquiv_naturality_right x i.hom.hom).symm
  exact (representedIntegerSection_map ((groupSchemeBaseChange p).functor.map i)
    ((Over.mapPullbackAdj p).homEquiv (Over.mk (𝟙 S)) K.X x)).trans
      (congrArg (representedIntegerSection (Group.BaseChange.baseChangedGroup p G)) h)

end AlgebraicGeometry.Scheme.EtaleCohomology.RepresentedKernel

namespace AlgebraicGeometry.Scheme.OverField.Curve

open Scheme.RelativePicard Scheme.Group Scheme.Group.BaseChange Scheme.EtaleCohomology
open Scheme.Modules.Invertible Scheme.EtaleCohomology.Picard RepresentedKernel
open Scheme.EtaleCohomology.Kummer
open GroupCohomology.Kummer.Coefficients GroupCohomology.Kummer.CoefficientBaseChange

universe u w wZ dZ dX s e
attribute [local instance] Over.cartesianMonoidalCategory hasSheafifyLarge
  groupSchemeBaseChange_isCommMonObj Kernel.isCommMonObj_group

variable {k : Type u} [Field k] [IsAlgClosed k] {X : FScheme k} (hX : Properties X)
  [IsLocallyNoetherian X.left]
  (P : LocallyNoetherianOver (Base k)) [LocallyOfFiniteType P.obj.hom]
  [IsSeparated P.obj.hom]
  (R : ((locallyNoetherianOverInclusion (Base k)).op ⋙ (fppfPicardSheaf X.hom).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
  (n : ℕ) (hn : 0 < n) (hu : IsUnit (n : k))
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X.left)]

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

variable (o' : X.left ⟶ Z) (ho' : o' ≫ π = 𝟙 X.left)
  [IsProper π] [Flat π] [GeometricallyIntegral π]
  (hi : IsUnit (n : Γ(X.left, ⊤)))
  [HasExt.{wZ} (AbelianSheaf.{u, u + 1} Z)]
  [HasDerivedCategory.{dZ} (AbelianSheaf.{u, u + 1} Z)]
  [HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} X.left)]
  [∀ V : X.left.Etale, HasExt.{s} (Sheaf ((Scheme.smallEtaleTopology Z).over
    ((siteBaseChange π).obj V)) AddCommGrpCat.{u + 1})]
  [∀ V : X.left.Etale, HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback V.hom π))]

/-- The actual first-projection inverse Kummer class gives the original marked H¹ injection
of the graph of the same original kernel point. -/
theorem jacobianFirstKummerH1
    (y : letI := picardCommGrpObj X.hom P R
      let J := picardIdentityComponent X.hom P R
      letI : IsCommMonObj J := inferInstanceAs (IsCommMonObj (identityComponentOver P.obj))
      (T₀) ⟶ (MultiplicationKernel.kernelGroup (Grp.mk J) n).X) :
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
      E.symm (jacobianRationalTorsionOfKernelPoint P R n y)
    let ξ := Kummer.rootsCohomologyPullback.{u, w, wZ} f n hn hi 1 α
    let d : T' ⟶ locallyNoetherianRationalPoint k := ObjectProperty.homMk
      (Over.homMk (T').obj.hom (Category.comp_id (T').obj.hom))
    let yK := (Over.mapPullbackAdj X.hom).homEquiv (Over.mk (𝟙 X.left)) K.X (d.hom ≫ y)
    let a := representedIntegerSection Kp yK
    let hpow : representedSheafMap ((groupSchemeBaseChange X.hom).functor.map q) =
        n • 𝟙 (representedSheaf G) :=
      (congrArg representedSheafMap (groupSchemeBaseChange_map_identity_pow X.hom A n)).trans
        (RepresentedKernel.Native.representedSheafMap_multiplication G n)
    let H := DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} X.left) 1
    let V₁ := DerivedCategory.singleFunctorCompHomologyFunctorIso
      (AbelianSheaf.{u, u + 1} X.left) 1
    let I := (constantSheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))
    let x := cohomologyOriginalDerivedAdjunct π (mu Z n) ξ
    H.map x = V₁.hom.app I ≫ a ≫
      Kummer.markedKummerH1Map.{u, dZ, dX, wZ, s, e} π o' ho' n hn hi m hpow j := by
  intro J A q K G Kp m j E α ξ d yK a hpow H V₁ I x
  let := picardCommGrpObj X.hom P R
  let : IsCommMonObj J := inferInstanceAs (IsCommMonObj (identityComponentOver P.obj))
  let L := pullbackClass f (Kummer.rootsPicardMap X.left n α)
  let v := cohomologyOriginalDerivedAdjunct π (gm Z) (picardCohomologyEquiv.{u, wZ} Z L)
  let Tn := Kummer.derivedKummerTriangle π n hn (levelInvertible π n hi)
  let eT := Kummer.derivedKummerH1KernelIso.{u, dZ, dX, wZ, s, e}
    π n hn (levelInvertible π n hi) o' ho'
  let yG := rootsOneJacobianTerminalPoint hX P R n hn hu α
  let aG := representedIntegerSection G yG
  have hp : (E α).val.toMul = y ≫ (Kernel.inclusion q).hom.hom := by
    exact congrArg (fun t => t.val.toMul) (E.apply_symm_apply
      (jacobianRationalTorsionOfKernelPoint P R n y))
  have hg : (Over.mapPullbackAdj X.hom).homEquiv (Over.mk (𝟙 X.left)) A.X
      ((d.hom ≫ y) ≫ (Kernel.inclusion q).hom.hom) = yG := by
    change (Over.mapPullbackAdj X.hom).homEquiv (Over.mk (𝟙 X.left)) A.X
      ((d.hom ≫ y) ≫ (Kernel.inclusion q).hom.hom) =
      (Over.mapPullbackAdj X.hom).homEquiv (Over.mk (𝟙 X.left)) A.X
        (d.hom ≫ (E α).val.toMul)
    exact congrArg ((Over.mapPullbackAdj X.hom).homEquiv (Over.mk (𝟙 X.left)) A.X)
      ((Category.assoc _ _ _).trans (congrArg (fun t => d.hom ≫ t) hp.symm))
  have hSection : a ≫ (markedKernelSequence m).f = aG :=
    (representedIntegerSection_adjunct_map X.hom (Kernel.inclusion q) (d.hom ≫ y)).trans
      (congrArg (representedIntegerSection G) hg)
  have hClass := Kummer.rootsPicardMap_pullback_cohomologyValue.{u, w, wZ} f n hn hi α
  have hc : Sheaf.H.map (inclusion Z n) 1 ξ = picardCohomologyEquiv.{u, wZ} Z L := by
    have h := congrArg (picardCohomologyEquiv.{u, wZ} Z) hClass
    simpa only [AddEquiv.apply_symm_apply] using h
  have hmap : v = x ≫ Tn.mor₁ := by
    have h := cohomologyOriginalDerivedAdjunct_map π (inclusion Z n) ξ
    rw [hc] at h
    exact h
  have hGm := rootsOneJacobianFirstPullbackGmAdjunctH1.{u, w, wZ, dZ, dX, s, e}
    hX P R n hn hu o' ho' α
  apply Kummer.markedKummerH1Map_value_of_mapped π o' ho' n hn hi m hpow j x a
  change H.map (x ≫ Tn.mor₁) ≫ eT.hom.τ₂ = V₁.hom.app I ≫ a ≫
    (markedKernelSequence m).f ≫ j
  rw [← hmap, Kummer.derivedKummerH1KernelIso_hom_τ₂]
  change H.map v ≫ (higherDirectImageIso π 1).inv.app (gm Z) ≫
    (gmHigherDirectImageNormalizedPicardIso.{u, wZ, s, e} π o' ho').hom = _
  have hGm' : H.map v ≫ (higherDirectImageIso π 1).inv.app (gm Z) ≫
      (gmHigherDirectImageNormalizedPicardIso.{u, wZ, s, e} π o' ho').hom =
    V₁.hom.app I ≫ aG ≫ j := hGm
  have hs := congrArg (fun b => V₁.hom.app I ≫ b ≫ j) hSection.symm
  have hs' := congrArg (fun b => V₁.hom.app I ≫ b)
    (Category.assoc a (markedKernelSequence m).f j)
  exact hGm'.trans (hs.trans hs')

end AlgebraicGeometry.Scheme.OverField.Curve
