/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.Kummer
public import Aglib.AlgebraicGeometry.Curves.Jacobian.PicardDegreeZeroEtaleChart
public import Aglib.AlgebraicGeometry.Picard.BaseChangeFamilyValue

/-! The original Kummer class in the original normalized Jacobian chart. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.Scheme.OverField.Curve

open Scheme.RelativePicard Scheme.Group Scheme.EtaleCohomology Scheme.Group.BaseChange
open Scheme.Modules.Invertible GroupCohomology.Kummer.Coefficients

universe u w

attribute [local instance] Over.cartesianMonoidalCategory hasSheafifyLarge
  groupSchemeBaseChange_isCommMonObj

variable {k : Type u} [Field k] [IsAlgClosed k] {X : FScheme k} (hX : Curve.Properties X)
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

/-- The original family of the rational Picard point in the original terminal chart. -/
abbrev rootsOneJacobianTerminalFppfValue (x : Sheaf.H.{w} (mu X.left n) 1) :=
  letI := picardCommGrpObj X.hom P R
  let p := X.hom
  let Q := locallyNoetherianRationalPoint k
  let d : T' ⟶ Q := ObjectProperty.homMk
    (Over.homMk (T').obj.hom (Category.comp_id (T').obj.hom))
  let t := (rootsOneJacobianTorsionAddEquiv hX P R n hn hu x).val.toMul
  let a : Q ⟶ P := ObjectProperty.homMk (t ≫ identityComponentι P.obj)
  let c := Kummer.rootsPicardMap X.left n x
  let r := pullback.fst p (𝟙 (Base k))
  let h := homEquiv_rootsOneJacobianTorsionAddEquiv hX P R n hn hu x
  let h₀ := homEquiv_comp_of_familyClass p P R d a (pullbackClass r c) h
  let h₁ := (pullbackClass_comp ((familyScheme p).map d.hom) r c).symm.trans
    (congrArg (fun f => pullbackClass f c) (familyScheme_map_fst p d.hom))
  h₀.trans (congrArg (((quotientProjection p ≫ toFppfPicardSheaf p).app
    (op (T').obj)).hom) h₁)

/-- The first Kummer class gives its original constant family in the original Jacobian chart. -/
abbrev rootsOneJacobianTerminalChartValue
    (o' : X.left ⟶ pullback X.hom X.hom)
    (ho' : o' ≫ pullback.snd X.hom X.hom = 𝟙 X.left)
    [IsProper (pullback.snd X.hom X.hom)] [Flat (pullback.snd X.hom X.hom)]
    [GeometricallyIntegral (pullback.snd X.hom X.hom)]
    (x : Sheaf.H.{w} (mu X.left n) 1) :=
  letI := picardCommGrpObj X.hom P R
  let p := X.hom
  let Q := locallyNoetherianRationalPoint k
  let d : T' ⟶ Q := ObjectProperty.homMk
    (Over.homMk (T').obj.hom (Category.comp_id (T').obj.hom))
  let t := d.hom ≫ (rootsOneJacobianTorsionAddEquiv hX P R n hn hu x).val.toMul
  let c := pullbackClass (pullback.fst p (T').obj.hom) (Kummer.rootsPicardMap X.left n x)
  let e := rootsOneJacobianTerminalFppfValue hX P R n hn hu x
  let hr : ObjectProperty.homMk (t ≫ identityComponentι P.obj) =
      d ≫ (ObjectProperty.homMk ((rootsOneJacobianTorsionAddEquiv hX P R n hn hu x).val.toMul ≫
        identityComponentι P.obj) : Q ⟶ P) := by
    apply ObjectProperty.hom_ext
    exact Category.assoc _ _ _
  jacobianEtaleChartPointNormalizedValue P R p U o' ho' t c
    ((congrArg R.homEquiv hr).trans e)

end AlgebraicGeometry.Scheme.OverField.Curve
