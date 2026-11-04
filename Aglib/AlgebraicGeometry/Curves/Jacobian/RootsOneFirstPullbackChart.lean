/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.RootsOneDegreeZeroChart
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.DerivedAdjointRepresentedPicardChart

/-! The original Kummer point after the original first projection. -/

open CategoryTheory CategoryTheory.Limits Opposite
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

@[expose] public noncomputable section

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Kummer

open Scheme.Modules.Invertible GroupCohomology.Kummer.Coefficients
open GroupCohomology.Kummer.CoefficientBaseChange

universe u w w'

attribute [local instance] hasSheafifyLarge

variable {X Y : Scheme.{u}} (f : Y ⟶ X) (n : ℕ) (hn : 0 < n)
  (hi : IsUnit (n : Γ(X, ⊤)))
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)] [HasExt.{w'} (AbelianSheaf.{u, u + 1} Y)]

/-- The first roots Picard value is the original pullback of the original Picard class. -/
theorem rootsPicardMap_pullback_cohomologyValue (x : Sheaf.H.{w} (mu X n) 1) :
    (Picard.picardCohomologyEquiv Y).symm
      (Sheaf.H.map (inclusion Y n) 1 (rootsCohomologyPullback.{u, w, w'} f n hn hi 1 x)) =
        pullbackClass f (rootsPicardMap X n x) := by
  change rootsPicardMap Y n (rootsCohomologyPullback.{u, w, w'} f n hn hi 1 x) = _
  exact DFunLike.congr_fun (rootsPicardMap_pullback.{u, w, w'} f n hn hi) x

end AlgebraicGeometry.Scheme.EtaleCohomology.Kummer

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Kummer

open Scheme.RelativePicard Scheme.Modules.Invertible

universe u w s e dX dS

attribute [local instance] hasSheafifyLarge Over.cartesianMonoidalCategory

variable {X S : Scheme.{u}} (p : X ⟶ S)
  [HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{dS} (AbelianSheaf.{u, u + 1} S)]
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [∀ U : S.Etale, HasExt.{s} (Sheaf ((Scheme.smallEtaleTopology X).over
    ((siteBaseChange p).obj U)) AddCommGrpCat.{u + 1})]
  [∀ U : S.Etale, HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback U.hom p))]
  (o : S ⟶ X) (ho : o ≫ p = 𝟙 S)
  [IsLocallyNoetherian S] [IsProper p] [Flat p] [GeometricallyIntegral p]
  (P : LocallyNoetherianOver S) [LocallyOfFiniteType P.obj.hom]
  (R : ((locallyNoetherianOverInclusion S).op ⋙ (fppfPicardSheaf p).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)

/-- The original normalized chart of an actual family gives the actual Gm homology map. -/
abbrev gmDerivedAdjunctH1OfNormalizedChartFamilyValue
    {G : Grp (Over S)} [IsCommMonObj G.X]
    (i : letI := picardCommGrpObj p P R; G ⟶ Grp.mk P.obj)
    (x : Over.mk (𝟙 S) ⟶ G.X) (L : PicardGroup X)
    (h : NormalizedChartFamilyValue p o ho P R (etaleTerminal S) i x
      (pullbackClass (pullback.fst p (𝟙 S)) L)) :=
  letI := picardCommGrpObj p P R
  let N := picardRepresenterNormalizedEtaleIso p o ho P R
  let j := representedSheafMap (K := Grp.mk P.obj) i ≫ N.hom
  let E := Picard.picardCohomologyEquiv.{u, w} X
  let h' := NormalizedChartFamilyValue.eq p o ho P R (etaleTerminal S) h
  Picard.gmDerivedAdjunctH1OfRepresentedChartValue.{u, dX, dS, w, s, e}
    p o ho j x (E L) L (E.symm_apply_apply L) h'

end AlgebraicGeometry.Scheme.EtaleCohomology.Kummer

namespace AlgebraicGeometry.Scheme.OverField.Curve

open Scheme.RelativePicard Scheme.Group Scheme.EtaleCohomology Scheme.Group.BaseChange
open Scheme.Modules.Invertible GroupCohomology.Kummer.Coefficients
open GroupCohomology.Kummer.CoefficientBaseChange

universe u w wZ dZ dX s e

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
set_option hygiene false in
local notation "Z" => pullback X.hom X.hom
set_option hygiene false in
local notation "π" => pullback.snd X.hom X.hom
set_option hygiene false in
local notation "f" => pullback.fst X.hom X.hom

/-- The original field Kummer point, restricted to the same terminal test over the curve. -/
abbrev rootsOneJacobianTerminalPoint (x : Sheaf.H.{w} (mu X.left n) 1) :=
  letI := picardCommGrpObj X.hom P R
  let d : T' ⟶ locallyNoetherianRationalPoint k := ObjectProperty.homMk
    (Over.homMk (T').obj.hom (Category.comp_id (T').obj.hom))
  let t := d.hom ≫ (rootsOneJacobianTorsionAddEquiv hX P R n hn hu x).val.toMul
  jacobianEtaleChartPoint P R X.hom U t

variable (o' : X.left ⟶ Z) (ho' : o' ≫ π = 𝟙 X.left)
  [IsProper π] [Flat π] [GeometricallyIntegral π]

/-- The same normalized family value, written as the original first-projection pullback. -/
abbrev rootsOneJacobianTerminalChartValueFirstPullback
    (x : Sheaf.H.{w} (mu X.left n) 1) :=
  let p := X.hom
  let L := Kummer.rootsPicardMap X.left n x
  let E := familyBaseChangeIso p p (T).obj
  let l := pullback.fst p (T').obj.hom
  let a := pullback.fst π (𝟙 X.left)
  let h := rootsOneJacobianTerminalChartValue hX P R n hn hu o' ho' x
  let h₁ := (pullbackClass_comp E.hom l L).symm
  let h₂ := congrArg (fun g => pullbackClass g L) (familyBaseChangeIso_hom_fst p p (T).obj)
  let h₃ := pullbackClass_comp a f L
  Kummer.NormalizedChartFamilyValue.congr _ _ _ _ _ _ h rfl (h₁.trans (h₂.trans h₃))

variable (hi : IsUnit (n : Γ(X.left, ⊤)))
  [HasExt.{wZ} (AbelianSheaf.{u, u + 1} Z)]
  [HasDerivedCategory.{dZ} (AbelianSheaf.{u, u + 1} Z)]
  [HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} X.left)]
  [∀ V : X.left.Etale, HasExt.{s} (Sheaf ((Scheme.smallEtaleTopology Z).over
    ((siteBaseChange π).obj V)) AddCommGrpCat.{u + 1})]
  [∀ V : X.left.Etale, HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback V.hom π))]

/-- The original first-pullback roots class has the same degree-one Picard value
as the original constant Kummer point on the curve. -/
abbrev rootsOneJacobianFirstPullbackGmAdjunctH1
    (x : Sheaf.H.{w} (mu X.left n) 1) :=
  letI := picardCommGrpObj X.hom P R
  let p := X.hom
  let Q := LocallyNoetherianOver.baseChange p P
  let hQ := baseChangeRepresentableBy p p P R
  letI : LocallyOfFiniteType Q.obj.hom := Scheme.locallyOfFiniteType_over_pullback_obj_hom p P.obj
  let m := picardDegreeZeroEtaleGroupInclusion P R p
  let y := rootsOneJacobianTerminalPoint hX P R n hn hu x
  let L := pullbackClass f (Kummer.rootsPicardMap X.left n x)
  let h := rootsOneJacobianTerminalChartValueFirstPullback hX P R n hn hu o' ho' x
  Kummer.gmDerivedAdjunctH1OfNormalizedChartFamilyValue.{u, wZ, s, e, dZ, dX}
    π o' ho' Q hQ m y L h

end AlgebraicGeometry.Scheme.OverField.Curve
