/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.AbelCurve
public import Aglib.AlgebraicGeometry.Curves.Jacobian.PicardDegreeZeroEtaleChart
public import Aglib.AlgebraicGeometry.Curves.Abel.Naturality

/-! The original Abel class on the original normalized terminal chart. -/

open CategoryTheory CategoryTheory.Limits Opposite
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

@[expose] public noncomputable section

namespace AlgebraicGeometry.Scheme.OverField.Curve

open Scheme.RelativePicard Scheme.Group Scheme.EtaleCohomology Scheme.Group.BaseChange
open Scheme.Modules.Invertible

universe u

attribute [local instance] Over.cartesianMonoidalCategory hasSheafifyLarge
  groupSchemeBaseChange_isCommMonObj

variable {k : Type u} [Field k] {X : FScheme k} (hX : Curve.Properties X)
  (o : Base k ⟶ X.left) (ho : o ≫ X.hom = 𝟙 (Base k))
  [IsLocallyNoetherian X.left]
  (P : LocallyNoetherianOver (Base k)) [LocallyOfFiniteType P.obj.hom]
  (R : ((locallyNoetherianOverInclusion (Base k)).op ⋙ (fppfPicardSheaf X.hom).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)

set_option hygiene false in
local notation "U" => etaleTerminal X.left
set_option hygiene false in
local notation "T" => Kummer.locallyNoetherianEtaleTest U
set_option hygiene false in
local notation "T'" => (LocallyNoetherianOver.map X.hom).obj T

/-- The original terminal section on the base of the original Abel family. -/
abbrev abelTerminalTestPoint : (T').obj ⟶ X :=
  Over.homMk (𝟙 X.left) rfl

/-- The base-changed Abel line-bundle class is the pullback of the universal
Abel line-bundle class along the original terminal family projection. -/
theorem abelTerminalFamilyClass_pullback :
    letI := hX.smooth
    letI := hX.proper
    let p := X.hom
    let q := abelTerminalTestPoint (X := X)
    let c := Hom.abelClass Hom.smoothRelativeDivisorIdeal p o ho p (𝟙 X.left)
      (Category.id_comp p)
    let c' := Hom.abelClass Hom.smoothRelativeDivisorIdeal p o ho (T').obj.hom q.left q.w
    pullbackClass (familyBaseChangeIso p p (T).obj).hom c' =
      pullbackClass (pullback.fst (pullback.snd p p) (𝟙 X.left)) c := by
  dsimp only
  let : SmoothOfRelativeDimension 1 X.hom := hX.smooth
  let : IsProper X.hom := hX.proper
  let p := X.hom
  let q := abelTerminalTestPoint (X := X)
  let c := Hom.abelClass Hom.smoothRelativeDivisorIdeal p o ho p (𝟙 X.left) (Category.id_comp p)
  let c' := Hom.abelClass Hom.smoothRelativeDivisorIdeal p o ho (T').obj.hom q.left q.w
  have h : pullbackClass ((familyScheme p).map q) c = c' := by
    have h' := Abel.abelClass_baseChange Hom.smoothRelativeDivisorIdeal
      Hom.relativeCartierIdealBaseChange moduleTensorPullback p o ho p (T').obj.hom
      (𝟙 X.left) (Category.id_comp p) q.left q.w
    change pullbackClass ((familyScheme p).map q) c = _ at h'
    simpa only [Category.comp_id] using h'
  calc
    _ = pullbackClass (familyBaseChangeIso p p (T).obj).hom
        (pullbackClass ((familyScheme p).map q) c) := congrArg _ h.symm
    _ = pullbackClass ((familyBaseChangeIso p p (T).obj).hom ≫ (familyScheme p).map q) c :=
      (pullbackClass_comp _ _ c).symm
    _ = _ := congrArg (fun z => pullbackClass z c) (familyBaseChangeIso_hom_comp_terminal p p)

/-- The original Abel section gives the original normalized terminal value. -/
abbrev jacobianAbelTerminalChartValue
    (o' : X.left ⟶ pullback X.hom X.hom)
    (ho' : o' ≫ pullback.snd X.hom X.hom = 𝟙 X.left)
    [IsProper (pullback.snd X.hom X.hom)] [Flat (pullback.snd X.hom X.hom)]
    [GeometricallyIntegral (pullback.snd X.hom X.hom)] :=
  letI := hX.smooth
  letI := hX.proper
  letI := picardCommGrpObj X.hom P R
  let p := X.hom
  let q := abelTerminalTestPoint (X := X)
  let t := q ≫ jacobianCurveMorphism hX o ho P R
  let c := Hom.abelClass Hom.smoothRelativeDivisorIdeal p o ho (T').obj.hom q.left q.w
  jacobianEtaleChartPointNormalizedValue P R p U o' ho' t c
    (homEquiv_comp_jacobianCurveMorphism hX o ho P R q)

/-- The original Abel point on the same graph used for the marked multiplication row. -/
abbrev jacobianAbelTerminalGraph :=
  letI := picardCommGrpObj X.hom P R
  let J := picardIdentityComponent X.hom P R
  let a := jacobianCurveMorphism hX o ho P R
  (Over.mapPullbackAdj X.hom).homEquiv (Over.mk (𝟙 X.left)) J
    (Over.homMk a.left (a.w.trans (Category.id_comp X.hom).symm))

/-- The represented chart evaluates the same original Abel graph section and class. -/
abbrev jacobianAbelTerminalGraphNormalizedValue
    (o' : X.left ⟶ pullback X.hom X.hom)
    (ho' : o' ≫ pullback.snd X.hom X.hom = 𝟙 X.left)
    [IsProper (pullback.snd X.hom X.hom)] [Flat (pullback.snd X.hom X.hom)]
    [GeometricallyIntegral (pullback.snd X.hom X.hom)] :=
  letI := hX.smooth
  letI := hX.proper
  letI := picardCommGrpObj X.hom P R
  let p := X.hom
  let q := abelTerminalTestPoint (X := X)
  let a := jacobianCurveMorphism hX o ho P R
  let t := q ≫ a
  let J := picardIdentityComponent p P R
  let x := jacobianEtaleChartPoint P R p U t
  let y := jacobianAbelTerminalGraph hX o ho P R
  let ht : t = Over.homMk a.left (a.w.trans (Category.id_comp p).symm) := by
    apply Over.OverMorphism.ext
    exact Category.id_comp a.left
  let hx : x = y := congrArg ((Over.mapPullbackAdj p).homEquiv (Over.mk (𝟙 X.left)) J) ht
  Kummer.NormalizedChartFamilyValue.congr _ _ _ _ _ _
    (jacobianAbelTerminalChartValue hX o ho P R o' ho') hx
    (abelTerminalFamilyClass_pullback hX o ho)

end AlgebraicGeometry.Scheme.OverField.Curve
