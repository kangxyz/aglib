/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.RelativePicardSheaf.NormalizedChart
public import Aglib.AlgebraicGeometry.Picard.BaseChangeFamilyValue

/-! The original normalized Picard chart under the original base change. -/

open CategoryTheory CategoryTheory.Limits Opposite

@[expose] public noncomputable section

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Kummer

open Scheme.RelativePicard Scheme.Modules.Invertible

universe u

attribute [local instance] hasSheafifyLarge Over.cartesianMonoidalCategory

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X S : Scheme.{u}} [IsLocallyNoetherian S] (p : X ⟶ S)
  (o : S ⟶ X) (ho : o ≫ p = 𝟙 S) [IsProper p] [Flat p] [GeometricallyIntegral p]
  (P : LocallyNoetherianOver S) [LocallyOfFiniteType P.obj.hom]
  (R : ((locallyNoetherianOverInclusion S).op ⋙ (fppfPicardSheaf p).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
  {G : Grp (Over S)} [IsCommMonObj G.X] (U : S.Etale)

/-- The original normalized value of a represented chart point and its family. -/
def NormalizedChartFamilyValue
    (i : letI := picardCommGrpObj p P R; G ⟶ Grp.mk P.obj)
    (x : (Scheme.Etale.forget S).obj U ⟶ G.X)
    (c : PicardGroup (pullback p U.hom)) : Prop :=
    letI := picardCommGrpObj p P R
    (representedSheafMap (K := Grp.mk P.obj) i ≫
        (picardRepresenterNormalizedEtaleIso p o ho P R).hom).hom.app (op U)
      (ULift.up (Additive.ofMul x)) =
    normalizedFamilyClass p o ho ((Scheme.Etale.forget S).obj U) c

/-- A represented map followed by the original normalized Picard comparison
has the original normalized family value. -/
theorem picardNormalizedChart_of_family_comp
    (i : letI := picardCommGrpObj p P R; G ⟶ Grp.mk P.obj)
    (x : (Scheme.Etale.forget S).obj U ⟶ G.X)
    (c : PicardGroup (pullback p U.hom))
    (h : R.homEquiv (ObjectProperty.homMk (x ≫ i.hom.hom) :
      locallyNoetherianEtaleTest U ⟶ P) =
      ((quotientProjection p ≫ toFppfPicardSheaf p).app
        (op ((Scheme.Etale.forget S).obj U))).hom c) :
    NormalizedChartFamilyValue p o ho P R U i x c := by
  dsimp only [NormalizedChartFamilyValue]
  let N := picardRepresenterNormalizedEtaleIso p o ho P R
  change N.hom.hom.app (op U) (ULift.up (Additive.ofMul (x ≫ i.hom.hom))) = _
  exact picardRepresenterNormalizedEtaleIso_hom_app_of_family p o ho P R U (x ≫ i.hom.hom) c h

/-- Read the original chart value on the original sections. -/
theorem NormalizedChartFamilyValue.eq
    {i : letI := picardCommGrpObj p P R; G ⟶ Grp.mk P.obj}
    {x : (Scheme.Etale.forget S).obj U ⟶ G.X}
    {c : PicardGroup (pullback p U.hom)}
    (h : NormalizedChartFamilyValue p o ho P R U i x c) :
    letI := picardCommGrpObj p P R
    (representedSheafMap (K := Grp.mk P.obj) i ≫
        (picardRepresenterNormalizedEtaleIso p o ho P R).hom).hom.app (op U)
      (ULift.up (Additive.ofMul x)) =
    normalizedFamilyClass p o ho ((Scheme.Etale.forget S).obj U) c := h

/-- A specified equality of points and families preserves the original normalized chart value. -/
theorem NormalizedChartFamilyValue.congr
    {i : letI := picardCommGrpObj p P R; G ⟶ Grp.mk P.obj}
    {x y : (Scheme.Etale.forget S).obj U ⟶ G.X}
    {c d : PicardGroup (pullback p U.hom)}
    (h : NormalizedChartFamilyValue p o ho P R U i x c) (hx : x = y) (hc : c = d) :
    NormalizedChartFamilyValue p o ho P R U i y d := by
  subst y d
  exact h

end AlgebraicGeometry.Scheme.EtaleCohomology.Kummer

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Kummer

open Scheme.RelativePicard Scheme.Modules.Invertible

universe u

attribute [local instance] hasSheafifyLarge Over.cartesianMonoidalCategory

variable {X S S' : Scheme.{u}} (p : X ⟶ S) (f : S' ⟶ S)
  [IsLocallyNoetherian S'] (o : S' ⟶ pullback p f) (ho : o ≫ pullback.snd p f = 𝟙 S')
  [IsProper (pullback.snd p f)] [Flat (pullback.snd p f)]
  [GeometricallyIntegral (pullback.snd p f)]
  (P : LocallyNoetherianOver S) [LocallyOfFiniteType P.obj.hom]
  (R : ((locallyNoetherianOverInclusion S).op ⋙ (fppfPicardSheaf p).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
  {G : Grp (Over S')} [IsCommMonObj G.X] (U : S'.Etale)

/-- The original normalized chart value after base change, with the original
relative class displayed before specialization. -/
abbrev picardNormalizedChartBaseChangeOfAdjointValue
    (i :
      let Q := LocallyNoetherianOver.baseChange f P
      let hQ := baseChangeRepresentableBy p f P R
      letI : LocallyOfFiniteType Q.obj.hom :=
        Scheme.locallyOfFiniteType_over_pullback_obj_hom f P.obj
      letI := picardCommGrpObj (pullback.snd p f) Q hQ
      G ⟶ Grp.mk Q.obj)
    (x : (Scheme.Etale.forget S').obj U ⟶ G.X)
    (c : PicardGroup (pullback p (U.hom ≫ f)))
    (y : ((LocallyNoetherianOver.map f).obj (locallyNoetherianEtaleTest U)).obj ⟶ P.obj)
    (hy : ((Over.mapPullbackAdj f).homEquiv (locallyNoetherianEtaleTest U).obj P.obj).symm
      (x ≫ i.hom.hom) = y)
    (hc :
      let T' := (LocallyNoetherianOver.map f).obj (locallyNoetherianEtaleTest U)
      R.homEquiv (ObjectProperty.homMk y : T' ⟶ P) =
        ((quotientProjection p ≫ toFppfPicardSheaf p).app (op T'.obj)).hom c) :=
  let T := locallyNoetherianEtaleTest U
  let Q := LocallyNoetherianOver.baseChange f P
  let hQ := baseChangeRepresentableBy p f P R
  letI : LocallyOfFiniteType Q.obj.hom := Scheme.locallyOfFiniteType_over_pullback_obj_hom f P.obj
  let t : T ⟶ Q := ObjectProperty.homMk (x ≫ i.hom.hom)
  let c' := pullbackClass (familyBaseChangeIso p f T.obj).hom c
  let T' := (LocallyNoetherianOver.map f).obj T
  let h := (congrArg (fun z => R.homEquiv (ObjectProperty.homMk z : T' ⟶ P)) hy).trans hc
  picardNormalizedChart_of_family_comp (pullback.snd p f) o ho Q hQ U i x c'
    (baseChangeRepresentableBy_homEquiv_of_family p f P R t c h)

end AlgebraicGeometry.Scheme.EtaleCohomology.Kummer
