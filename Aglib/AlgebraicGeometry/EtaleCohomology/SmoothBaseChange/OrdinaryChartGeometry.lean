/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.PullbackUnitGeometry
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.EtaleDirectImageSiteSquare

/-! # Original total-space geometry of an ordinary chart

The original site square transports the given test arrow. Its original
representative projection is a base change of the unchanged base chart map.
Both projection equations and the cartesian square are proved before any
coefficient sheaf or cohomological comparison is supplied.
-/

@[expose] public noncomputable section
open CategoryTheory Limits

private theorem project_two {C : Type*} [Category* C]
    {A B D E F G H : C} (m : A ⟶ B) (i : B ⟶ D) (p : D ⟶ E)
    (q : E ⟶ F) (r : B ⟶ G) (s : G ⟶ F) (t : A ⟶ H) (b : H ⟶ G)
    (hi : i ≫ p ≫ q = r ≫ s) (hm : m ≫ r = t ≫ b) :
    ((m ≫ i) ≫ p) ≫ q = t ≫ b ≫ s := by
  rw [Category.assoc, Category.assoc, hi, ← Category.assoc, hm, Category.assoc]

private theorem project_one {C : Type*} [Category* C]
    {A B D E F : C} (m : A ⟶ B) (p : B ⟶ D) (q : D ⟶ E)
    (r : B ⟶ F) (s : F ⟶ E) (t : A ⟶ F)
    (hp : p ≫ q = r ≫ s) (hm : m ≫ r = t) :
    (m ≫ p) ≫ q = t ≫ s := by
  rw [Category.assoc, hp, ← Category.assoc, hm]

namespace AlgebraicGeometry.Scheme.EtaleCohomology.SmoothBaseChange
open Continuity
universe u

variable {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
variable {V : S.Etale} {T : S'.Etale} (a : T ⟶ (siteBaseChange g).obj V)

/-- The unique original total-space test induced by the native site square. -/
def ordinaryChartTotalTest :
    (siteBaseChange (pullback.fst g f)).obj T ⟶
      (siteBaseChange (pullback.snd g f)).obj ((siteBaseChange f).obj V) :=
  (siteBaseChange (pullback.fst g f)).map a ≫
    (siteBaseChangeSquareIso f (pullback.fst g f) g (pullback.snd g f)
      pullback.condition).hom.app V

/-- The original total chart projection retains the original base chart map. -/
theorem ordinaryChartTotalTest_fst :
    (unitRepresentativeArrow (pullback.snd g f) (ordinaryChartTotalTest f g a)).left ≫
        pullback.fst V.hom f =
      pullback.fst T.hom (pullback.fst g f) ≫ (unitRepresentativeArrow g a).left := by
  change ((((siteBaseChange (pullback.fst g f)).map a).left ≫
      ((siteBaseChangeSquareIso f (pullback.fst g f) g (pullback.snd g f)
        pullback.condition).hom.app V).left) ≫
      pullback.fst (pullback.snd V.hom f) (pullback.snd g f)) ≫
        pullback.fst V.hom f = _
  exact project_two
    ((siteBaseChange (pullback.fst g f)).map a).left
    ((siteBaseChangeSquareIso f (pullback.fst g f) g (pullback.snd g f)
      pullback.condition).hom.app V).left _ _ _ _ _ a.left
    (siteBaseChangeSquareIso_fst_fst f (pullback.fst g f) g (pullback.snd g f)
      pullback.condition V)
    (siteBaseChange_map_fst (pullback.fst g f) a)

/-- The structural projection is the original total-space projection. -/
theorem ordinaryChartTotalTest_snd :
    (unitRepresentativeArrow (pullback.snd g f) (ordinaryChartTotalTest f g a)).left ≫
        pullback.snd V.hom f =
      pullback.snd T.hom (pullback.fst g f) ≫ pullback.snd g f := by
  let aX := ordinaryChartTotalTest f g a
  have hw : aX.left ≫ pullback.snd (pullback.snd V.hom f) (pullback.snd g f) =
      pullback.snd T.hom (pullback.fst g f) := MorphismProperty.Over.w aX
  change (aX.left ≫ pullback.fst (pullback.snd V.hom f) (pullback.snd g f)) ≫
    pullback.snd V.hom f = _
  exact project_one aX.left _ _ _ _ _ pullback.condition hw

/-- The unchanged total representative arrow is a genuine base change of the
unchanged base representative arrow, in the actual native pullback square. -/
theorem ordinaryChartTotalTest_isPullback :
    IsPullback
      (unitRepresentativeArrow (pullback.snd g f) (ordinaryChartTotalTest f g a)).left
      (pullback.fst T.hom (pullback.fst g f)) (pullback.fst V.hom f)
      (unitRepresentativeArrow g a).left := by
  have H : IsPullback
      (pullback.snd T.hom (pullback.fst g f) ≫ pullback.snd g f)
      (pullback.fst T.hom (pullback.fst g f)) f (T.hom ≫ g) :=
    (IsPullback.of_hasPullback T.hom (pullback.fst g f)).flip.paste_horiz
      (IsPullback.of_hasPullback g f).flip
  have hp : (unitRepresentativeArrow g a).left ≫ V.hom = T.hom ≫ g :=
    Over.w (unitRepresentativeArrow g a)
  have H' : IsPullback
      ((unitRepresentativeArrow (pullback.snd g f) (ordinaryChartTotalTest f g a)).left ≫
        pullback.snd V.hom f)
      (pullback.fst T.hom (pullback.fst g f)) f
      ((unitRepresentativeArrow g a).left ≫ V.hom) := by
    rw [ordinaryChartTotalTest_snd, hp]
    exact H
  exact H'.of_right (ordinaryChartTotalTest_fst f g a)
    (IsPullback.of_hasPullback V.hom f).flip

end AlgebraicGeometry.Scheme.EtaleCohomology.SmoothBaseChange
