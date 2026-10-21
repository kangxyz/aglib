/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.RelativePicard.DegreeZero
public import Aglib.AlgebraicGeometry.Curves.RiemannHurwitz
public import Aglib.AlgebraicGeometry.Curves.Picard.Degree.ProperCurveProductFormula
public import Aglib.AlgebraicGeometry.Curves.Picard.NormDegree.OrderFormula
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.Normality
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.Dimension
public import Aglib.AlgebraicGeometry.Properties.Normal.Components
public import Aglib.AlgebraicGeometry.Modules.BaseChange.Affine
public import Aglib.AlgebraicGeometry.Morphisms.FiniteFlat.GeometricDegreeRank

/-!
# Pullback of normalized degree-zero classes between pointed curves

The original map `f × id` pulls normalized Picard classes back when `f`
preserves the given origins. For finite etale surjective curve maps, native
degree scaling preserves degree zero on every geometric fibre. The resulting
additive map is natural on arbitrary test schemes.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.RelativePicard.Classes

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve.RelativePicard

attribute [local instance] Over.cartesianMonoidalCategory

local notation "degree" => curveDegree smoothFieldNormality normalComponentsOpen
  smoothFieldRegularity smoothClosedPointDimension smoothFieldDimension
  Picard.Degree.properCurveProductFormula

local notation "zeroGroup" => degreeZeroGroup smoothFieldNormality normalComponentsOpen
  smoothFieldRegularity smoothClosedPointDimension smoothFieldDimension
  Picard.Degree.properCurveProductFormula moduleTensorPullback

local notation "zeroMap" => degreeZeroMap smoothFieldNormality normalComponentsOpen
  smoothFieldRegularity smoothClosedPointDimension smoothFieldDimension
  Picard.Degree.properCurveProductFormula moduleTensorPullback

variable {k : Type u} [Field k] {X Y : FScheme k} (f : X ⟶ Y)

/-- The first-coordinate family map is the actual base change of `f`. -/
theorem curveMapFamily_isPullback (T : FScheme k) :
    IsPullback (fst X T).left (f ▷ T).left f.left (fst Y T).left := by
  apply IsPullback.flip
  apply IsPullback.of_right (h₁₂ := (snd Y T).left) (h₂₂ := Y.hom) (v₁₃ := T.hom)
    _ (congrArg Over.Hom.left (whiskerRight_fst f T))
    (IsPullback.of_hasPullback Y.hom T.hom).flip
  have hsecond : (f ▷ T).left ≫ (snd Y T).left = (snd X T).left :=
    congrArg Over.Hom.left (whiskerRight_snd f T)
  rw [hsecond, Over.w]
  exact (IsPullback.of_hasPullback X.hom T.hom).flip

/-- First-coordinate curve pullback commutes with every map of tests. -/
theorem curveMapFamily_naturality {T T' : FScheme k} (a : T' ⟶ T) :
    familyMap X.hom T.hom T'.hom a.left (Over.w a) ≫ (f ▷ T).left =
      (f ▷ T').left ≫ familyMap Y.hom T.hom T'.hom a.left (Over.w a) := by
  change ((X ◁ a) ≫ (f ▷ T)).left = ((f ▷ T') ≫ (Y ◁ a)).left
  apply congrArg Over.Hom.left
  apply CartesianMonoidalCategory.hom_ext <;>
    simp only [Category.assoc, whiskerRight_fst, whiskerRight_snd,
      whiskerLeft_fst, whiskerLeft_snd, whiskerLeft_fst_assoc, whiskerRight_snd_assoc]

variable (oX : 𝟙_ (FScheme k) ⟶ X) (oY : 𝟙_ (FScheme k) ⟶ Y)
variable (ho : oX ≫ f = oY)

include ho in
/-- The actual origin section commutes with the pointed curve map. -/
theorem curveMapFamily_origin (T : FScheme k) :
    Scheme.RelativePicard.originSection X.hom oX.left (Over.w oX) T ≫ (f ▷ T).left =
      Scheme.RelativePicard.originSection Y.hom oY.left (Over.w oY) T := by
  change (lift (toUnit T ≫ oX) (𝟙 T) ≫ (f ▷ T)).left =
    (lift (toUnit T ≫ oY) (𝟙 T)).left
  apply congrArg Over.Hom.left
  apply CartesianMonoidalCategory.hom_ext <;>
    simp only [Category.assoc, whiskerRight_fst, whiskerRight_snd, lift_fst, lift_snd,
      lift_fst_assoc, ho]

/-- Pullback on the actual normalized Picard subgroups. -/
def normalizedCurvePullback (T : FScheme k) :
    normalizedGroup moduleTensorPullback Y.hom oY.left (Over.w oY) T →+
      normalizedGroup moduleTensorPullback X.hom oX.left (Over.w oX) T where
  toFun a := ⟨pullbackClass (f ▷ T).left a.val, by
    change pullbackClass (Scheme.RelativePicard.originSection X.hom oX.left (Over.w oX) T)
      (pullbackClass (f ▷ T).left a.val) = 0
    rw [← pullbackClass_comp, curveMapFamily_origin f oX oY ho T]
    exact a.property⟩
  map_zero' := by apply Subtype.ext; exact pullbackClass_zero _
  map_add' a b := by apply Subtype.ext; exact pullbackClass_add moduleTensorPullback _ _ _

@[simp] theorem normalizedCurvePullback_val (T : FScheme k)
    (a : normalizedGroup moduleTensorPullback Y.hom oY.left (Over.w oY) T) :
    (normalizedCurvePullback f oX oY ho T a).val = pullbackClass (f ▷ T).left a.val := rfl

variable (hX : Properties X) (hY : Properties Y)

/-- Native degree zero is preserved by an actual finite etale surjective
map of smooth proper geometrically connected curves. -/
theorem curveDegree_pullback_zero [IsFinite f.left] [Etale f.left] [Surjective f.left]
    (a : PicardGroup Y.left) (ha : degree Y hY a = 0) :
    degree X hX (pullbackClass f.left a) = 0 := by
  let : ConnectedSpace Y.left := curveProperties_connectedSpace hY
  obtain ⟨n, hn⟩ := exists_hasLocallyFreeRank f.left
    (finiteLocallyFree_of_finite_etale finiteFlatPresentationLocallyFree f.left)
  have h := curveDegree_pullback_of_hasLocallyFreeRank smoothFieldNormality normalComponentsOpen
    smoothFieldRegularity smoothClosedPointDimension smoothFieldDimension
    Picard.Degree.properCurveProductFormula Scheme.Modules.affineModuleBaseChange
    FiniteFlat.finiteDominantGenericFibre Picard.NormDegree.finiteMorphismNormOrder
    f hX hY n hn a
  simpa only [ha, mul_zero] using h

variable [IsFinite f.left] [Etale f.left] [Surjective f.left]

/-- Actual fibrewise degree zero is preserved under first-coordinate
pullback, for every test scheme and every structural field map. -/
theorem fibreDegree_curvePullback_zero (T : FScheme k)
    (a : zeroGroup Y hY oY.left (Over.w oY) T)
    (K : Type u) [Field K] [IsAlgClosed K] (s : Spec (.of K) ⟶ Base k)
    (t : Over.mk s ⟶ T) :
    fibreDegree smoothFieldNormality normalComponentsOpen smoothFieldRegularity
      smoothClosedPointDimension smoothFieldDimension Picard.Degree.properCurveProductFormula
      moduleTensorPullback X hX T K s t (pullbackClass (f ▷ T).left a.val.val) = 0 := by
  let X' : FScheme K := Over.mk (pullback.snd X.hom s)
  let Y' : FScheme K := Over.mk (pullback.snd Y.hom s)
  let f' : X' ⟶ Y' := Over.homMk (f ▷ Over.mk s).left
    (congrArg Over.Hom.left (whiskerRight_snd f (Over.mk s)))
  have hSquare := curveMapFamily_isPullback f (Over.mk s)
  let : IsFinite f'.left := MorphismProperty.of_isPullback hSquare inferInstance
  let : Etale f'.left := MorphismProperty.of_isPullback hSquare inferInstance
  let : Surjective f'.left := MorphismProperty.of_isPullback hSquare inferInstance
  dsimp only [fibreDegree, AddMonoidHom.comp_apply, pullbackHom_apply]
  have hc := congrArg (fun m : (X ⊗ Over.mk s).left ⟶ (Y ⊗ T).left =>
    pullbackClass m (show PicardGroup (Y ⊗ T).left from a.val.val))
    (curveMapFamily_naturality f t)
  have hp := (pullbackClass_comp (familyMap X.hom T.hom s t.left (Over.w t))
    (f ▷ T).left a.val.val).symm.trans
      (hc.trans (pullbackClass_comp (f ▷ Over.mk s).left
        (familyMap Y.hom T.hom s t.left (Over.w t)) a.val.val))
  exact (congrArg (degree X' (curveProperties_baseChange hX K s)) hp).trans
    (curveDegree_pullback_zero f' (curveProperties_baseChange hX K s)
      (curveProperties_baseChange hY K s) _ (a.property K s t))

/-- The stated geometric degree is the actual degree multiplier on every
geometric fibre of every test family. -/
theorem fibreDegree_curvePullback (n : ℕ) (hn : HasGeometricDegree f n) (T : FScheme k)
    (a : PicardGroup (Y ⊗ T).left)
    (K : Type u) [Field K] (s : Spec (.of K) ⟶ Base k)
    (t : Over.mk s ⟶ T) :
    fibreDegree smoothFieldNormality normalComponentsOpen smoothFieldRegularity
      smoothClosedPointDimension smoothFieldDimension Picard.Degree.properCurveProductFormula
      moduleTensorPullback X hX T K s t (pullbackClass (f ▷ T).left a) =
    (n : ℤ) * fibreDegree smoothFieldNormality normalComponentsOpen smoothFieldRegularity
      smoothClosedPointDimension smoothFieldDimension Picard.Degree.properCurveProductFormula
      moduleTensorPullback Y hY T K s t a := by
  let X' : FScheme K := Over.mk (pullback.snd X.hom s)
  let Y' : FScheme K := Over.mk (pullback.snd Y.hom s)
  let f' : X' ⟶ Y' := Over.homMk (f ▷ Over.mk s).left
    (congrArg Over.Hom.left (whiskerRight_snd f (Over.mk s)))
  have hSquare := curveMapFamily_isPullback f (Over.mk s)
  let : IsFinite f'.left := MorphismProperty.of_isPullback hSquare inferInstance
  let : Etale f'.left := MorphismProperty.of_isPullback hSquare inferInstance
  let : Surjective f'.left := MorphismProperty.of_isPullback hSquare inferInstance
  have hfree := finiteLocallyFree_of_finite_etale finiteFlatPresentationLocallyFree f'.left
  have hrank : HasLocallyFreeRank f'.left n := by
    apply (hasLocallyFreeRank_iff_rank_eq f'.left hfree n).mpr
    intro y
    exact (FiniteFlat.nativeRank_eq_locallyFreeRank f'.left
      Scheme.Modules.affineModuleBaseChange y).symm.trans
      ((Scheme.Hom.finrank_of_isPullback _ _ _ _ hSquare y).trans
        (nativeRank_eq_of_hasGeometricDegree f n hn ((fst Y (Over.mk s)).left y)))
  have hscale := curveDegree_pullback_of_hasLocallyFreeRank smoothFieldNormality
    normalComponentsOpen smoothFieldRegularity smoothClosedPointDimension smoothFieldDimension
    Picard.Degree.properCurveProductFormula Scheme.Modules.affineModuleBaseChange
    FiniteFlat.finiteDominantGenericFibre Picard.NormDegree.finiteMorphismNormOrder
    f' (curveProperties_baseChange hX K s) (curveProperties_baseChange hY K s) n hrank
    (pullbackClass (familyMap Y.hom T.hom s t.left (Over.w t)) a)
  dsimp only [fibreDegree, AddMonoidHom.comp_apply, pullbackHom_apply]
  have hc := congrArg (fun m : (X ⊗ Over.mk s).left ⟶ (Y ⊗ T).left => pullbackClass m a)
    (curveMapFamily_naturality f t)
  have hp := (pullbackClass_comp (familyMap X.hom T.hom s t.left (Over.w t))
    (f ▷ T).left a).symm.trans
      (hc.trans (pullbackClass_comp (f ▷ Over.mk s).left
        (familyMap Y.hom T.hom s t.left (Over.w t)) a))
  exact (congrArg (degree X' (curveProperties_baseChange hX K s)) hp).trans hscale

/-- Pullback between the original normalized degree-zero Picard groups.
The homomorphism is literally pullback by `f × id` on underlying classes. -/
def degreeZeroCurvePullback (T : FScheme k) :
    zeroGroup Y hY oY.left (Over.w oY) T →+ zeroGroup X hX oX.left (Over.w oX) T where
  toFun a := ⟨normalizedCurvePullback f oX oY ho T a.val, by
    intro K _ _ s t
    exact fibreDegree_curvePullback_zero f oY hX hY T a K s t⟩
  map_zero' := by apply Subtype.ext; exact map_zero _
  map_add' a b := by apply Subtype.ext; exact map_add _ _ _

@[simp] theorem degreeZeroCurvePullback_val (T : FScheme k)
    (a : zeroGroup Y hY oY.left (Over.w oY) T) :
    (degreeZeroCurvePullback f oX oY ho hX hY T a).val.val =
      pullbackClass (f ▷ T).left a.val.val := rfl

/-- The cross-curve pullback commutes with all maps of test schemes,
on the actual normalized degree-zero classes. -/
theorem degreeZeroCurvePullback_naturality {T T' : FScheme k} (t : T' ⟶ T)
    (a : zeroGroup Y hY oY.left (Over.w oY) T) :
    zeroMap X hX oX.left (Over.w oX) t (degreeZeroCurvePullback f oX oY ho hX hY T a) =
      degreeZeroCurvePullback f oX oY ho hX hY T'
        (zeroMap Y hY oY.left (Over.w oY) t a) := by
  apply Subtype.ext
  apply Subtype.ext
  change pullbackClass (familyMap X.hom T.hom T'.hom t.left (Over.w t))
      (pullbackClass (f ▷ T).left a.val.val) =
    pullbackClass (f ▷ T').left
      (pullbackClass (familyMap Y.hom T.hom T'.hom t.left (Over.w t)) a.val.val)
  rw [← pullbackClass_comp, curveMapFamily_naturality, pullbackClass_comp]

end AlgebraicGeometry.Scheme.OverField.Curve.RelativePicard
