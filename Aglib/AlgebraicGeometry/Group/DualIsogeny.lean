/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.RelativePicard.Pullback
public import Aglib.AlgebraicGeometry.Curves.SmoothGeometry
public import Aglib.AlgebraicGeometry.Group.PointDivisor
public import Aglib.AlgebraicGeometry.Group.MultiplicationDegree
public import Aglib.AlgebraicGeometry.Group.EtaleQuotient

/-!
# The actual Picard pullback morphism of a curve isogeny

Pullback of the existing normalized Abel class is inverted by the actual
evaluation divisor on the locally Noetherian target curve. This constructs
a morphism on the original schemes, identifies its action on every test
scheme, and proves that it preserves the original group laws.

The coherent-genus-one premise is native and explicit. No Picard representing
witness or identification from multiplication triangles is assumed.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.OverField.Curve

universe u

namespace AlgebraicGeometry.Scheme.Group.DualIsogeny

attribute [local instance] Over.cartesianMonoidalCategory

local notation "zeroMap" => Curve.RelativePicard.degreeZeroMap smoothFieldNormality
  normalComponentsOpen smoothFieldRegularity smoothClosedPointDimension smoothFieldDimension
  Curve.Picard.Degree.properCurveProductFormula moduleTensorPullback

variable {k : Type u} [Field k]

private theorem pointClass_naturality (G : Grp (FScheme k)) (hG : Curve.Properties G.X)
    {T T' : FScheme k} (t : T' ⟶ T) (a : T ⟶ G.X) :
    PointDivisor.degreeZeroPointClass G hG T' (t ≫ a) =
      zeroMap G.X hG η[G.X].left (Over.w _) t (PointDivisor.degreeZeroPointClass G hG T a) :=
  Curve.Abel.degreeZeroAbelClass_naturality smoothFieldNormality normalComponentsOpen
    smoothFieldRegularity smoothClosedPointDimension smoothFieldDimension
    Curve.Picard.Degree.properCurveProductFormula moduleTensorPullback
    Curve.Abel.FiniteCartierDegree.finiteCartierIdealDegree relativeCartierIdealBaseChange
    smoothRelativeDivisorIdeal G.X hG η[G.X].left (Over.w _) t a

private theorem pointClass_origin (G : Grp (FScheme k)) (hG : Curve.Properties G.X) :
    PointDivisor.degreeZeroPointClass G hG (𝟙_ (FScheme k)) η[G.X] = 0 := by
  have h := Curve.Abel.degreeZeroAbelClass_origin smoothFieldNormality normalComponentsOpen
    smoothFieldRegularity smoothClosedPointDimension smoothFieldDimension
    Curve.Picard.Degree.properCurveProductFormula moduleTensorPullback G.X hG
    Curve.Abel.FiniteCartierDegree.finiteCartierIdealDegree smoothRelativeDivisorIdeal
    relativeCartierIdealBaseChange η[G.X].left (Over.w _) (𝟙_ (FScheme k))
  have ho : Curve.Abel.originPoint G.X.hom η[G.X].left (Over.w _)
      (𝟙_ (FScheme k)) = η[G.X] := by
    apply Over.OverMorphism.ext
    change (𝟙 (Base k)) ≫ η[G.X].left = η[G.X].left
    exact Category.id_comp _
  simpa only [ho] using h

private theorem pointClass_injective (G : Grp (FScheme k)) (hG : Curve.Properties G.X)
    (hg : coherentGenus k G.X = 1) (T : FScheme k) [IsReduced T.left] :
    Function.Injective (PointDivisor.degreeZeroPointClass G hG T) :=
  PointDivisor.pointClass_injective_of_isReduced smoothFieldNormality normalComponentsOpen
    smoothFieldRegularity smoothClosedPointDimension smoothFieldDimension
    Curve.Picard.Degree.properCurveProductFormula moduleTensorPullback
    Curve.Abel.FiniteCartierDegree.finiteCartierIdealDegree relativeCartierIdealBaseChange
    smoothRelativeDivisorIdeal Curve.Picard.NormDegree.finiteMorphismNormOrder
    Cohomology.properStructureCohomologyBaseChange lineBundleRiemannRoch
    lineBundleHighDegreeVanishing Cohomology.noetherianSheafCohomologyVanishing G.X hG η[G.X]
    hg T

variable {E D : Grp (FScheme k)} (f : E ⟶ D)
variable (hE : Curve.Properties E.X) (hD : Curve.Properties D.X)
variable [IsFinite f.hom.hom.left] [Etale f.hom.hom.left] [Surjective f.hom.hom.left]

/-- Pullback by the original isogeny on normalized degree-zero classes,
over an arbitrary test scheme. -/
abbrev picardPullback (T : FScheme k) :=
  Curve.RelativePicard.degreeZeroCurvePullback f.hom.hom η[E.X] η[D.X]
    (IsMonHom.one_hom f.hom.hom) hE hD T

variable (hgE : coherentGenus k E.X = 1)

/-- The actual Picard-dual morphism, obtained from the evaluation-divisor
inverse of the pulled-back normalized diagonal class. -/
def picardDualMorphism : D.X ⟶ E.X := by
  let : SmoothOfRelativeDimension 1 E.X.hom := hE.smooth
  let : IsProper E.X.hom := hE.proper
  let : LocallyOfFiniteType D.X.hom := curveProperties_locallyOfFiniteType hD
  let : IsLocallyNoetherian D.X.left := LocallyOfFiniteType.isLocallyNoetherian D.X.hom
  exact Curve.Abel.inverseCandidate smoothFieldNormality normalComponentsOpen smoothFieldRegularity
    smoothClosedPointDimension smoothFieldDimension Curve.Picard.Degree.properCurveProductFormula
    moduleTensorPullback Curve.Abel.FiniteCartierDegree.finiteCartierIdealDegree
    relativeCartierIdealBaseChange smoothRelativeDivisorIdeal
    Curve.Picard.NormDegree.finiteMorphismNormOrder Cohomology.properStructureCohomologyBaseChange
    lineBundleRiemannRoch lineBundleHighDegreeVanishing
    Cohomology.noetherianSheafCohomologyVanishing
    E.X hE η[E.X].left (Over.w _) hgE D.X
    (picardPullback f hE hD D.X (PointDivisor.degreeZeroPointClass D hD D.X (𝟙 D.X)))
    fibrewiseRegularLineBundle smoothRelativeCartierLocality

/-- The constructed morphism recovers the actual pulled-back universal
Abel class on the target curve itself. -/
theorem picardDualMorphism_class :
    PointDivisor.degreeZeroPointClass E hE D.X (picardDualMorphism f hE hD hgE) =
      picardPullback f hE hD D.X (PointDivisor.degreeZeroPointClass D hD D.X (𝟙 D.X)) := by
  let : SmoothOfRelativeDimension 1 E.X.hom := hE.smooth
  let : IsProper E.X.hom := hE.proper
  let : LocallyOfFiniteType D.X.hom := curveProperties_locallyOfFiniteType hD
  let : IsLocallyNoetherian D.X.left := LocallyOfFiniteType.isLocallyNoetherian D.X.hom
  exact Curve.Abel.inverseCandidate_class smoothFieldNormality normalComponentsOpen
    smoothFieldRegularity smoothClosedPointDimension smoothFieldDimension
    Curve.Picard.Degree.properCurveProductFormula moduleTensorPullback
    Curve.Abel.FiniteCartierDegree.finiteCartierIdealDegree relativeCartierIdealBaseChange
    smoothRelativeDivisorIdeal Curve.Picard.NormDegree.finiteMorphismNormOrder
    Cohomology.properStructureCohomologyBaseChange lineBundleRiemannRoch
    lineBundleHighDegreeVanishing Cohomology.noetherianSheafCohomologyVanishing
    E.X hE η[E.X].left (Over.w _) hgE D.X
    (picardPullback f hE hD D.X (PointDivisor.degreeZeroPointClass D hD D.X (𝟙 D.X)))
    fibrewiseRegularLineBundle smoothRelativeCartierLocality

/-- On every test scheme, the constructed dual map is the actual Picard
pullback under the original point/divisor maps. -/
theorem picardDualMorphism_pointClass (T : FScheme k) (a : T ⟶ D.X) :
    PointDivisor.degreeZeroPointClass E hE T (a ≫ picardDualMorphism f hE hD hgE) =
      picardPullback f hE hD T (PointDivisor.degreeZeroPointClass D hD T a) := by
  rw [pointClass_naturality, picardDualMorphism_class]
  rw [Curve.RelativePicard.degreeZeroCurvePullback_naturality]
  rw [← pointClass_naturality, Category.comp_id]

/-- The evaluation-divisor dual preserves the actual identity sections. -/
theorem picardDualMorphism_pointed :
    η[D.X] ≫ picardDualMorphism f hE hD hgE = η[E.X] := by
  let : IsReduced (𝟙_ (FScheme k)).left := by
    change IsReduced (Spec (.of k))
    infer_instance
  apply pointClass_injective E hE hgE (𝟙_ (FScheme k))
  rw [picardDualMorphism_pointClass, pointClass_origin, map_zero, pointClass_origin]

/-- The actual Picard-dual group morphism on the original curves. -/
def picardDualHom : D ⟶ E := by
  let : IsMonHom (picardDualMorphism f hE hD hgE) :=
    Curve.pointedMorphism_of_curveProperties D E hD hE _
      (picardDualMorphism_pointed f hE hD hgE)
  exact Grp.ofHom (picardDualMorphism f hE hD hgE)

/-- The actual Picard pullback comparison for the constructed group map. -/
theorem picardDualHom_pointClass (T : FScheme k) (a : T ⟶ D.X) :
    PointDivisor.degreeZeroPointClass E hE T (a ≫ (picardDualHom f hE hD hgE).hom.hom) =
      picardPullback f hE hD T (PointDivisor.degreeZeroPointClass D hD T a) :=
  picardDualMorphism_pointClass f hE hD hgE T a

/-- The actual normalized Picard pullback identifies the dual morphism
uniquely. This criterion does not replace its hypothesis by multiplication
triangles. -/
theorem picardDualMorphism_unique (g : D.X ⟶ E.X)
    (hg : PointDivisor.degreeZeroPointClass E hE D.X g =
      picardPullback f hE hD D.X (PointDivisor.degreeZeroPointClass D hD D.X (𝟙 D.X))) :
    g = picardDualMorphism f hE hD hgE := by
  let : IsIntegral D.X.left := hD.isIntegral
  apply pointClass_injective E hE hgE D.X
  exact hg.trans (picardDualMorphism_class f hE hD hgE).symm

end AlgebraicGeometry.Scheme.Group.DualIsogeny

namespace AlgebraicGeometry.Scheme.Group.DualIsogeny

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k] (G : Grp (FScheme k))
variable [SmoothOfRelativeDimension 1 G.X.hom] [IsSeparated G.X.hom]

/-- Evaluation of the actual normalized diagonal class on two scheme-valued
points. Its value is a line-bundle class on the test scheme. -/
def poincareClass (T : FScheme k) (a b : T ⟶ G.X) : PicardGroup T.left :=
  pullbackClass (lift a b).left (Multiplication.normalizedDiagonalClass G)

theorem poincareClass_comp {T T' : FScheme k} (t : T' ⟶ T) (a b : T ⟶ G.X) :
    pullbackClass t.left (poincareClass G T a b) =
      poincareClass G T' (t ≫ a) (t ≫ b) := by
  rw [poincareClass, ← pullbackClass_comp, ← Over.comp_left, comp_lift]
  rfl

theorem poincareClass_swap (T : FScheme k) (a b : T ⟶ G.X) :
    poincareClass G T a b = poincareClass G T b a :=
  Multiplication.normalizedDiagonalClass_lift_swap G T a b

theorem poincareClass_one_right (T : FScheme k) (a : T ⟶ G.X) :
    poincareClass G T a 1 = 0 := by
  have hd : lift a (1 : T ⟶ G.X) ≫ Multiplication.difference G = a := by
    simp only [Multiplication.difference, GrpObj.comp_div, lift_fst, lift_snd, div_one]
  change (pullbackHom moduleTensorPullback (lift a (1 : T ⟶ G.X)).left)
    (-pullbackClass (Multiplication.difference G).left (Multiplication.identityIdealClass G) +
      pullbackClass (fst G.X G.X).left (Multiplication.identityIdealClass G) +
      pullbackClass (snd G.X G.X).left (Multiplication.identityIdealClass G)) = 0
  rw [map_add, map_add, map_neg]
  simp only [pullbackHom_apply, ← pullbackClass_comp, ← Over.comp_left, hd, lift_fst, lift_snd,
    Multiplication.pullback_identityIdealClass_one, neg_add_cancel, add_zero]

theorem poincareClass_one_left (T : FScheme k) (b : T ⟶ G.X) :
    poincareClass G T 1 b = 0 := by
  rw [poincareClass_swap, poincareClass_one_right]

theorem pointClass_val (hG : Curve.Properties G.X) (T : FScheme k) (a : T ⟶ G.X) :
    (PointDivisor.degreeZeroPointClass G hG T a).val.val =
      pullbackClass (G.X ◁ a).left (Multiplication.normalizedDiagonalClass G) := by
  have h := pointClass_naturality G hG a (𝟙 G.X)
  rw [Category.comp_id] at h
  have h' := congrArg (fun b => b.val.val) h
  change (PointDivisor.degreeZeroPointClass G hG T a).val.val =
    pullbackClass (G.X ◁ a).left
      (PointDivisor.degreeZeroPointClass G hG G.X (𝟙 G.X)).val.val at h'
  simpa only [Multiplication.degreeZeroPointClass_id_val] using h'

theorem poincareClass_mul_right [IsAlgClosed k] (hG : Curve.Properties G.X)
    (hg : coherentGenus k G.X = 1) (T : FScheme k) (a b c : T ⟶ G.X) :
    poincareClass G T a (b * c) = poincareClass G T a b + poincareClass G T a c := by
  have h := congrArg (fun z => z.val.val) (PointDivisor.degreeZeroPointClass_mul G hG hg T b c)
  change (PointDivisor.degreeZeroPointClass G hG T (b * c)).val.val =
    (PointDivisor.degreeZeroPointClass G hG T b).val.val +
      (PointDivisor.degreeZeroPointClass G hG T c).val.val at h
  rw [pointClass_val, pointClass_val, pointClass_val] at h
  have h' := congrArg (pullbackHom moduleTensorPullback (lift a (𝟙 T)).left) h
  rw [map_add] at h'
  have hc (z : T ⟶ G.X) : lift a (𝟙 T) ≫ (G.X ◁ z) = lift a z := by
    apply CartesianMonoidalCategory.hom_ext <;>
      simp only [Category.assoc, whiskerLeft_fst, whiskerLeft_snd, lift_fst, lift_snd,
        lift_snd_assoc, Category.id_comp]
  simpa only [pullbackHom_apply, ← pullbackClass_comp, ← Over.comp_left, hc, poincareClass]
    using h'

theorem poincareClass_mul_left [IsAlgClosed k] (hG : Curve.Properties G.X)
    (hg : coherentGenus k G.X = 1) (T : FScheme k) (a b c : T ⟶ G.X) :
    poincareClass G T (a * b) c = poincareClass G T a c + poincareClass G T b c := by
  rw [poincareClass_swap G T (a * b) c, poincareClass_mul_right G hG hg,
    poincareClass_swap G T c a, poincareClass_swap G T c b]

/-- The line-bundle-valued pairing is additive in its first point. -/
def poincareLeftHom [IsAlgClosed k] (hG : Curve.Properties G.X)
    (hg : coherentGenus k G.X = 1) (T : FScheme k) (b : T ⟶ G.X) :
    Additive (T ⟶ G.X) →+ PicardGroup T.left where
  toFun a := poincareClass G T a.toMul b
  map_zero' := poincareClass_one_left G T b
  map_add' a c := poincareClass_mul_left G hG hg T a.toMul c.toMul b

/-- The difference cross-effect on the original Picard group. The inverse
in the third term is essential for arbitrary degree-zero line bundles. -/
def picardCrossEffect : PicardGroup G.X.left →+ PicardGroup (G.X ⊗ G.X).left where
  toFun L := -pullbackClass (Multiplication.difference G).left L +
    pullbackClass (fst G.X G.X).left L + pullbackClass ((snd G.X G.X) ≫ ι[G.X]).left L
  map_zero' := by simp only [pullbackClass_zero, neg_zero, add_zero]
  map_add' L M := by
    simp only [pullbackClass_add moduleTensorPullback]
    abel

theorem picardCrossEffect_identityIdeal :
    picardCrossEffect G (Multiplication.identityIdealClass G) =
      Multiplication.normalizedDiagonalClass G := by
  change -pullbackClass (Multiplication.difference G).left (Multiplication.identityIdealClass G) +
    pullbackClass (fst G.X G.X).left (Multiplication.identityIdealClass G) +
      pullbackClass ((snd G.X G.X) ≫ ι[G.X]).left (Multiplication.identityIdealClass G) = _
  rw [Over.comp_left, pullbackClass_comp, Multiplication.pullback_identityIdealClass_inv]
  rfl

/-- Every actual point class has zero difference cross-effect. This uses
the proved bilinearity of the normalized diagonal class. -/
theorem picardCrossEffect_point [IsAlgClosed k] (hG : Curve.Properties G.X)
    (hg : coherentGenus k G.X = 1) (q : 𝟙_ (FScheme k) ⟶ G.X) :
    picardCrossEffect G (poincareClass G G.X (𝟙 G.X) (toUnit G.X ≫ q)) = 0 := by
  change -pullbackClass (Multiplication.difference G).left
      (poincareClass G G.X (𝟙 G.X) (toUnit G.X ≫ q)) +
    pullbackClass (fst G.X G.X).left (poincareClass G G.X (𝟙 G.X) (toUnit G.X ≫ q)) +
    pullbackClass ((snd G.X G.X) ≫ ι[G.X]).left
      (poincareClass G G.X (𝟙 G.X) (toUnit G.X ≫ q)) = 0
  rw [poincareClass_comp, poincareClass_comp, poincareClass_comp]
  simp only [Category.comp_id, ← Category.assoc, comp_toUnit]
  let h := poincareLeftHom G hG hg (G.X ⊗ G.X) (toUnit (G.X ⊗ G.X) ≫ q)
  change -h (Additive.ofMul (fst G.X G.X / snd G.X G.X)) +
    h (Additive.ofMul (fst G.X G.X)) + h (Additive.ofMul ((snd G.X G.X)⁻¹)) = 0
  change -h (Additive.ofMul (fst G.X G.X) - Additive.ofMul (snd G.X G.X)) +
    h (Additive.ofMul (fst G.X G.X)) + h (-Additive.ofMul (snd G.X G.X)) = 0
  rw [map_sub, map_neg]
  abel

/-- The identity ideal in the actual family, as a first-projection pullback. -/
def familyIdentityClass (T : FScheme k) : PicardGroup (G.X ⊗ T).left :=
  pullbackClass (fst G.X T).left (Multiplication.identityIdealClass G)

theorem familyIdentityClass_eq_originIdeal (T : FScheme k) :
    familyIdentityClass G T = classOf _ (originIdealLineBundle smoothRelativeDivisorIdeal
      G.X.hom η[G.X].left (Over.w _) T.hom) := by
  have h := Curve.Abel.originIdealClass_baseChange smoothRelativeDivisorIdeal
    relativeCartierIdealBaseChange G.X.hom η[G.X].left (Over.w _) G.X.hom T.hom
    (T.hom ≫ η[G.X].left) (by rw [Category.assoc, Over.w, Over.tensorUnit_hom, Category.comp_id])
  rw [← Multiplication.pullback_identityIdealClass_fst G, ← pullbackClass_comp,
    Over.fst_left, familyMap_fst] at h
  exact h

theorem fibreDegree_familyIdentityClass (hG : Curve.Properties G.X) (T : FScheme k)
    (K : Type u) [Field K] (s : Spec (.of K) ⟶ Base k) (t : Over.mk s ⟶ T) :
    Curve.RelativePicard.fibreDegree smoothFieldNormality normalComponentsOpen
      smoothFieldRegularity smoothClosedPointDimension smoothFieldDimension
      Curve.Picard.Degree.properCurveProductFormula moduleTensorPullback G.X hG T K s t
      (familyIdentityClass G T) = -1 := by
  rw [familyIdentityClass_eq_originIdeal]
  exact Curve.Abel.fibreDegree_originIdeal G.X smoothRelativeDivisorIdeal η[G.X].left
    (Over.w _) T smoothFieldNormality normalComponentsOpen smoothFieldRegularity
    smoothClosedPointDimension smoothFieldDimension Curve.Picard.Degree.properCurveProductFormula
    moduleTensorPullback Curve.Abel.FiniteCartierDegree.finiteCartierIdealDegree
    relativeCartierIdealBaseChange hG K s t

theorem pointClass_unitor (hG : Curve.Properties G.X) (q : 𝟙_ (FScheme k) ⟶ G.X) :
    pullbackClass (ρ_ G.X).inv.left
      (PointDivisor.degreeZeroPointClass G hG (𝟙_ (FScheme k)) q).val.val =
      poincareClass G G.X (𝟙 G.X) (toUnit G.X ≫ q) := by
  rw [pointClass_val, ← pullbackClass_comp, ← Over.comp_left]
  have h : (ρ_ G.X).inv ≫ (G.X ◁ q) = lift (𝟙 G.X) (toUnit G.X ≫ q) := by
    apply CartesianMonoidalCategory.hom_ext <;>
      simp only [Category.assoc, whiskerLeft_fst, whiskerLeft_snd,
        rightUnitor_inv_fst, rightUnitor_inv_snd_assoc, lift_fst, lift_snd]
  rw [h]
  rfl

theorem familyIdentityClass_unitor :
    pullbackClass (ρ_ G.X).inv.left (familyIdentityClass G (𝟙_ (FScheme k))) =
      Multiplication.identityIdealClass G := by
  simp only [familyIdentityClass, ← pullbackClass_comp, ← Over.comp_left,
    rightUnitor_inv_fst, Over.id_left, pullbackClass_id]

end AlgebraicGeometry.Scheme.Group.DualIsogeny

namespace AlgebraicGeometry.Scheme.Group.DualIsogeny

attribute [local instance] Over.cartesianMonoidalCategory

local notation "zeroGroup" => Curve.RelativePicard.degreeZeroGroup smoothFieldNormality
  normalComponentsOpen smoothFieldRegularity smoothClosedPointDimension smoothFieldDimension
  Curve.Picard.Degree.properCurveProductFormula moduleTensorPullback

variable {k : Type u} [Field k] {E D : Grp (FScheme k)} (f : E ⟶ D)
variable [SmoothOfRelativeDimension 1 E.X.hom] [IsSeparated E.X.hom]
variable [SmoothOfRelativeDimension 1 D.X.hom] [IsSeparated D.X.hom]
variable [IsFinite f.hom.hom.left] [Etale f.hom.hom.left] [Surjective f.hom.hom.left]
variable (hE : Curve.Properties E.X) (hD : Curve.Properties D.X)
variable (n : ℕ) (hn : HasGeometricDegree f.hom.hom n)

/-- Subtracting the stated geometric degree times the identity ideal from
the pulled-back identity ideal gives an actual normalized degree-zero class.
Its geometric degree test uses the original all-field-map degree hypothesis. -/
def degreeCorrectionClass : zeroGroup E.X hE η[E.X].left (Over.w _) (𝟙_ (FScheme k)) := by
  let B := pullbackClass (f.hom.hom ▷ (𝟙_ (FScheme k))).left
      (familyIdentityClass D (𝟙_ (FScheme k))) - n • familyIdentityClass E (𝟙_ (FScheme k))
  refine ⟨⟨B, ?_⟩, ?_⟩
  · change pullbackClass
      (Scheme.RelativePicard.originSection E.X.hom η[E.X].left (Over.w _) (𝟙_ (FScheme k))) B = 0
    exact fieldPicard_eq_zero k _
  · intro K _ _ s t
    change (Curve.RelativePicard.fibreDegree smoothFieldNormality normalComponentsOpen
      smoothFieldRegularity smoothClosedPointDimension smoothFieldDimension
      Curve.Picard.Degree.properCurveProductFormula moduleTensorPullback E.X hE
      (𝟙_ (FScheme k)) K s t) B = 0
    dsimp only [B]
    rw [map_sub, map_nsmul,
      Curve.RelativePicard.fibreDegree_curvePullback f.hom.hom hE hD n hn,
      fibreDegree_familyIdentityClass, fibreDegree_familyIdentityClass]
    simp only [nsmul_eq_mul, sub_self]

omit [SmoothOfRelativeDimension 1 E.X.hom] [IsSeparated E.X.hom]
  [IsFinite f.hom.hom.left] [Etale f.hom.hom.left] [Surjective f.hom.hom.left] in
theorem familyIdentityClass_unitor_pullback :
    pullbackClass (ρ_ E.X).inv.left
      (pullbackClass (f.hom.hom ▷ (𝟙_ (FScheme k))).left
        (familyIdentityClass D (𝟙_ (FScheme k)))) =
      pullbackClass f.hom.hom.left (Multiplication.identityIdealClass D) := by
  have hc : (ρ_ E.X).inv ≫ (f.hom.hom ▷ (𝟙_ (FScheme k))) ≫
      fst D.X (𝟙_ (FScheme k)) = f.hom.hom := by
    rw [whiskerRight_fst, rightUnitor_inv_fst_assoc]
  have hcleft := congrArg Over.Hom.left hc
  calc
    _ = pullbackClass ((ρ_ E.X).inv.left ≫
        (f.hom.hom ▷ (𝟙_ (FScheme k))).left ≫ (fst D.X (𝟙_ (FScheme k))).left)
        (Multiplication.identityIdealClass D) := by
      simp only [familyIdentityClass, pullbackClass_comp]
    _ = _ := congrArg (fun m => pullbackClass m (Multiplication.identityIdealClass D)) hcleft

include hE hD hn in
/-- The actual degree correction is represented by a rational point under
the existing Abel inverse, over the original field. -/
theorem exists_point_degreeCorrection (hgE : coherentGenus k E.X = 1) :
    ∃ q : 𝟙_ (FScheme k) ⟶ E.X,
      poincareClass E E.X (𝟙 E.X) (toUnit E.X ≫ q) =
        pullbackClass f.hom.hom.left (Multiplication.identityIdealClass D) -
          n • Multiplication.identityIdealClass E := by
  let : IsLocallyNoetherian (𝟙_ (FScheme k)).left := by
    change IsLocallyNoetherian (Spec (.of k))
    infer_instance
  let a := degreeCorrectionClass f hE hD n hn
  let q := Curve.Abel.inverseCandidate smoothFieldNormality normalComponentsOpen
    smoothFieldRegularity smoothClosedPointDimension smoothFieldDimension
    Curve.Picard.Degree.properCurveProductFormula moduleTensorPullback
    Curve.Abel.FiniteCartierDegree.finiteCartierIdealDegree relativeCartierIdealBaseChange
    smoothRelativeDivisorIdeal Curve.Picard.NormDegree.finiteMorphismNormOrder
    Cohomology.properStructureCohomologyBaseChange lineBundleRiemannRoch
    lineBundleHighDegreeVanishing Cohomology.noetherianSheafCohomologyVanishing E.X hE
    η[E.X].left (Over.w _) hgE (𝟙_ (FScheme k)) a
    fibrewiseRegularLineBundle smoothRelativeCartierLocality
  have hq : PointDivisor.degreeZeroPointClass E hE (𝟙_ (FScheme k)) q = a :=
    Curve.Abel.inverseCandidate_class smoothFieldNormality normalComponentsOpen
      smoothFieldRegularity smoothClosedPointDimension smoothFieldDimension
      Curve.Picard.Degree.properCurveProductFormula moduleTensorPullback
      Curve.Abel.FiniteCartierDegree.finiteCartierIdealDegree relativeCartierIdealBaseChange
      smoothRelativeDivisorIdeal Curve.Picard.NormDegree.finiteMorphismNormOrder
      Cohomology.properStructureCohomologyBaseChange lineBundleRiemannRoch
      lineBundleHighDegreeVanishing Cohomology.noetherianSheafCohomologyVanishing E.X hE
      η[E.X].left (Over.w _) hgE (𝟙_ (FScheme k)) a
      fibrewiseRegularLineBundle smoothRelativeCartierLocality
  have h := congrArg (fun b => pullbackClass (ρ_ E.X).inv.left b.val.val) hq
  rw [pointClass_unitor] at h
  change poincareClass E E.X (𝟙 E.X) (toUnit E.X ≫ q) =
    (pullbackHom moduleTensorPullback (ρ_ E.X).inv.left)
      (pullbackClass (f.hom.hom ▷ (𝟙_ (FScheme k))).left
        (familyIdentityClass D (𝟙_ (FScheme k))) -
          n • familyIdentityClass E (𝟙_ (FScheme k))) at h
  rw [map_sub, map_nsmul, pullbackHom_apply, pullbackHom_apply,
    familyIdentityClass_unitor_pullback, familyIdentityClass_unitor] at h
  exact ⟨q, h⟩

omit [SmoothOfRelativeDimension 1 E.X.hom] [IsSeparated E.X.hom]
  [SmoothOfRelativeDimension 1 D.X.hom] [IsSeparated D.X.hom]
  [IsFinite f.hom.hom.left] [Etale f.hom.hom.left] [Surjective f.hom.hom.left] in
/-- Cross-effect commutes with the literal pullback along a group map. -/
theorem picardCrossEffect_pullback (L : PicardGroup D.X.left) :
    picardCrossEffect E (pullbackClass f.hom.hom.left L) =
      pullbackClass (f.hom.hom ⊗ₘ f.hom.hom).left (picardCrossEffect D L) := by
  have hd : (f.hom.hom ⊗ₘ f.hom.hom) ≫ Multiplication.difference D =
      Multiplication.difference E ≫ f.hom.hom := by
    simp only [Multiplication.difference, GrpObj.comp_div, GrpObj.div_comp,
      tensorHom_fst, tensorHom_snd]
  have hi : (f.hom.hom ⊗ₘ f.hom.hom) ≫ snd D.X D.X ≫ ι[D.X] =
      (snd E.X E.X ≫ ι[E.X]) ≫ f.hom.hom := by
    rw [tensorHom_snd_assoc, Category.assoc, GrpObj.inv_hom]
  change -pullbackClass (Multiplication.difference E).left (pullbackClass f.hom.hom.left L) +
    pullbackClass (fst E.X E.X).left (pullbackClass f.hom.hom.left L) +
    pullbackClass (snd E.X E.X ≫ ι[E.X]).left (pullbackClass f.hom.hom.left L) =
    (pullbackHom moduleTensorPullback (f.hom.hom ⊗ₘ f.hom.hom).left)
      (-pullbackClass (Multiplication.difference D).left L +
        pullbackClass (fst D.X D.X).left L + pullbackClass (snd D.X D.X ≫ ι[D.X]).left L)
  rw [map_add, map_add, map_neg]
  simp only [pullbackHom_apply, ← pullbackClass_comp, ← Over.comp_left,
    hd, tensorHom_fst, hi]

include hE hD hn in
/-- The actual degree of an isogeny controls the simultaneous pullback
of the normalized diagonal class. -/
theorem normalizedDiagonalClass_tensor_pullback [IsAlgClosed k]
    (hgE : coherentGenus k E.X = 1) :
    pullbackClass (f.hom.hom ⊗ₘ f.hom.hom).left
      (Multiplication.normalizedDiagonalClass D) =
      n • Multiplication.normalizedDiagonalClass E := by
  obtain ⟨q, hq⟩ := exists_point_degreeCorrection f hE hD n hn hgE
  have hz := picardCrossEffect_point E hE hgE q
  rw [hq, map_sub, map_nsmul, picardCrossEffect_identityIdeal] at hz
  have he := sub_eq_zero.mp hz
  rw [picardCrossEffect_pullback, picardCrossEffect_identityIdeal] at he
  exact he

include hn in
/-- The constructed actual Picard dual satisfies the source multiplication
triangle. The proof uses the geometric degree and the actual Picard
pullback comparison, rather than identifying a dual from triangles alone. -/
theorem picardDualHom_triangle [IsAlgClosed k] (hgE : coherentGenus k E.X = 1) :
    f.hom.hom ≫ (picardDualHom f hE hD hgE).hom.hom = (𝟙 E.X) ^ n := by
  let : IsIntegral E.X.left := hE.isIntegral
  apply pointClass_injective E hE hgE E.X
  rw [PointDivisor.degreeZeroPointClass_pow E hE hgE]
  apply Subtype.ext
  apply Subtype.ext
  change (PointDivisor.degreeZeroPointClass E hE E.X
      (f.hom.hom ≫ (picardDualHom f hE hD hgE).hom.hom)).val.val =
    n • (PointDivisor.degreeZeroPointClass E hE E.X (𝟙 E.X)).val.val
  rw [Multiplication.degreeZeroPointClass_id_val]
  have h := congrArg (fun a => a.val.val)
    (picardDualHom_pointClass f hE hD hgE E.X f.hom.hom)
  change (PointDivisor.degreeZeroPointClass E hE E.X
      (f.hom.hom ≫ (picardDualHom f hE hD hgE).hom.hom)).val.val =
    pullbackClass (f.hom.hom ▷ E.X).left
      (PointDivisor.degreeZeroPointClass D hD E.X f.hom.hom).val.val at h
  rw [pointClass_val D hD E.X f.hom.hom, ← pullbackClass_comp, ← Over.comp_left,
    ← tensorHom_def] at h
  exact h.trans (normalizedDiagonalClass_tensor_pullback f hE hD n hn hgE)

include hn in
/-- An actual reverse map with the source multiplication triangle is the
constructed Picard dual, once the original isogeny's geometric degree is
known. Epimorphism cancellation is used only after the Picard-dual triangle
has been proved geometrically. -/
theorem eq_picardDualHom_of_triangle [IsAlgClosed k] (hgE : coherentGenus k E.X = 1)
    (d : D ⟶ E) (hfd : f.hom.hom ≫ d.hom.hom = (𝟙 E.X) ^ n) :
    d = picardDualHom f hE hD hgE := by
  apply EtaleQuotient.cancel_group_map f
  apply Grp.hom_ext
  exact hfd.trans (picardDualHom_triangle f hE hD n hn hgE).symm

include hn in
/-- The given multiplication-triangle reverse acts by the actual Picard
pullback on every test scheme. This is the comparison needed before
constructing its Cartier kernel pairing. -/
theorem reverse_pointClass [IsAlgClosed k] (hgE : coherentGenus k E.X = 1)
    (d : D ⟶ E) (hfd : f.hom.hom ≫ d.hom.hom = (𝟙 E.X) ^ n)
    (T : FScheme k) (a : T ⟶ D.X) :
    PointDivisor.degreeZeroPointClass E hE T (a ≫ d.hom.hom) =
      picardPullback f hE hD T (PointDivisor.degreeZeroPointClass D hD T a) := by
  rw [eq_picardDualHom_of_triangle f hE hD n hn hgE d hfd]
  exact picardDualHom_pointClass f hE hD hgE T a

end AlgebraicGeometry.Scheme.Group.DualIsogeny
