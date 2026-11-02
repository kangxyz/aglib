/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.CoordinateGroup
public import Aglib.AlgebraicGeometry.Modules.Invertible.Affine
public import Aglib.AlgebraicGeometry.Group.PointDivisor
public import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.Geometry
public import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.Genus
public import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.BaseChange
public import Aglib.AlgebraicGeometry.Group.ScalarExtension
public import Aglib.AlgebraicGeometry.Group.PointedTranslation
public import Aglib.AlgebraicGeometry.IdealSheaf.Affine
public import Aglib.AlgebraicGeometry.IdealSheaf.BaseChange.OpenRestriction

/-!
# The actual coordinate ideal in the group-law comparison

The affine evaluation kernel is the native ideal used by Mathlib's point
class homomorphism. The affine Picard/class-group equivalence is built from
the existing actual sheaf and module equivalences.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Polynomial
open AlgebraicGeometry.Scheme.Modules.Invertible
open scoped Polynomial.Bivariate
universe u

namespace WeierstrassCurve.Projective

attribute [local instance] fieldDecidableEq

variable {k : Type u} [Field k]

/-- The actual evaluation kernel is exactly the ideal used in the native
coordinate point-to-class homomorphism. -/
theorem affinePointEval_ker (W : WeierstrassCurve k) (x y : k)
    (h : W.toAffine.Equation x y) :
    RingHom.ker (affinePointEval W x y h) =
      Affine.CoordinateRing.XYIdeal W.toAffine x (C y) := by
  let I := Affine.CoordinateRing.XYIdeal W.toAffine x (C y)
  have hpoly : (W.toAffine.polynomial.eval (C y)).eval x = 0 := by
    simpa only [Affine.polynomial, eval_add, eval_sub, eval_mul, eval_pow,
      eval_C, eval_X, add_mul, add_assoc] using (Affine.equation_iff' x y).mp h
  have hmax : I.IsMaximal := Ideal.Quotient.maximal_of_isField I
    ((Affine.CoordinateRing.quotientXYIdealEquiv hpoly).toMulEquiv.isField
      (Field.toIsField k))
  apply (hmax.eq_of_le (RingHom.ker_ne_top (affinePointEval W x y h)) ?_).symm
  apply Ideal.span_le.mpr
  intro z hz
  rcases Set.mem_insert_iff.mp hz with rfl | hz
  · change affinePointEval W x y h (Affine.CoordinateRing.XClass W.toAffine x) = 0
    simp [Affine.CoordinateRing.XClass, affinePointEval]
  · obtain rfl := Set.mem_singleton_iff.mp hz
    change affinePointEval W x y h (Affine.CoordinateRing.YClass W.toAffine (C y)) = 0
    simp [Affine.CoordinateRing.YClass, affinePointEval]

/-- The actual affine Picard class mapped to the native class group, through
global sections and the native class-group/Picard equivalence. -/
def affinePicardToClassGroup (W : WeierstrassCurve k) :
    PicardGroup (Spec (.of (affineRing W))) →+
      Additive (ClassGroup (affineRing W)) :=
  (ClassGroup.equivPic (affineRing W)).symm.toMonoidHom.toAdditive.comp
    (picardGroupEquivCommRingPic (.of (affineRing W))).toAddMonoidHom

/-- The affine comparison preserves addition of actual line-bundle classes. -/
theorem affinePicardToClassGroup_add (W : WeierstrassCurve k)
    (a b : PicardGroup (Spec (.of (affineRing W)))) :
    affinePicardToClassGroup W (a + b) =
      affinePicardToClassGroup W a + affinePicardToClassGroup W b :=
  (affinePicardToClassGroup W).map_add a b

/-- The existing affine sheaf/module equivalence and native class-group
comparison are injective on actual affine Picard classes. -/
theorem affinePicardToClassGroup_injective (W : WeierstrassCurve k) :
    Function.Injective (affinePicardToClassGroup W) :=
  (ClassGroup.equivPic (affineRing W)).symm.injective.comp
    (picardGroupEquivCommRingPic (.of (affineRing W))).injective


open CategoryTheory.Limits AlgebraicGeometry.Scheme.Hom

/-- Pulling the ideal of a factored morphism back through an open immersion
recovers its actual factor ideal. -/
def idealModulePullbackFactor {D U X : Scheme.{u}} (p : D ⟶ U)
    (i : U ⟶ X) [IsOpenImmersion i] :
    (Scheme.Modules.pullback i).obj (idealModule (p ≫ i)) ≅ idealModule p :=
  Scheme.Hom.idealModulePullbackFactor p i

/-- Restricting the actual finite coordinate-point ideal to the original
affine chart gives the sheafification of Mathlib's literal `XYIdeal`. -/
def affineCoordinateIdealIso (W : WeierstrassCurve k) (x y : k)
    (h : W.toAffine.Nonsingular x y) :
    (Scheme.Modules.pullback (affineChart W)).obj
      (idealModule (coordinatePoint W (.some x y h)).left) ≅
        AlgebraicGeometry.tilde (ModuleCat.of (affineRing W)
          (Affine.CoordinateRing.XYIdeal W.toAffine x (C y))) := by
  let e := (LinearEquiv.ofEq
    (RingHom.ker (affinePointEval W x y h.1))
    (Affine.CoordinateRing.XYIdeal W.toAffine x (C y))
    (affinePointEval_ker W x y h.1)).toModuleIso
  exact idealModulePullbackFactor
    (Spec.map (CommRingCat.ofHom (affinePointEval W x y h.1))) (affineChart W) ≪≫
      (affineIdealIso (CommRingCat.ofHom (affinePointEval W x y h.1))).symm ≪≫
      (AlgebraicGeometry.tilde.functor (.of (affineRing W))).mapIso e

/-- The ideal of a morphism from an empty scheme is the unit module. -/
def idealModuleEmptyIso {D X : Scheme.{u}} [IsEmpty D] (i : D ⟶ X) :
    idealModule i ≅ SheafOfModules.unit X.ringCatSheaf :=
  Scheme.Hom.idealModuleEmptyIso i

/-- The original origin has empty inverse image on the affine complement. -/
theorem origin_affine_pullback_isEmpty (W : WeierstrassCurve k) :
    IsEmpty (pullback (C := Scheme.{u}) (infinitySection W) (affineChart W)) := by
  constructor
  intro p
  have hc := congrArg (fun f : pullback (infinitySection W) (affineChart W) ⟶
    scheme W => f p) (pullback.condition (f := infinitySection W) (g := affineChart W))
  have hp : pullback.fst (infinitySection W) (affineChart W) p =
      IsLocalRing.closedPoint k := Subsingleton.elim _ _
  have he : affineChart W (pullback.snd (infinitySection W) (affineChart W) p) =
      infinityPoint W := by
    simpa only [Scheme.Hom.comp_apply, hp, infinityPoint] using hc.symm
  have hr : affineChart W (pullback.snd (infinitySection W) (affineChart W) p) ∈
      Set.range (affineChart W) := ⟨_, rfl⟩
  rw [affineChart_range_complement] at hr
  exact hr he

/-- The actual origin ideal becomes the unit sheaf on its affine complement. -/
def originIdealAffineIso (W : WeierstrassCurve k) :
    (Scheme.Modules.pullback (affineChart W)).obj (idealModule (infinitySection W)) ≅
      SheafOfModules.unit (Spec (.of (affineRing W))).ringCatSheaf := by
  let i := infinitySection W
  let b := affineChart W
  let a := pullback.fst i b
  let j := pullback.snd i b
  have : IsEmpty (pullback (C := Scheme.{u}) i b) := origin_affine_pullback_isEmpty W
  have : IsIso (idealPullbackMap i j b a pullback.condition) :=
    idealPullbackMap_isIso_of_isOpenImmersion i j b a pullback.condition
      (IsPullback.of_hasPullback i b)
  exact asIso (idealPullbackMap i j b a pullback.condition) ≪≫ idealModuleEmptyIso j


open scoped nonZeroDivisors

private theorem classGroupEquivPic_mk {A : Type u} [CommRing A] [IsDomain A]
    (I : (FractionalIdeal A⁰ (FractionRing A))ˣ) :
    ClassGroup.equivPic A (ClassGroup.mk (FractionRing A) I) =
      CommRing.Pic.mk A (FractionalIdeal.unitsMulEquivSubmodule I) := by
  rw [← ClassGroup.Quot_mk_eq_mk]
  rfl

/-- The native invertible fractional point ideal is the original integral
point ideal, through the injective localization map. -/
def coordinateIdealFractionalEquiv (W : WeierstrassCurve k) {x y : k}
    (h : W.toAffine.Nonsingular x y) :
    Affine.CoordinateRing.XYIdeal W.toAffine x (C y) ≃ₗ[affineRing W]
      FractionalIdeal.unitsMulEquivSubmodule
        (Affine.CoordinateRing.XYIdeal' (W := W.toAffine) h) := by
  change (Affine.CoordinateRing.XYIdeal W.toAffine x (C y)) ≃ₗ[affineRing W]
    IsLocalization.coeSubmodule (FractionRing (affineRing W))
      (Affine.CoordinateRing.XYIdeal W.toAffine x (C y))
  exact Submodule.equivMapOfInjective
    (Algebra.linearMap (affineRing W) (FractionRing (affineRing W)))
    (IsFractionRing.injective (affineRing W) (FractionRing (affineRing W))) _

/-- The original integral point ideal is invertible as an actual module. -/
theorem coordinateIdeal_invertible (W : WeierstrassCurve k) {x y : k}
    (h : W.toAffine.Nonsingular x y) :
    Module.Invertible (affineRing W) (Affine.CoordinateRing.XYIdeal W.toAffine x (C y)) :=
  Module.Invertible.congr (coordinateIdealFractionalEquiv W h).symm

/-- The actual sheafification of the native point ideal as a line bundle. -/
def coordinateIdealLineBundle (W : WeierstrassCurve k) {x y : k}
    (h : W.toAffine.Nonsingular x y) : LineBundle (Spec (.of (affineRing W))) := by
  let := coordinateIdeal_invertible W h
  exact tildeLineBundle (ModuleCat.of (affineRing W)
    (Affine.CoordinateRing.XYIdeal W.toAffine x (C y)))

/-- The affine sheafification of the point ideal corresponds to Mathlib's
actual point ideal class, with the original fractional ideal carrier. -/
theorem affinePicardToClassGroup_coordinateIdeal (W : WeierstrassCurve k) {x y : k}
    (h : W.toAffine.Nonsingular x y) :
    affinePicardToClassGroup W (classOf (Spec (.of (affineRing W)))
      (coordinateIdealLineBundle W h)) =
      Affine.Point.toClass (.some x y h) := by
  let := coordinateIdeal_invertible W h
  change (ClassGroup.equivPic (affineRing W)).symm
    (Additive.toMul (toCommRingPic (R := .of (affineRing W))
      (classOf _ (tildeLineBundle (R := .of (affineRing W))
        (ModuleCat.of (affineRing W)
          (Affine.CoordinateRing.XYIdeal W.toAffine x (C y))))))) = _
  rw [toCommRingPic_tildeLineBundle]
  apply (ClassGroup.equivPic (affineRing W)).injective
  rw [MulEquiv.apply_symm_apply, Affine.Point.toClass_some, classGroupEquivPic_mk]
  exact CommRing.Pic.mk_eq_mk_iff.mpr ⟨coordinateIdealFractionalEquiv W h⟩

open AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.OverField.Curve
open AlgebraicGeometry.Scheme.RelativePicard.Classes
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

/-- The inverse projection of the literal identity-base fibre product. -/
def identityFamilyLift (X : FScheme k) :
    X.left ⟶ pullback X.hom (𝟙 (Base k)) :=
  inv (pullback.fst X.hom (𝟙 (Base k)))

instance identityFamilyLift_isIso (X : FScheme k) : IsIso (identityFamilyLift X) := by
  dsimp [identityFamilyLift]
  infer_instance

private theorem graph_eq_point_identityFamilyLift (X : FScheme k)
    (P : 𝟙_ (FScheme k) ⟶ X) :
    graph X.hom (𝟙 (Base k)) P.left (Over.w P) = P.left ≫ identityFamilyLift X := by
  apply (cancel_mono (pullback.fst X.hom (𝟙 (Base k)))).mp
  simp [identityFamilyLift]

/-- The actual ideal of a rational point, as a line bundle on a smooth curve. -/
def rationalPointIdealLineBundle (X : FScheme k) (hX : Properties X)
    (P : 𝟙_ (FScheme k) ⟶ X) : LineBundle X.left := by
  let := hX.smooth
  let := hX.proper
  exact ⟨idealModule P.left,
    sectionIdeal_isLocallyRankOne smoothRelativeDivisorIdeal X.hom P.left (Over.w P)⟩

private theorem graphClass_identityFamilyLift (X : FScheme k) (hX : Properties X)
    (P : 𝟙_ (FScheme k) ⟶ X) :
    let := hX.smooth
    let := hX.proper
    pullbackClass (identityFamilyLift X)
      (classOf _ (graphIdealLineBundle smoothRelativeDivisorIdeal
        X.hom (𝟙 (Base k)) P.left (Over.w P))) =
      classOf _ (rationalPointIdealLineBundle X hX P) := by
  let := hX.smooth
  let := hX.proper
  apply Quotient.sound
  change Nonempty ((Scheme.Modules.pullback (identityFamilyLift X)).obj
    (idealModule (graph X.hom (𝟙 (Base k)) P.left (Over.w P))) ≅ idealModule P.left)
  rw [graph_eq_point_identityFamilyLift]
  exact ⟨idealModulePullbackFactor P.left (identityFamilyLift X)⟩

/-- The original normalized Abel class at the identity base, pulled back
through the canonical identity-fibre isomorphism, is the difference of the
actual point ideal classes. The normalization correction vanishes over a field. -/
theorem degreeZeroPointClass_identityFamilyLift
    (G : Grp (FScheme k)) (hG : Properties G.X) (P : 𝟙_ (FScheme k) ⟶ G.X) :
    pullbackClass (identityFamilyLift G.X)
      (Scheme.Group.PointDivisor.degreeZeroPointClass G hG (𝟙_ (FScheme k)) P).val.val =
      -classOf _ (rationalPointIdealLineBundle G.X hG P) +
        classOf _ (rationalPointIdealLineBundle G.X hG η[G.X]) := by
  let := hG.smooth
  let := hG.proper
  change pullbackClass (identityFamilyLift G.X)
    (Abel.normalizedAbelClass smoothRelativeDivisorIdeal moduleTensorPullback
      G.X.hom η[G.X].left (Over.w η[G.X]) (𝟙_ (FScheme k)) P).val = _
  rw [Abel.normalizedAbelClass, normalizeHom_val]
  let a := abelClass smoothRelativeDivisorIdeal G.X.hom η[G.X].left
    (Over.w η[G.X]) (𝟙 (Base k)) P.left (Over.w P)
  have hz : pullbackClass
      (Scheme.RelativePicard.originSection G.X.hom η[G.X].left
        (Over.w η[G.X]) (𝟙_ (FScheme k))) a = 0 := fieldPicard_eq_zero k _
  change pullbackClass (identityFamilyLift G.X)
    (a - pullbackClass (pullback.snd G.X.hom (𝟙 (Base k)))
      (pullbackClass (Scheme.RelativePicard.originSection G.X.hom η[G.X].left
        (Over.w η[G.X]) (𝟙_ (FScheme k))) a)) = _
  rw [hz, pullbackClass_zero, sub_zero]
  dsimp only [a]
  rw [abelClass_eq, pullbackClass_add moduleTensorPullback,
    pullbackClass_neg moduleTensorPullback]
  rw [graphClass_identityFamilyLift G.X hG P]
  change -classOf _ (rationalPointIdealLineBundle G.X hG P) +
    pullbackClass (identityFamilyLift G.X)
      (classOf _ (graphIdealLineBundle smoothRelativeDivisorIdeal G.X.hom (𝟙 (Base k))
        ((𝟙 (Base k)) ≫ η[G.X].left) _)) = _
  simp only [Category.id_comp]
  rw [graphClass_identityFamilyLift G.X hG η[G.X]]

/-- A given actual genus-one group law becomes addition of the actual
normalized point-ideal classes. No group law or representability is constructed. -/
theorem rationalPointIdealClass_mul [IsAlgClosed k]
    (G : Grp (FScheme k)) (hG : Properties G.X) (hg : coherentGenus k G.X = 1)
    (P Q : 𝟙_ (FScheme k) ⟶ G.X) :
    -classOf _ (rationalPointIdealLineBundle G.X hG (P * Q)) +
        classOf _ (rationalPointIdealLineBundle G.X hG η[G.X]) =
      (-classOf _ (rationalPointIdealLineBundle G.X hG P) +
        classOf _ (rationalPointIdealLineBundle G.X hG η[G.X])) +
      (-classOf _ (rationalPointIdealLineBundle G.X hG Q) +
        classOf _ (rationalPointIdealLineBundle G.X hG η[G.X])) := by
  have h := congrArg
    (fun a => pullbackClass (identityFamilyLift G.X) a.val.val)
    (Scheme.Group.PointDivisor.degreeZeroPointClass_mul G hG hg (𝟙_ (FScheme k)) P Q)
  change pullbackClass (identityFamilyLift G.X)
    (Scheme.Group.PointDivisor.degreeZeroPointClass G hG (𝟙_ (FScheme k)) (P * Q)).val.val =
    pullbackClass (identityFamilyLift G.X)
      ((Scheme.Group.PointDivisor.degreeZeroPointClass G hG (𝟙_ (FScheme k)) P).val.val +
        (Scheme.Group.PointDivisor.degreeZeroPointClass G hG (𝟙_ (FScheme k)) Q).val.val) at h
  rw [pullbackClass_add moduleTensorPullback, degreeZeroPointClass_identityFamilyLift,
    degreeZeroPointClass_identityFamilyLift, degreeZeroPointClass_identityFamilyLift] at h
  exact h


/-- The actual origin ideal class restricts to zero on the affine complement. -/
theorem originIdealClass_affine (W : WeierstrassCurve k) (hΔ : W.Δ ≠ 0) :
    pullbackClass (affineChart W)
      (classOf (scheme W) (rationalPointIdealLineBundle (curveOver W)
        (curveOver_properties W hΔ) (originOver W))) = 0 := by
  apply Quotient.sound
  exact ⟨originIdealAffineIso W ≪≫
    (coproductUniqueIso (fun _ : PUnit.{u + 1} =>
      SheafOfModules.unit (Spec (.of (affineRing W))).ringCatSheaf)).symm⟩

/-- The affine ideal-class invariant of an actual point of the original cubic. -/
def coordinatePointIdealInvariant (W : WeierstrassCurve k) (hΔ : W.Δ ≠ 0)
    (P : 𝟙_ (FScheme k) ⟶ curveOver W) : Additive (ClassGroup (affineRing W)) :=
  affinePicardToClassGroup W (pullbackClass (affineChart W)
    (-classOf (scheme W) (rationalPointIdealLineBundle (curveOver W)
      (curveOver_properties W hΔ) P)))

/-- The invariant is exactly the negative native point ideal class. -/
theorem coordinatePointIdealInvariant_coordinatePoint
    (W : WeierstrassCurve k) (hΔ : W.Δ ≠ 0) (P : W.toAffine.Point) :
    coordinatePointIdealInvariant W hΔ (coordinatePoint W P) = -Affine.Point.toClass P := by
  cases P with
  | zero =>
    change affinePicardToClassGroup W (pullbackClass (affineChart W)
      (-classOf (scheme W) (rationalPointIdealLineBundle (curveOver W)
        (curveOver_properties W hΔ) (originOver W)))) = -Affine.Point.toClass 0
    rw [pullbackClass_neg moduleTensorPullback, originIdealClass_affine W hΔ,
      neg_zero, map_zero, Affine.Point.toClass_zero, neg_zero]
  | some x y h =>
    unfold coordinatePointIdealInvariant
    rw [pullbackClass_neg moduleTensorPullback, map_neg]
    congr 1
    have hc : pullbackClass (affineChart W)
        (classOf (scheme W) (rationalPointIdealLineBundle (curveOver W)
          (curveOver_properties W hΔ) (coordinatePoint W (.some x y h)))) =
        classOf _ (coordinateIdealLineBundle W h) := by
      apply Quotient.sound
      exact ⟨affineCoordinateIdealIso W x y h⟩
    rw [hc, affinePicardToClassGroup_coordinateIdeal]

/-- The invariant converts any given original pointed group law into
addition in the native affine ideal class group. -/
theorem coordinatePointIdealInvariant_mul_of_isAlgClosed [IsAlgClosed k]
    (W : WeierstrassCurve k) (hΔ : W.Δ ≠ 0)
    (hg : coherentGenus k (curveOver W) = 1)
    (L : PointedGroupLaw (curveOver W) (originOver W)) :
    let : GrpObj (curveOver W) := L.law
    ∀ P Q : 𝟙_ (FScheme k) ⟶ curveOver W,
      coordinatePointIdealInvariant W hΔ (P * Q) =
        coordinatePointIdealInvariant W hΔ P + coordinatePointIdealInvariant W hΔ Q := by
  let : GrpObj (curveOver W) := L.law
  dsimp only
  intro P Q
  let G : Grp (FScheme k) := { X := curveOver W, grp := L.law }
  have h := rationalPointIdealClass_mul G (curveOver_properties W hΔ)
    hg P Q
  have h' := congrArg (fun a => affinePicardToClassGroup W
    (pullbackClass (affineChart W) a)) h
  change affinePicardToClassGroup W (pullbackClass (affineChart W)
      (-classOf (scheme W) (rationalPointIdealLineBundle (curveOver W)
        (curveOver_properties W hΔ) (P * Q)) +
        classOf (scheme W) (rationalPointIdealLineBundle (curveOver W)
          (curveOver_properties W hΔ) η[curveOver W]))) =
    affinePicardToClassGroup W (pullbackClass (affineChart W)
      ((-classOf (scheme W) (rationalPointIdealLineBundle (curveOver W)
          (curveOver_properties W hΔ) P) +
          classOf (scheme W) (rationalPointIdealLineBundle (curveOver W)
            (curveOver_properties W hΔ) η[curveOver W])) +
        (-classOf (scheme W) (rationalPointIdealLineBundle (curveOver W)
          (curveOver_properties W hΔ) Q) +
          classOf (scheme W) (rationalPointIdealLineBundle (curveOver W)
            (curveOver_properties W hΔ) η[curveOver W])))) at h'
  simpa only [L.origin, pullbackClass_add moduleTensorPullback,
    originIdealClass_affine W hΔ, map_zero, add_zero, map_add,
    coordinatePointIdealInvariant] using h'

/-- Coordinate addition agrees with every actual original pointed group
law over an algebraically closed field. -/
theorem coordinatePoint_add_of_isAlgClosed [IsAlgClosed k]
    (W : WeierstrassCurve k) (hΔ : W.Δ ≠ 0)
    (hg : coherentGenus k (curveOver W) = 1)
    (L : PointedGroupLaw (curveOver W) (originOver W)) :
    let : GrpObj (curveOver W) := L.law
    ∀ P Q : W.toAffine.Point,
      coordinatePoint W (P + Q) = coordinatePoint W P * coordinatePoint W Q := by
  let : GrpObj (curveOver W) := L.law
  dsimp only
  intro P Q
  obtain ⟨R, hR⟩ := coordinatePoint_surjective W hΔ
    (coordinatePoint W P * coordinatePoint W Q)
  have h := coordinatePointIdealInvariant_mul_of_isAlgClosed W hΔ hg L
    (coordinatePoint W P) (coordinatePoint W Q)
  rw [← hR, coordinatePointIdealInvariant_coordinatePoint,
    coordinatePointIdealInvariant_coordinatePoint, coordinatePointIdealInvariant_coordinatePoint,
    ← neg_add] at h
  rw [← hR]
  congr 1
  apply Affine.Point.toClass_injective
  rw [map_add]
  exact (neg_injective h).symm

open AlgebraicGeometry.Scheme.Group.BaseChange
variable {K : Type u} [Field K]

/-- Coefficient base change is the literal categorical pullback over the new field. -/
def coefficientCurveOverIso (W : WeierstrassCurve k) (f : k →+* K) :
    curveOver (W.map f) ≅ (Over.pullback (Spec.map (CommRingCat.ofHom f))).obj (curveOver W) := by
  letI := f.toAlgebra
  exact Over.isoMk (coefficientBaseChangeIso (S := K) W)
    (coefficientBaseChangeIso_hom_snd (S := K) W)

/-- Pullback of the given original group, transported through the actual
coefficient-base-change isomorphism, retains the original origin section. -/
abbrev coefficientPointedGroupLaw (W : WeierstrassCurve k) (f : k →+* K)
    (L : PointedGroupLaw (curveOver W) (originOver W)) :
    PointedGroupLaw (curveOver (W.map f)) (originOver (W.map f)) := by
  letI := f.toAlgebra
  letI : GrpObj (curveOver W) := L.law
  let G : Grp (FScheme k) := { X := curveOver W, grp := L.law }
  let B := (groupSchemeBaseChange (Spec.map (CommRingCat.ofHom f))).functor.obj G
  letI : GrpObj ((Over.pullback (Spec.map (CommRingCat.ofHom f))).obj (curveOver W)) :=
    B.grp
  let e := coefficientCurveOverIso W f
  letI : GrpObj (curveOver (W.map f)) := GrpObj.ofIso e.symm
  refine ⟨inferInstance, ?_⟩
  change η[B.X] ≫ e.inv = originOver (W.map f)
  apply (cancel_mono e.hom).mp
  simp only [Category.assoc, e.inv_hom_id]
  apply Over.OverMorphism.ext
  have h := congrArg Over.Hom.left
    ((pullbackFiberMulEquiv (Spec.map (CommRingCat.ofHom f)) (𝟙 (Base K)) G).map_one)
  rw [pullbackFiberMulEquiv_apply_left] at h
  simp only [Hom.one_def, Over.comp_left, Over.toUnit_left, L.origin] at h
  change pullback.lift (((𝟙 _) ≫ Spec.map (CommRingCat.ofHom f)) ≫ infinitySection W)
    (𝟙 _) _ = (𝟙 _) ≫ η[B.X].left at h
  simp only [Category.id_comp] at h
  change η[B.X].left = infinitySection (W.baseChange K) ≫
    (coefficientBaseChangeIso (S := K) W).hom
  rw [coefficientBaseChangeIso_pointed (S := K) W]
  simpa only [baseChangedInfinitySection] using! h.symm

/-- The points of the coefficient model map multiplicatively to Spec K-valued
points of the original k-group. The original group operation is retained. -/
def coefficientPointHom (W : WeierstrassCurve k) (f : k →+* K)
    (L : PointedGroupLaw (curveOver W) (originOver W)) :
    letI : GrpObj (curveOver W) := L.law
    letI : GrpObj (curveOver (W.map f)) := (coefficientPointedGroupLaw W f L).law
    (𝟙_ (FScheme K) ⟶ curveOver (W.map f)) →*
      (extensionPointSource f ⟶ curveOver W) := by
  letI : GrpObj (curveOver W) := L.law
  letI : GrpObj (curveOver (W.map f)) := (coefficientPointedGroupLaw W f L).law
  let G : Grp (FScheme k) := { X := curveOver W, grp := L.law }
  let B := (groupSchemeBaseChange (Spec.map (CommRingCat.ofHom f))).functor.obj G
  letI : GrpObj ((Over.pullback (Spec.map (CommRingCat.ofHom f))).obj (curveOver W)) :=
    B.grp
  let e := coefficientCurveOverIso W f
  let : IsMonHom e.inv := isMonHom_ofIso e.symm
  let : IsMonHom e.hom := inferInstanceAs (IsMonHom e.symm.inv)
  let a : extensionPointSource f ⟶ Over.mk ((𝟙 (Base K)) ≫ Spec.map (CommRingCat.ofHom f)) :=
    Over.homMk (𝟙 _) (by simp)
  let pre : (Over.mk ((𝟙 (Base K)) ≫ Spec.map (CommRingCat.ofHom f)) ⟶ curveOver W) →*
      (extensionPointSource f ⟶ curveOver W) :=
    { toFun := fun p => a ≫ p
      map_one' := by simp [Hom.one_def]
      map_mul' := fun p q => MonObj.comp_mul a p q }
  exact pre.comp ((pullbackFiberMulEquiv (Spec.map (CommRingCat.ofHom f))
    (𝟙 (Base K)) G).symm.toMonoidHom.comp
      (IsMonHom.monoidHom e.hom (𝟙_ (FScheme K))))

/-- The multiplicative transport has the literal coefficient scheme map as
its underlying projection. -/
theorem coefficientPointHom_left (W : WeierstrassCurve k) (f : k →+* K)
    (L : PointedGroupLaw (curveOver W) (originOver W))
    (P : 𝟙_ (FScheme K) ⟶ curveOver (W.map f)) :
    (coefficientPointHom W f L P).left = P.left ≫ coefficientSchemeMap W f := by
  let := f.toAlgebra
  change (𝟙 _) ≫ ((P ≫ (coefficientCurveOverIso W f).hom).left ≫ pullback.fst _ _) = _
  simp only [Category.id_comp, Over.comp_left, Category.assoc]
  exact congrArg (fun q => P.left ≫ q) (coefficientBaseChangeIso_hom_fst (S := K) W)

/-- Affine evaluation commutes with the original coefficient algebra map. -/
theorem affinePointEval_coefficient (W : WeierstrassCurve k) (f : k →+* K)
    (x y : K) (h : (W.map f).toAffine.Equation x y) :
    (affinePointEval (W.map f) x y h).comp (affineCoefficientMap W f) =
      affinePointEvalExtension W f x y h := by
  apply affinePointEvalExtension_ext W
  · intro a
    simp only [RingHom.comp_apply, affineCoefficientMap_constant,
      affinePointEval_constant, affinePointEvalExtension_constant]
  · simp only [RingHom.comp_apply, affineCoefficientMap_x,
      affinePointEval_x, affinePointEvalExtension_x]
  · simp only [RingHom.comp_apply, affineCoefficientMap_y,
      affinePointEval_y, affinePointEvalExtension_y]

/-- Multiplicative base-change transport agrees with the original coordinate
map to Spec K-valued points, including its infinity branch. -/
theorem coefficientPointHom_coordinatePoint (W : WeierstrassCurve k) (f : k →+* K)
    (L : PointedGroupLaw (curveOver W) (originOver W)) (P : (W.map f).toAffine.Point) :
    coefficientPointHom W f L (coordinatePoint (W.map f) P) = coordinatePointExtension W f P := by
  apply Over.OverMorphism.ext
  rw [coefficientPointHom_left]
  cases P with
  | zero => exact infinitySection_coefficient W f
  | some x y h =>
    change (Spec.map (CommRingCat.ofHom (affinePointEval (W.map f) x y h.1)) ≫
      affineChart (W.map f)) ≫ coefficientSchemeMap W f =
      Spec.map (CommRingCat.ofHom (affinePointEvalExtension W f x y h.1)) ≫ affineChart W
    rw [Category.assoc, affineChart_coefficient, ← Category.assoc, ← Spec.map_comp]
    exact congrArg (fun g : affineRing W →+* K =>
      Spec.map (CommRingCat.ofHom g) ≫ affineChart W) (affinePointEval_coefficient W f x y h.1)

/-- The coordinate operation comparison for every original group evaluated
over an algebraically closed extension field. -/
theorem coordinatePointExtension_add_of_isAlgClosed [IsAlgClosed K]
    (W : WeierstrassCurve k) (f : k →+* K) (hΔ : W.Δ ≠ 0)
    (hg : coherentGenus K (curveOver (W.map f)) = 1)
    (L : PointedGroupLaw (curveOver W) (originOver W)) :
    let : GrpObj (curveOver W) := L.law
    ∀ P Q : (W.map f).toAffine.Point,
      coordinatePointExtension W f (P + Q) =
        coordinatePointExtension W f P * coordinatePointExtension W f Q := by
  let : GrpObj (curveOver W) := L.law
  dsimp only
  intro P Q
  have hΔ' : (W.map f).Δ ≠ 0 := by
    rw [map_Δ]
    exact (_root_.map_ne_zero f).mpr hΔ
  have h := congrArg (coefficientPointHom W f L)
    (coordinatePoint_add_of_isAlgClosed (W.map f) hΔ' hg
      (coefficientPointedGroupLaw W f L) P Q)
  simpa only [map_mul, coefficientPointHom_coordinatePoint] using h


variable {E : Type u} [Field E]

/-- The actual base-compatible Spec map between two extension point sources. -/
def extensionPointSourceMap (f : k →+* K) (g : K →+* E) :
    extensionPointSource (g.comp f) ⟶ extensionPointSource f :=
  Over.homMk (Spec.map (CommRingCat.ofHom g)) (by
    change Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom f) = _
    rw [← Spec.map_comp]
    rfl)

/-- The native affine-point group map under the prescribed field tower. -/
def coordinateFieldMap (W : WeierstrassCurve k) (f : k →+* K) (g : K →+* E) :
    (W.map f).toAffine.Point →+ (W.map (g.comp f)).toAffine.Point := by
  letI := f.toAlgebra
  letI := g.toAlgebra
  letI := (g.comp f).toAlgebra
  letI : IsScalarTower k K E := IsScalarTower.of_algebraMap_eq' rfl
  exact Affine.Point.map (W' := W.toAffine) (Algebra.ofId K E)

/-- The original coordinate map is natural in an arbitrary field extension. -/
theorem coordinatePointExtension_comp (W : WeierstrassCurve k)
    (f : k →+* K) (g : K →+* E) (P : (W.map f).toAffine.Point) :
    extensionPointSourceMap f g ≫ coordinatePointExtension W f P =
      coordinatePointExtension W (g.comp f) (coordinateFieldMap W f g P) := by
  apply Over.OverMorphism.ext
  cases P with
  | zero =>
    change Spec.map (CommRingCat.ofHom g) ≫
      (Spec.map (CommRingCat.ofHom f) ≫ infinitySection W) =
      Spec.map (CommRingCat.ofHom (g.comp f)) ≫ infinitySection W
    rw [← Category.assoc, ← Spec.map_comp]
    rfl
  | some x y h =>
    change Spec.map (CommRingCat.ofHom g) ≫
      (Spec.map (CommRingCat.ofHom (affinePointEvalExtension W f x y h.1)) ≫ affineChart W) =
      Spec.map (CommRingCat.ofHom (affinePointEvalExtension W (g.comp f) (g x) (g y) _)) ≫
        affineChart W
    rw [← Category.assoc, ← Spec.map_comp]
    apply congrArg (fun q : affineRing W →+* E => Spec.map (CommRingCat.ofHom q) ≫ affineChart W)
    apply affinePointEvalExtension_ext W
    · intro a
      simp only [RingHom.comp_apply, affinePointEvalExtension_constant]
      change g (affinePointEvalExtension W f x y h.1 (algebraMap k (affineRing W) a)) =
        g (f a)
      rw [affinePointEvalExtension_constant]
    · simp only [RingHom.comp_apply, affinePointEvalExtension_x]
      change g (affinePointEvalExtension W f x y h.1 (affineX W)) = g x
      rw [affinePointEvalExtension_x]
    · simp only [RingHom.comp_apply, affinePointEvalExtension_y]
      change g (affinePointEvalExtension W f x y h.1 (affineY W)) = g y
      rw [affinePointEvalExtension_y]

/-- The original k-group evaluated on Spec K agrees with the coordinate
operation over every extension field K. The algebraic closure is only an
internal faithfully-flat test and is not an extra hypothesis. -/
theorem coordinatePointExtension_add (W : WeierstrassCurve k) (f : k →+* K)
    (hΔ : W.Δ ≠ 0) (L : PointedGroupLaw (curveOver W) (originOver W)) :
    letI : GrpObj (curveOver W) := L.law
    ∀ P Q : (W.map f).toAffine.Point,
      coordinatePointExtension W f (P + Q) =
        coordinatePointExtension W f P * coordinatePointExtension W f Q := by
  let : GrpObj (curveOver W) := L.law
  intro P Q
  let g := algebraMap K (AlgebraicClosure K)
  let m := coordinateFieldMap W f g
  have h := coordinatePointExtension_add_of_isAlgClosed W (g.comp f) hΔ
    (curveOver_coherentGenus (W.map (g.comp f))) L (m P) (m Q)
  rw [← m.map_add, ← coordinatePointExtension_comp, ← coordinatePointExtension_comp,
    ← coordinatePointExtension_comp, ← MonObj.comp_mul] at h
  apply Over.OverMorphism.ext
  let := Scheme.Group.PointedMorphism.fieldExtensionSpec_epi g
  apply (cancel_epi (Spec.map (CommRingCat.ofHom g))).mp
  exact congrArg Over.Hom.left h

/-- The exact original scalar-extension comparison family. -/
theorem coordinatePointExtensionGroupCompatibility :
    CoordinatePointExtensionGroupCompatibility.{u} := by
  intro k K _ _ _ f W hΔ L
  exact coordinatePointExtension_add W f hΔ L

private def identityExtensionSource (k : Type u) [Field k] :
    𝟙_ (FScheme k) ⟶ extensionPointSource (RingHom.id k) :=
  Over.homMk (𝟙 _) (by simp [extensionPointSource])

private theorem coordinatePointExtension_id (W : WeierstrassCurve k) (P : W.toAffine.Point) :
    identityExtensionSource k ≫ coordinatePointExtension W (RingHom.id k) P =
      coordinatePoint W P := by
  apply Over.OverMorphism.ext
  cases P with
  | zero => simp [identityExtensionSource, coordinatePointExtension, originOverExtension,
      coordinatePoint, originOver]
  | some x y h =>
    change (𝟙 _) ≫
      (Spec.map (CommRingCat.ofHom (affinePointEvalExtension W (RingHom.id k) x y h.1)) ≫
        affineChart W) = Spec.map (CommRingCat.ofHom (affinePointEval W x y h.1)) ≫ affineChart W
    rw [Category.id_comp]
    apply congrArg (fun q : affineRing W →+* k => Spec.map (CommRingCat.ofHom q) ≫ affineChart W)
    apply affinePointEvalExtension_ext W
    · intro a
      simp only [affinePointEvalExtension_constant, RingHom.id_apply, affinePointEval_constant]
    · simp only [affinePointEvalExtension_x, affinePointEval_x]
    · simp only [affinePointEvalExtension_y, affinePointEval_y]

/-- The exact original coordinate-operation comparison family. -/
theorem coordinatePointGroupCompatibility : CoordinatePointGroupCompatibility.{u} := by
  intro k _ _ W hΔ L
  let : GrpObj (curveOver W) := L.law
  dsimp only
  intro P Q
  have h := congrArg (fun p => identityExtensionSource k ≫ p)
    (coordinatePointExtension_add W (RingHom.id k) hΔ L P Q)
  simpa only [MonObj.comp_mul, coordinatePointExtension_id] using h

end WeierstrassCurve.Projective
