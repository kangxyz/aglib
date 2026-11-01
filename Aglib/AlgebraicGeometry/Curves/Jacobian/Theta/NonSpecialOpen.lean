/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.Theta.UniversalFibre
public import Aglib.AlgebraicGeometry.Curves.Jacobian.Theta.RankOne

/-!
# Nonemptiness of the actual universal degree-g rank-one open

The already constructed line bundle of degree g with h0=1 and h1=0 gives a
rational point of the original Jacobian after subtracting g[O(o)]. The
whole universal classification and actual structural-field cohomology
comparison put that point in the original rank-one open. Neither a
rank-one-open hypothesis nor an Abel birationality assertion is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open Opposite AlgebraicGeometry
open Scheme Scheme.Modules Scheme.Modules.Invertible Scheme.RelativePicard Scheme.Group
open Scheme.Cohomology Scheme.Modules.QuasiCoherent
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve

variable {k : Type u} [Field k] {X : FScheme k} (hX : Properties X)
  (o : Spec (.of k) ⟶ X.left) (ho : o ≫ X.hom = 𝟙 _)
  (P : LocallyNoetherianOver (Spec (.of k)))
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf X.hom).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
  [LocallyOfFiniteType P.obj.hom]

include hX o ho in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem picardPoint_comp_translation (c d : PicardGroup X.left) :
    letI := picardCommGrpObj X.hom P R
    picardPoint P R c ≫ (GrpObj.mulRight (picardPoint P R d)).hom =
      picardPoint P R (c + d) := by
  let := picardCommGrpObj X.hom P R
  let := hX.proper
  let := hX.flat
  let := hX.isGeometricallyIntegral
  let : IsSplitEpi X.hom := IsSplitEpi.mk' ⟨o, ho⟩
  let E := picardPointAddEquivOfIsSplitEpiOfIsProperOfFlatOfGeometricallyIntegral P R
  have hadd : picardPoint P R (c + d) = picardPoint P R c * picardPoint P R d := by
    have h := congrArg Additive.toMul (E.map_add c d)
    change Additive.toMul (E (c + d)) = Additive.toMul (E c) * Additive.toMul (E d) at h
    simpa only [E,
      picardPointAddEquivOfIsSplitEpiOfIsProperOfFlatOfGeometricallyIntegral_apply] using h
  rw [hadd]
  simp only [GrpObj.mulRight, CategoryTheory.Hom.mul_def, CartesianMonoidalCategory.comp_lift_assoc,
    Category.comp_id, comp_toUnit_assoc, toUnit_unit, Category.id_comp]

variable [IsAlgClosed k] [IsSeparated P.obj.hom]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original universal degree-g rank-one open is nonempty in positive
genus, on the same P/R identity component and with the given origin. -/
theorem degreeUniversalRankOneOpen_nonempty (hg : 0 < coherentGenus k X) :
    letI := picardCommGrpObj X.hom P R
    (degreeUniversalRankOneOpen hX o ho P R (coherentGenus k X) :
      Set (identityComponentOver P.obj).left).Nonempty := by
  let := picardCommGrpObj X.hom P R
  let := hX.proper
  let := hX.smooth
  let := hX.flat
  let := hX.connected
  let := hX.isGeometricallyIntegral
  let : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension.{u} 1) :=
    smoothOfRelativeDimension_isStableUnderBaseChange 1
  let n := coherentGenus k X
  let J := identityComponentOver P.obj
  have : IsLocallyNoetherian J.left := LocallyOfFiniteType.isLocallyNoetherian J.hom
  let p := pullback.snd X.hom J.hom
  have : SmoothOfRelativeDimension 1 p := MorphismProperty.pullback_snd _ _ hX.smooth
  let B := (degreeUniversalPair hX o ho P R n).bundle
  have := lineBundle_isLocallyFree _ B
  have := lineBundle_isFinitePresentation _ B
  have : B.val.IsQuasicoherent := inferInstance
  obtain ⟨L, hdeg, h0, h1⟩ := exists_lineBundle_degree_genus_h0_one_h1_zero hX P R hg
  let c := classOf X.left L - n • classOf X.left (PointDivisor.positiveLineBundle X hX o ho)
  have hc : curveDegree smoothFieldNormality normalComponentsOpen smoothFieldRegularity
      smoothClosedPointDimension smoothFieldDimension Picard.Degree.properCurveProductFormula
      X hX c = 0 := by
    dsimp only [c]
    rw [map_sub, map_nsmul, hdeg, curveDegree_positiveLineBundle]
    simp [n]
  have hsub : Set.range (picardPoint P R c).left ⊆ identityComponent P.obj := by
    rintro _ ⟨x, rfl⟩
    have hx : x = IsLocalRing.closedPoint k :=
      Subsingleton.elim (α := Spec (.of k)) x (IsLocalRing.closedPoint k)
    rw [hx]
    exact (picardPoint_mem_identityComponent_iff_of_isAlgClosed hX P R c).mpr hc
  let a := liftIdentityComponent P.obj (picardPoint P R c) hsub
  have ha : a ≫ identityComponentι P.obj ≫ (GrpObj.mulRight (picardPoint P R
      (n • classOf X.left (PointDivisor.positiveLineBundle X hX o ho)))).hom =
      picardPoint P R (classOf X.left L) := by
    rw [← Category.assoc, liftIdentityComponent_ι,
      picardPoint_comp_translation hX o ho P R]
    exact congrArg (picardPoint P R) (sub_add_cancel _ _)
  obtain ⟨⟨s, σ⟩, hs⟩ := (Scheme.SpecToEquivOfField k J.left).symm.surjective a.left
  have hdim (q : ℕ) : modulePointFiberCohomologyDimension p B.val q s =
      Module.finrank k (moduleCohomology k X L.val q) :=
    (fibreCohomology_residueField_comparison p B.val a.left s σ.hom hs.symm q).1.symm.trans
      (degreeUniversalPair_rational_fibre_dimension hX o ho P R n a L ha q)
  change (Abel.rankOneOpen p B : Set J.left).Nonempty
  refine ⟨s, (Abel.mem_rankOneOpen p B s).mpr ⟨(hdim 0).trans h0, fun q hq => ?_⟩⟩
  by_cases hq1 : q = 1
  · subst q
    have : Module.Finite (J.left.residueField s) (modulePointFiberCohomology p B.val 1 s) :=
      modulePointFiberCohomology_finite_of_proper p B.val
        (affineLocallyFiniteType_of_finitePresentation B.val) 1 s
    exact Module.finrank_zero_iff.mp ((hdim 1).trans h1)
  · exact Abel.rankOneFamily_pointFiber_vanishing p B.val s q (by omega)

end AlgebraicGeometry.Scheme.OverField.Curve
