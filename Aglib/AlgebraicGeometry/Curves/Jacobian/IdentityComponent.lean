/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.PicardScheme
public import Aglib.AlgebraicGeometry.Curves.Jacobian.RationalPoints
public import Aglib.AlgebraicGeometry.Group.IdentityComponent.Irreducible
public import Aglib.AlgebraicGeometry.Morphisms.Proper.Over

/-!
# The identity component of the Picard scheme of a curve as the image of the Abel morphism

Let `k` be an algebraically closed field, `X` a smooth proper geometrically connected curve over
`k` (`Curve.Properties X`) with a rational point `o`, `g = coherentGenus k X`, and let `P`, locally
of finite type and separated over `k`, represent `Pic_{X/k,(fppf)}` on locally Noetherian test
schemes through `R`, with group law `picardCommGrpObj X.hom P R` and identity component
`J = Pic⁰_{X/k}`. Let `Z ⊆ P` be an open and closed set containing the unit point whose rational
points are the points of degree-zero classes, in the sense that `picardPoint P R L ∈ Z` forces
`deg L = 0`. In [DegreeStrata](DegreeStrata.lean), `Z` is the Hilbert-polynomial stratum of the
unit point. Then (Stacks, Picard Schemes of Curves, Lemma 6.7, Tag 0BA0, proof, and Milne,
*Jacobian Varieties*, §1, p. 3):

* every degree-zero class is a value of the Abel morphism `a_g : X^g ⟶ P` at a rational point of
  `X^g` (`exists_comp_abelMorphism_eq_picardPoint_of_isAlgClosed`, from
  `BoundedFamily.exists_parameter_of_picardDegree_eq_zero`: every degree-zero class is
  `Σ_{i < g} (p_i - o)`);
* `a_g(X^g) = Z = J` (`range_abelMorphism_eq_and_identityComponent_eq_of_isClopen_of_isAlgClosed`,
  `identityComponent_eq_of_isClopen_of_isAlgClosed`): `J ⊆ Z`
  since `Z` is open and closed and contains the unit, `a_g(X^g) ⊆ J` since `X^g` is connected,
  and `Z ⊆ a_g(X^g)` since the image is closed (`X^g` is proper, `P` separated) and contains every
  closed point of `Z` (`P` is Jacobson and its closed points are rational);
* the rational points of `J` are the degree-zero classes
  (`picardPoint_mem_identityComponent_iff_of_isClopen_of_isAlgClosed`);
* `J ⟶ Spec k` is proper (`isProper_identityComponentOver_of_isClopen_of_isAlgClosed`), since `X^g ⟶
  J` is surjective and `X^g` is proper (`isProper_of_surjective_over_proper`).

The hypotheses on `Z` are discharged in [DegreeStrata](DegreeStrata.lean).
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.RelativePicard AlgebraicGeometry.Scheme.Group
open AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.Scheme.OverField.Curve

variable {k : Type u} [Field k] {X : FScheme k} (hX : Properties X)

/-- **A curve over an algebraically closed field has a rational point**: `X` is nonempty and
Jacobson, so it has a closed point, which is rational (`pointOfClosedPoint`). -/
theorem Properties.exists_rationalPoint_of_isAlgClosed [IsAlgClosed k] (hX : Properties X) :
    ∃ o : Spec (.of k) ⟶ X.left, o ≫ X.hom = 𝟙 _ := by
  have := curveProperties_locallyOfFiniteType hX
  have : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  obtain ⟨x⟩ := curveProperties_nonempty hX
  obtain ⟨z, -, hz⟩ := nonempty_inter_closedPoints (Z := Set.univ) ⟨x, trivial⟩
    isOpen_univ.isLocallyClosed
  exact ⟨pointOfClosedPoint X.hom z hz, pointOfClosedPoint_comp X.hom z hz⟩

variable (P : LocallyNoetherianOver (Spec (.of k)))
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙ (fppfPicardSheaf X.hom).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)

include hX in
/-- **Every degree-zero class is a value of the Abel morphism `a_g` at a rational point**
(`exists_parameter_of_picardDegree_eq_zero`: every degree-zero class on a curve over an
algebraically closed field is `Σ_{i < g} (p_i - o)`). -/
theorem exists_comp_abelMorphism_eq_picardPoint_of_isAlgClosed [IsAlgClosed k]
    (o : Spec (.of k) ⟶ X.left)
    (ho : o ≫ X.hom = 𝟙 _) (L : PicardGroup X.left)
    (hL : curveDegree smoothFieldNormality normalComponentsOpen smoothFieldRegularity
      smoothClosedPointDimension smoothFieldDimension Picard.Degree.properCurveProductFormula
      X hX L = 0) :
    letI := hX.smooth
    letI := hX.proper
    ∃ a : 𝟙_ (Over (Spec (.of k))) ⟶ parameter X.hom (coherentGenus k X),
      a ≫ (abelMorphism o ho P R (coherentGenus k X)).hom = picardPoint P R L := by
  have := hX.smooth
  have := hX.proper
  have := hX.isIntegral
  have := curveProperties_isNoetherian hX
  have : ∀ x : ClosedPoint X.left, IsDiscreteValuationRing (X.left.presheaf.stalk x.val) :=
    fun x => PointDivisor.isDiscreteValuationRing_stalk X hX x
  obtain ⟨a, ha, h⟩ :=
    exists_parameter_of_picardDegree_eq_zero X hX hX.topologicalKrullDim_eq_one o ho L hL
  exact ⟨Over.homMk a ha, parameterPoint_comp_abelMorphism_eq_picardPoint o ho P R a ha L h⟩

variable [LocallyOfFiniteType P.obj.hom]

include hX in
/-- **The closed points of `P` are the rational points of line-bundle classes** over an
algebraically closed field (`pointOfClosedPoint`, and
`picardPoint_bijective_of_isSplitEpi_of_isProper_of_flat_of_geometricallyIntegral`
with a rational point of `X`). -/
theorem exists_picardPoint_eq_of_isClosed_of_isAlgClosed [IsAlgClosed k] {z : P.obj.left}
    (hz : IsClosed {z}) :
    ∃ L : PicardGroup X.left, (picardPoint P R L).left (IsLocalRing.closedPoint k) = z := by
  have := hX.proper
  have := hX.flat
  have := hX.isGeometricallyIntegral
  obtain ⟨o, ho⟩ := hX.exists_rationalPoint_of_isAlgClosed
  have : IsSplitEpi X.hom := IsSplitEpi.mk' ⟨o, ho⟩
  obtain ⟨b, hb⟩ := exists_point_left_apply_eq_of_isClosed_of_isAlgClosed P.obj hz
  obtain ⟨L, hL⟩ :=
    (picardPoint_bijective_of_isSplitEpi_of_isProper_of_flat_of_geometricallyIntegral P R).2 b
  exact ⟨L, hL ▸ hb⟩

variable [IsSeparated P.obj.hom]

/-- **The image of the Abel morphism is an open and closed degree-zero locus containing the unit**
(Stacks, Tag 0BA0, proof; Milne, *Jacobian Varieties*, §1, p. 3): for an open and closed
`Z ⊆ P` containing the unit point, all of whose rational points are points of degree-zero
classes, `a_g(X^g) = Z = J`, the identity component `Pic⁰_{X/k}`. -/
theorem range_abelMorphism_eq_and_identityComponent_eq_of_isClopen_of_isAlgClosed [IsAlgClosed k]
    (o : Spec (.of k) ⟶ X.left) (ho : o ≫ X.hom = 𝟙 _)
    (Z : Set P.obj.left) (hZ : IsClopen Z)
    (hZ₁ : (letI := picardCommGrpObj X.hom P R; Group.unitPoint P.obj) ∈ Z)
    (hZdeg : ∀ L : PicardGroup X.left, (picardPoint P R L).left (IsLocalRing.closedPoint k) ∈ Z →
      curveDegree smoothFieldNormality normalComponentsOpen smoothFieldRegularity
        smoothClosedPointDimension smoothFieldDimension Picard.Degree.properCurveProductFormula
        X hX L = 0) :
    letI := hX.smooth
    letI := hX.proper
    letI := picardCommGrpObj X.hom P R
    Set.range (abelMorphism o ho P R (coherentGenus k X)).hom.left = Z ∧
      (identityComponent P.obj : Set P.obj.left) = Z := by
  let := hX.smooth
  let := hX.proper
  let := picardCommGrpObj X.hom P R
  have hJZ : (identityComponent P.obj : Set P.obj.left) ⊆ Z := hZ.connectedComponent_subset hZ₁
  have hCJ := range_abelMorphism_subset_identityComponent o ho P R hX (coherentGenus k X)
  have hZC : Z ⊆ Set.range (abelMorphism o ho P R (coherentGenus k X)).hom.left := by
    by_contra hne
    obtain ⟨z, hzZ, hzC⟩ := Set.not_subset.mp hne
    have : JacobsonSpace P.obj.left := LocallyOfFiniteType.jacobsonSpace P.obj.hom
    have hopen : IsOpen (Z ∩ (Set.range (abelMorphism o ho P R (coherentGenus k X)).hom.left)ᶜ) :=
      hZ.isOpen.inter (isClosed_range_abelMorphism o ho P R _).isOpen_compl
    have hne' : (Z ∩ (Set.range (abelMorphism o ho P R (coherentGenus k X)).hom.left)ᶜ).Nonempty :=
      ⟨z, hzZ, hzC⟩
    obtain ⟨y, ⟨hyZ, hyC⟩, hy⟩ := nonempty_inter_closedPoints hne' hopen.isLocallyClosed
    obtain ⟨L, rfl⟩ := exists_picardPoint_eq_of_isClosed_of_isAlgClosed hX P R hy
    obtain ⟨a, ha⟩ :=
      exists_comp_abelMorphism_eq_picardPoint_of_isAlgClosed hX P R o ho L (hZdeg L hyZ)
    refine hyC ⟨a.left (IsLocalRing.closedPoint k), ?_⟩
    rw [← ha]
    rfl
  exact And.intro (subset_antisymm (hCJ.trans hJZ) hZC) (subset_antisymm hJZ (hZC.trans hCJ))

include hX in
/-- **The identity component is the given degree-zero locus**: `J = Pic⁰_{X/k}` equals every open
and closed `Z ⊆ P` containing the unit point whose rational points are points of degree-zero
classes (`range_abelMorphism_eq_and_identityComponent_eq_of_isClopen_of_isAlgClosed` at a rational
point of `X`). -/
theorem identityComponent_eq_of_isClopen_of_isAlgClosed [IsAlgClosed k]
    (Z : Set P.obj.left) (hZ : IsClopen Z)
    (hZ₁ : (letI := picardCommGrpObj X.hom P R; Group.unitPoint P.obj) ∈ Z)
    (hZdeg : ∀ L : PicardGroup X.left, (picardPoint P R L).left (IsLocalRing.closedPoint k) ∈ Z →
      curveDegree smoothFieldNormality normalComponentsOpen smoothFieldRegularity
        smoothClosedPointDimension smoothFieldDimension Picard.Degree.properCurveProductFormula
        X hX L = 0) :
    letI := picardCommGrpObj X.hom P R
    (identityComponent P.obj : Set P.obj.left) = Z := by
  obtain ⟨o, ho⟩ := hX.exists_rationalPoint_of_isAlgClosed
  exact (range_abelMorphism_eq_and_identityComponent_eq_of_isClopen_of_isAlgClosed hX P R o ho Z hZ
    hZ₁ hZdeg).2

/-- **The rational points of `J = Pic⁰_{X/k}` are the degree-zero classes** (Stacks, Tag 0BA0(2);
Milne, *Jacobian Varieties*, p. 3), for `Z` as in
`identityComponent_eq_of_isClopen_of_isAlgClosed`. -/
theorem picardPoint_mem_identityComponent_iff_of_isClopen_of_isAlgClosed [IsAlgClosed k]
    (Z : Set P.obj.left) (hZ : IsClopen Z)
    (hZ₁ : (letI := picardCommGrpObj X.hom P R; Group.unitPoint P.obj) ∈ Z)
    (hZdeg : ∀ L : PicardGroup X.left, (picardPoint P R L).left (IsLocalRing.closedPoint k) ∈ Z →
      curveDegree smoothFieldNormality normalComponentsOpen smoothFieldRegularity
        smoothClosedPointDimension smoothFieldDimension Picard.Degree.properCurveProductFormula
        X hX L = 0)
    (L : PicardGroup X.left) :
    letI := picardCommGrpObj X.hom P R
    (picardPoint P R L).left (IsLocalRing.closedPoint k) ∈ identityComponent P.obj ↔
      curveDegree smoothFieldNormality normalComponentsOpen smoothFieldRegularity
        smoothClosedPointDimension smoothFieldDimension Picard.Degree.properCurveProductFormula
        X hX L = 0 := by
  let := picardCommGrpObj X.hom P R
  obtain ⟨o, ho⟩ := hX.exists_rationalPoint_of_isAlgClosed
  obtain ⟨hC, hJ⟩ :=
    range_abelMorphism_eq_and_identityComponent_eq_of_isClopen_of_isAlgClosed hX P R o ho Z hZ hZ₁
      hZdeg
  constructor
  · intro h
    have h' : (picardPoint P R L).left (IsLocalRing.closedPoint k) ∈ Z := by
      rw [← hJ]
      exact h
    exact hZdeg L h'
  · intro h
    obtain ⟨a, ha⟩ := exists_comp_abelMorphism_eq_picardPoint_of_isAlgClosed hX P R o ho L h
    change (picardPoint P R L).left (IsLocalRing.closedPoint k) ∈
      (identityComponent P.obj : Set P.obj.left)
    rw [hJ, ← hC, ← ha]
    exact ⟨a.left (IsLocalRing.closedPoint k), rfl⟩

/-- **`J = Pic⁰_{X/k}` is proper over `k`** (Stacks, Picard Schemes of Curves, Lemma 6.7,
Tag 0BA0, proof: the image of a proper scheme), for `Z` as in
`identityComponent_eq_of_isClopen_of_isAlgClosed`: the Abel morphism `X^g ⟶ J` is surjective,
`X^g` is proper and `J` is separated and of finite type (`isProper_of_surjective_over_proper`). -/
theorem isProper_identityComponentOver_of_isClopen_of_isAlgClosed [IsAlgClosed k]
    (Z : Set P.obj.left) (hZ : IsClopen Z)
    (hZ₁ : (letI := picardCommGrpObj X.hom P R; Group.unitPoint P.obj) ∈ Z)
    (hZdeg : ∀ L : PicardGroup X.left, (picardPoint P R L).left (IsLocalRing.closedPoint k) ∈ Z →
      curveDegree smoothFieldNormality normalComponentsOpen smoothFieldRegularity
        smoothClosedPointDimension smoothFieldDimension Picard.Degree.properCurveProductFormula
        X hX L = 0) :
    letI := picardCommGrpObj X.hom P R
    IsProper (identityComponentOver P.obj).hom := by
  let := picardCommGrpObj X.hom P R
  let := hX.smooth
  let := hX.proper
  obtain ⟨o, ho⟩ := hX.exists_rationalPoint_of_isAlgClosed
  obtain ⟨hC, hJ⟩ :=
    range_abelMorphism_eq_and_identityComponent_eq_of_isClopen_of_isAlgClosed hX P R o ho Z hZ hZ₁
      hZdeg
  have hsub : Set.range (abelMorphism o ho P R (coherentGenus k X)).hom.left ⊆
      identityComponent P.obj := by
    rw [hC, hJ]
  let q := liftIdentityComponent P.obj (abelMorphism o ho P R (coherentGenus k X)).hom hsub
  have hq : q ≫ identityComponentι P.obj = (abelMorphism o ho P R (coherentGenus k X)).hom :=
    liftIdentityComponent_ι _ _ _
  have : Surjective q.left := by
    refine ⟨fun y => ?_⟩
    have hy : (identityComponent P.obj).ι y ∈
        Set.range (abelMorphism o ho P R (coherentGenus k X)).hom.left := by
      rw [hC, ← hJ, ← Scheme.Opens.range_ι]
      exact ⟨y, rfl⟩
    obtain ⟨x, hx⟩ := hy
    refine ⟨x, (identityComponent P.obj).ι.isOpenEmbedding.injective ?_⟩
    rw [← hx, ← hq]
    rfl
  have : IsSeparated (identityComponentOver P.obj).hom :=
    inferInstanceAs (IsSeparated ((identityComponent P.obj).ι ≫ P.obj.hom))
  have : IsProper (locallyNoetherianParameter X (coherentGenus k X)).obj.hom :=
    parameter_isProper X.hom _
  exact isProper_of_surjective_over_proper q

end AlgebraicGeometry.Scheme.OverField.Curve
