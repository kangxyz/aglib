/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Group.Kernel.ClosedImmersion
public import Aglib.AlgebraicGeometry.Group.Kernel.ScalarExtension
public import Aglib.AlgebraicGeometry.Curves.Picard.SmoothRepresentative
public import Aglib.AlgebraicGeometry.Curves.Abel.BoundedFamily.EulerStratum
public import Aglib.AlgebraicGeometry.Picard.LineBundleFamily.Fppf
public import Aglib.AlgebraicGeometry.Morphisms.Etale.FiniteStalkNeighborhood
public import Aglib.AlgebraicGeometry.Morphisms.Etale.QuasiFinite
public import Aglib.AlgebraicGeometry.Morphisms.FormallyUnramified.FiniteFibres
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-! # Generic finite etaleness of the original relative Picard torsion

The group kernel is always the existing `Group.Kernel.group` of pointwise
multiplication on the supplied Picard representative. Its field fibre is
etale because the same base-changed representative is smooth over the field.
Properness is produced from the original proper Euler stratum containing the
unit, using normalized torsion classes, not assumed as a certificate.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.RelativePicard AlgebraicGeometry.ProjectiveSpace

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve.PicardTorsion

attribute [local instance] Over.cartesianMonoidalCategory

section FieldFibres

variable {S Y : Scheme.{u}} [IsLocallyNoetherian S]
  (p : Y ⟶ S) [SmoothOfRelativeDimension 1 p] [IsProper p]
  [GeometricallyConnected p]
  (P : LocallyNoetherianOver S) [LocallyOfFiniteType P.obj.hom]
  (R : ((locallyNoetherianOverInclusion S).op ⋙ (fppfPicardSheaf p).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)

/-- Every original field-valued fibre of the original Picard multiplication
kernel is etale when the scalar is invertible in that field. The induced
base-changed group structure is retained; no second Picard group structure
or identity-component comparison is introduced. -/
theorem etale_fieldFibre {k : Type u} [Field k]
    (t : Spec (.of k) ⟶ S) (n : ℕ) (hn : IsUnit (n : k)) :
    letI := picardCommGrpObj p P R
    Etale (pullback.snd (Group.Kernel.group ((𝟙 (Grp.mk P.obj)) ^ n)).X.hom t) := by
  let := picardCommGrpObj p P R
  let P' := LocallyNoetherianOver.baseChange t P
  let R' := baseChangeRepresentableBy p t P R
  have hs : Smooth (pullback.snd P.obj.hom t) :=
    smooth_picardRepresentative_of_locallyFiniteType (properties_fieldFibre p t) P' R'
  let := hs
  exact Group.Kernel.etale_pullback_multiplication_of_smooth (Grp.mk P.obj) t n hn

end FieldFibres

section NormalizedClasses

variable {S Y : Scheme.{u}} [IsLocallyNoetherian S]
  (p : Y ⟶ S) [IsProper p] [Flat p] [GeometricallyIntegral p]
  (o : S ⟶ Y) (ho : o ≫ p = 𝟙 S)
  (P : LocallyNoetherianOver S) [LocallyOfFiniteType P.obj.hom]
  (R : ((locallyNoetherianOverInclusion S).op ⋙ (fppfPicardSheaf p).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)

include o ho in
/-- A point killed by pointwise multiplication has an actual torsion
line-bundle class on the original family. Normalization is essential: an
arbitrary representative modulo base Picard classes need not be torsion. -/
theorem exists_torsion_lineBundle (T : LocallyNoetherianOver S)
    (b : T.obj ⟶ P.obj) (n : ℕ) :
    letI := picardCommGrpObj p P R
    b ^ n = 1 → ∃ L : LineBundle (pullback p T.obj.hom),
      n • classOf _ L = 0 ∧
      ((quotientProjection p ≫ toFppfPicardSheaf p).app (op T.obj)).hom (classOf _ L) =
        R.homEquiv (ObjectProperty.homMk b) := by
  let := picardCommGrpObj p P R
  intro hb
  let e := ((normalizedFppfIsoOfIsProperOfFlatOfGeometricallyIntegral p o ho).app
    (op T.obj)).addCommGroupIsoToAddEquiv
  let a := e.symm (R.homEquiv (ObjectProperty.homMk b))
  have hb' : n • (Additive.ofMul b) = 0 := hb
  have hr : n • picardHomAddEquiv p P R T (Additive.ofMul b) = 0 := by
    rw [← map_nsmul, hb', map_zero]
  have ha : n • a = 0 := by
    change n • e.symm (picardHomAddEquiv p P R T (Additive.ofMul b)) = 0
    rw [← map_nsmul, hr, map_zero]
  have hav : n • (a.val : PicardGroup (pullback p T.obj.hom)) = 0 :=
    congrArg Subtype.val ha
  have hq : ((quotientProjection p ≫ toFppfPicardSheaf p).app (op T.obj)).hom a.val =
      R.homEquiv (ObjectProperty.homMk b) := by
    rw [← normalizedFamilyClass_fppf p o ho T.obj,
      normalizedFamilyClass_normalized]
    exact e.apply_symm_apply _
  obtain ⟨L, hL⟩ := Quotient.exists_rep a.val
  have hclass : classOf (pullback p T.obj.hom) L =
      (a.val : PicardGroup (pullback p T.obj.hom)) := hL
  refine ⟨L, by rw [hclass]; exact hav, ?_⟩
  change ((quotientProjection p ≫ toFppfPicardSheaf p).app (op T.obj)).hom
    (classOf (pullback p T.obj.hom) L) = _
  rw [hclass]
  exact hq

end NormalizedClasses

section EmbeddedFamily

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
  {ιX : Type u} {Y : Scheme.{u}}
  (i : Y ⟶ ProjectiveSpace A ιX) [IsClosedImmersion i]
  {N : ℕ} (e : ιX ≃ Fin (N + 1))
  [SmoothOfRelativeDimension 1 (i ≫ toSpec A ιX)]
  [IsProper (i ≫ toSpec A ιX)] [Flat (i ≫ toSpec A ιX)]
  [GeometricallyIntegral (i ≫ toSpec A ιX)]
  [GeometricallyConnected (i ≫ toSpec A ιX)]
  (o : Spec (.of A) ⟶ Y) (ho : o ≫ (i ≫ toSpec A ιX) = 𝟙 _)
  (P : LocallyNoetherianOver (Spec (.of A))) [LocallyOfFiniteType P.obj.hom]
  [IsSeparated P.obj.hom]
  (R : ((locallyNoetherianOverInclusion (Spec (.of A))).op ⋙
    (fppfPicardSheaf (i ≫ toSpec A ιX)).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)

omit [IsSeparated P.obj.hom] in
include o ho in
/-- A positive torsion point belongs to the original Euler stratum of the
unit on that same field fibre. -/
theorem fieldPoint_mem_unitEuler {k : Type u} [Field k]
    (t : Spec (.of k) ⟶ Spec (.of A)) (φ : Polynomial ℚ)
    (hunit : HasFiberDualEulerPolynomial i t φ (trivialLineBundle _)
      (IsLocalRing.closedPoint k))
    (b : (⟨Over.mk t, by change IsLocallyNoetherian (Spec _); infer_instance⟩ :
      LocallyNoetherianOver (Spec (.of A))) ⟶ P)
    (n : ℕ) (hn : 0 < n) :
    letI := picardCommGrpObj (i ≫ toSpec A ιX) P R
    b.hom ^ n = 1 → b.hom.left (IsLocalRing.closedPoint k) ∈
      (Strata.eulerCondition i N e φ).opens (T := P.obj) (R.homEquiv (𝟙 P)) := by
  let p := i ≫ toSpec A ιX
  let := picardCommGrpObj p P R
  intro hb
  obtain ⟨L, hL, hrep⟩ := exists_torsion_lineBundle p o ho P R _ b.hom n hb
  let d := curveDegree smoothFieldNormality normalComponentsOpen smoothFieldRegularity
    smoothClosedPointDimension smoothFieldDimension Picard.Degree.properCurveProductFormula
    (Over.mk (pullback.snd p t)) (properties_fieldFibre p t)
  have hdeg : d (classOf _ L) = 0 := by
    have h := congrArg d hL
    rw [map_nsmul, map_zero] at h
    exact (nsmul_right_injective (ne_of_gt hn)) h
  have hpoly := (hasFiberDualEulerPolynomial_iff_degree_zero i e t
    (properties_fieldFibre p t) φ hunit L).mpr hdeg
  have hholds : (Strata.eulerCondition i N e φ).HoldsAt (R.homEquiv b)
      (IsLocalRing.closedPoint k) := by
    change ((quotientProjection p ≫ toFppfPicardSheaf p).app
      (op (Over.mk t))).hom (classOf _ L) = R.homEquiv b at hrep
    rw [← hrep]
    exact ((Strata.eulerCondition i N e φ).holdsAt_app_iff (classOf _ L)
      (IsLocalRing.closedPoint k)).mpr hpoly
  have h := (Strata.eulerCondition i N e φ).holdsAt_map b.hom
    (R.homEquiv (𝟙 P)) (IsLocalRing.closedPoint k)
  have hr := R.homEquiv_comp b (𝟙 P)
  rw [Category.comp_id] at hr
  change R.homEquiv b = ((fppfPicardSheaf p).obj.map b.hom.op)
    (R.homEquiv (𝟙 P)) at hr
  rw [← hr] at h
  exact h.mp hholds

include e o ho in
/-- The actual kernel is proper over a neighbourhood of each base point.
The same neighbourhood and Euler polynomial come from the original Abel
proper-image construction and its retained unit condition. -/
theorem exists_neighbourhood_isProper_kernel (n : ℕ) (hn : 0 < n)
    (x : Spec (.of A)) :
    letI := picardCommGrpObj (i ≫ toSpec A ιX) P R
    ∃ U : (Spec (.of A)).Opens, x ∈ U ∧
      IsProper (pullback.snd (Group.Kernel.group ((𝟙 (Grp.mk P.obj)) ^ n)).X.hom U.ι) := by
  let p := i ≫ toSpec A ιX
  let := picardCommGrpObj p P R
  let G := Grp.mk P.obj
  let muMap : G ⟶ G := (𝟙 G) ^ n
  let K := Group.Kernel.group muMap
  let j : K.X ⟶ P.obj := (Group.Kernel.inclusion muMap).hom.hom
  obtain ⟨U, φ, hx, hunit, hproper⟩ :=
    Abel.BoundedFamily.exists_neighbourhood_isProper_eulerStratum_and_unit
      i e o ho P R x
  let W := (Strata.eulerCondition i N e φ).opens (T := P.obj) (R.homEquiv (𝟙 P))
  let Z := pullback K.X.hom U.ι
  let zU : Z ⟶ U := pullback.snd K.X.hom U.ι
  let f : Z ⟶ P.obj.left := pullback.fst K.X.hom U.ι ≫ j.left
  have hf : f ≫ P.obj.hom = zU ≫ U.ι := by
    dsimp only [f, zU]
    rw [Category.assoc, Over.w, pullback.condition]
  have hland : Set.range f ⊆ (W : Set P.obj.left) := by
    rintro _ ⟨z, rfl⟩
    let F := Z.residueField z
    let r : Spec (.of F) ⟶ Z := Z.fromSpecResidueField z
    let t : Spec (.of F) ⟶ Spec (.of A) := (r ≫ zU) ≫ U.ι
    let a : Over.mk t ⟶ K.X := Over.homMk (r ≫ pullback.fst K.X.hom U.ι) (by
      change (r ≫ pullback.fst K.X.hom U.ι) ≫ K.X.hom =
        (r ≫ pullback.snd K.X.hom U.ι) ≫ U.ι
      simpa only [Category.assoc] using congrArg (fun m => r ≫ m)
        (pullback.condition (f := K.X.hom) (g := U.ι)))
    let b : (⟨Over.mk t, by change IsLocallyNoetherian (Spec _); infer_instance⟩ :
      LocallyNoetherianOver (Spec (.of A))) ⟶ P :=
      ObjectProperty.homMk (a ≫ j)
    have hb : b.hom ^ n = 1 := by
      rw [← Group.Kernel.point_multiplication G n b.hom]
      change (a ≫ j) ≫ muMap.hom.hom = 1
      have hjzero : j ≫ muMap.hom.hom = 1 := (Group.Kernel.marking muMap).over
      rw [Category.assoc, hjzero, MonObj.comp_one]
    have ht : t (IsLocalRing.closedPoint F) ∈ U :=
      ((r ≫ zU) (IsLocalRing.closedPoint F)).property
    have h := fieldPoint_mem_unitEuler i e o ho P R t φ (hunit F t ht) b n hn hb
    have hr : r (IsLocalRing.closedPoint F) = z := Scheme.fromSpecResidueField_apply _ _
    change f (r (IsLocalRing.closedPoint F)) ∈ W at h
    rw [hr] at h
    exact h
  let β : Z ⟶ W := IsOpenImmersion.lift W.ι f (by
    rw [Scheme.Opens.range_ι]
    exact hland)
  have hβ : β ≫ W.ι = f := IsOpenImmersion.lift_fac _ _ _
  let Q := pullback (W.ι ≫ P.obj.hom) U.ι
  let q : Z ⟶ Q := pullback.lift β zU (by
    rw [← Category.assoc, hβ, hf])
  let w : Over.mk (W.ι ≫ P.obj.hom) ⟶ P.obj := Over.homMk W.ι rfl
  let jU := ((Over.pullback U.ι).map j).left
  let wU := ((Over.pullback U.ι).map w).left
  have hj : IsClosedImmersion j.left := Group.Kernel.inclusion_isClosedImmersion muMap
  have hjU : IsClosedImmersion jU :=
    MorphismProperty.overPullbackMap (P := @IsClosedImmersion) U.ι j hj
  have hwU : IsOpenImmersion wU :=
    MorphismProperty.overPullbackMap (P := @IsOpenImmersion) U.ι w inferInstance
  let := hwU
  have hqfst : q ≫ pullback.fst (W.ι ≫ P.obj.hom) U.ι = β :=
    pullback.lift_fst _ _ _
  have hqsnd : q ≫ pullback.snd (W.ι ≫ P.obj.hom) U.ι = zU :=
    pullback.lift_snd _ _ _
  have hqw : q ≫ wU = jU := by
    apply pullback.hom_ext
    · simp only [wU, jU, Over.pullback_map_left, Category.assoc, pullback.lift_fst]
      change q ≫ pullback.fst (W.ι ≫ P.obj.hom) U.ι ≫ W.ι = f
      rw [← Category.assoc, hqfst]
      exact hβ
    · simp only [wU, jU, Over.pullback_map_left, Category.assoc, pullback.lift_snd]
      change q ≫ pullback.snd (W.ι ≫ P.obj.hom) U.ι = zU
      exact hqsnd
  have : IsClosedImmersion (q ≫ wU) := by rw [hqw]; exact hjU
  have : IsClosedImmersion q := IsClosedImmersion.of_comp q wU
  let : IsProper (pullback.snd (W.ι ≫ P.obj.hom) U.ι) := hproper
  have : IsProper zU := by
    rw [show zU = q ≫ pullback.snd (W.ι ≫ P.obj.hom) U.ι from
      (pullback.lift_snd _ _ _).symm]
    infer_instance
  exact ⟨U, hx, this⟩

include e o ho in
/-- The actual positive multiplication kernel is proper on the whole base.
Properness is local on the target; each neighbourhood is supplied by the
actual original Euler-stratum construction above. -/
theorem isProper_kernel (n : ℕ) (hn : 0 < n) :
    letI := picardCommGrpObj (i ≫ toSpec A ιX) P R
    IsProper (Group.Kernel.group ((𝟙 (Grp.mk P.obj)) ^ n)).X.hom := by
  let := picardCommGrpObj (i ≫ toSpec A ιX) P R
  let k := (Group.Kernel.group ((𝟙 (Grp.mk P.obj)) ^ n)).X.hom
  choose U hx hU using exists_neighbourhood_isProper_kernel i e o ho P R n hn
  apply IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsProper) U
  · apply top_le_iff.mp
    intro x _
    exact (le_iSup U x) (hx x)
  · intro x
    let := hU x
    rw [← (isPullback_morphismRestrict k (U x)).flip.isoPullback_hom_snd]
    infer_instance

omit [IsClosedImmersion i] [Flat (i ≫ toSpec A ιX)]
  [GeometricallyIntegral (i ≫ toSpec A ιX)] [IsSeparated P.obj.hom] in
/-- Invertibility on the base gives etaleness of every original residue fibre. -/
theorem etale_residueFieldFibre_of_isUnit (n : ℕ) (hinv : IsUnit (n : A))
    (x : Spec (.of A)) :
    letI := picardCommGrpObj (i ≫ toSpec A ιX) P R
    Etale ((Group.Kernel.group ((𝟙 (Grp.mk P.obj)) ^ n)).X.hom.fiberToSpecResidueField x) := by
  let S := Spec (.of A)
  let t := S.fromSpecResidueField x
  have hnF : IsUnit (n : S.residueField x) := by
    simpa only [map_natCast] using hinv.map (Spec.preimage t).hom
  exact etale_fieldFibre (i ≫ toSpec A ιX) P R t n hnF

include e o ho in
/-- The original positive Picard multiplication kernel is finite on the whole
base when the scalar is invertible. No flatness of this kernel is asserted. -/
theorem isFinite_kernel_of_isUnit (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : A)) :
    letI := picardCommGrpObj (i ≫ toSpec A ιX) P R
    IsFinite (Group.Kernel.group ((𝟙 (Grp.mk P.obj)) ^ n)).X.hom := by
  let := picardCommGrpObj (i ≫ toSpec A ιX) P R
  let k := (Group.Kernel.group ((𝟙 (Grp.mk P.obj)) ^ n)).X.hom
  let : IsProper k := isProper_kernel i e o ho P R n hn
  have : LocallyQuasiFinite k := LocallyQuasiFinite.of_fiberToSpecResidueField k fun x => by
    let := etale_residueFieldFibre_of_isUnit i P R n hinv x
    infer_instance
  exact IsFinite.of_isProper_of_locallyQuasiFinite k

include e o ho in
/-- The original finite Picard multiplication kernel is formally unramified.
This is not a whole-base finite-etale assertion. -/
theorem formallyUnramified_kernel_of_isUnit (n : ℕ) (hn : 0 < n)
    (hinv : IsUnit (n : A)) :
    letI := picardCommGrpObj (i ≫ toSpec A ιX) P R
    FormallyUnramified (Group.Kernel.group ((𝟙 (Grp.mk P.obj)) ^ n)).X.hom := by
  let := picardCommGrpObj (i ≫ toSpec A ιX) P R
  let k := (Group.Kernel.group ((𝟙 (Grp.mk P.obj)) ^ n)).X.hom
  let : IsFinite k := isFinite_kernel_of_isUnit i e o ho P R n hn hinv
  apply FormallyUnramified.of_isFinite_of_fiberToSpecResidueField k
  intro x
  let := etale_residueFieldFibre_of_isUnit i P R n hinv x
  infer_instance

include e o ho in
/-- Over an integral Noetherian affine base, the same positive Picard
multiplication kernel is finite etale on an actual nonempty target open.
Neither properness nor generic etaleness is an external premise. -/
theorem exists_nonempty_open_finite_etale_kernel [IsDomain A]
    (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : A)) :
    letI := picardCommGrpObj (i ≫ toSpec A ιX) P R
    ∃ U : (Spec (.of A)).Opens, (U : Set (Spec (.of A))).Nonempty ∧
      IsFinite ((Group.Kernel.group ((𝟙 (Grp.mk P.obj)) ^ n)).X.hom ∣_ U) ∧
      Etale ((Group.Kernel.group ((𝟙 (Grp.mk P.obj)) ^ n)).X.hom ∣_ U) := by
  let := picardCommGrpObj (i ≫ toSpec A ιX) P R
  let k := (Group.Kernel.group ((𝟙 (Grp.mk P.obj)) ^ n)).X.hom
  let : IsProper k := isProper_kernel i e o ho P R n hn
  let S := Spec (.of A)
  let F := S.functionField
  let t : Spec F ⟶ S := S.fromSpecStalk (genericPoint S)
  have hnF : IsUnit (n : F) := by
    simpa only [map_natCast] using hinv.map (Spec.preimage t).hom
  have ht : Etale (pullback.snd k t) :=
    etale_fieldFibre (i ≫ toSpec A ιX) P R t n hnF
  obtain ⟨U, hη, he⟩ := k.exists_etale_target_neighborhood_of_etale_stalkBaseChange
    k.isClosedMap (genericPoint S) ht
  let := he
  have : IsProper (k ∣_ U) := IsZariskiLocalAtTarget.restrict (P := @IsProper) inferInstance U
  exact ⟨U, ⟨genericPoint S, hη⟩, IsFinite.of_isProper_of_locallyQuasiFinite _, he⟩

end EmbeddedFamily

end AlgebraicGeometry.Scheme.OverField.Curve.PicardTorsion
