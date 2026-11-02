/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.RiemannRoch.EulerCharacteristic
public import Aglib.AlgebraicGeometry.Curves.Abel.BoundedFamily.RepresentedMorphism
public import Aglib.AlgebraicGeometry.Curves.Abel.BoundedFamily.GeometricFibreParameters
public import Aglib.AlgebraicGeometry.Curves.RelativeGenus
public import Aglib.AlgebraicGeometry.Picard.Strata.EulerCondition
public import Aglib.AlgebraicGeometry.Picard.Comparison.Isomorphism
public import Aglib.AlgebraicGeometry.Picard.Relative.Classes
public import Aglib.AlgebraicGeometry.Morphisms.Surjective.GeometricPoints
public import Aglib.AlgebraicGeometry.Morphisms.Proper.Over
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Aglib.AlgebraicGeometry.Picard.Strata.FiberConditions
public import Aglib.AlgebraicGeometry.Cohomology.Projective.EmbeddedFibers.SeparatedFieldComparison

/-!
# Degree zero and the original relative Euler stratum

Over an arbitrary base ring, evaluate the original embedded-family Euler
condition at an arbitrary field-valued point. Riemann--Roch compares a line
bundle with the trivial bundle on that very fibre: the polarization term and
the genus cancel. Thus the Euler stratum containing the unit consists precisely
of degree-zero classes. No new embedding, Picard representation or polarization
constancy hypothesis is introduced.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.Cohomology AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.RelativePicard

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve

variable {A : Type u} [CommRing A] {ι : Type u} {Y : Scheme.{u}}
  (i : Y ⟶ ProjectiveSpace A ι) [IsClosedImmersion i]
  {N : ℕ} (e : ι ≃ Fin (N + 1))
  {K : Type u} [Field K] (t : Spec (.of K) ⟶ Spec (.of A))

include e in
/-- At an arbitrary field-valued base point, the original residue-field Euler
invariant equals the original coherent Euler characteristic over that field. -/
theorem fiberDualTwistEulerChar_fieldPoint
    (L : LineBundle (pullback (i ≫ toSpec A ι) t)) (n : ℤ) :
    fiberDualTwistEulerChar i t L (IsLocalRing.closedPoint K) n =
      moduleEulerChar (pullback.snd (i ≫ toSpec A ι) t)
        (pulledTwistLineBundle i t n (dualLineBundle _ L)).val := by
  have : Finite ι := Finite.of_equiv _ e.symm
  have : IsProper (i ≫ toSpec A ι) := inferInstance
  have : (pulledTwist (pullback.fst (i ≫ toSpec A ι) t ≫ i) n
      (dualLineBundle _ L).val).IsQuasicoherent :=
    lineBundle_isQuasicoherent ⟨_, isLocallyRankOne_pulledTwist _ n (dualLineBundle _ L).property⟩
  have hk : Spec.map (Spec.preimage ((Spec (.of K)).fromSpecResidueField
      (IsLocalRing.closedPoint K))) ≫ t =
        (Spec (.of K)).fromSpecResidueField (IsLocalRing.closedPoint K) ≫ t := by
    rw [Spec.map_preimage]
  have hmap : residueFieldBaseChange (i ≫ toSpec A ι) t
      (IsLocalRing.closedPoint K) =
      pullback.map (i ≫ toSpec A ι)
        ((Spec (.of K)).fromSpecResidueField (IsLocalRing.closedPoint K) ≫ t)
        (i ≫ toSpec A ι) t (𝟙 Y)
        (Spec.map (Spec.preimage ((Spec (.of K)).fromSpecResidueField
          (IsLocalRing.closedPoint K)))) (𝟙 _) (by simp) (by simp) := by
    apply pullback.hom_ext <;> simp [pullback.map, Spec.map_preimage]
  change embeddedFiberTwistEulerChar i
      (K := (Spec (.of K)).residueField (IsLocalRing.closedPoint K))
      ((Spec (.of K)).fromSpecResidueField (IsLocalRing.closedPoint K) ≫ t) _ n =
    embeddedFiberTwistEulerChar i t (dualLineBundle _ L).val n
  rw [embeddedFiberTwistEulerChar_eq, embeddedFiberTwistEulerChar_eq]
  congr 1
  funext q
  congr 2
  refine (embeddedFiberTwistDim_congr i _
    ((Scheme.Modules.pullbackCongr hmap).app (dualLineBundle _ L).val) n q).trans ?_
  exact embeddedFiberTwistDim_pullbackMap_of_eq_of_isSeparated i t
    (Spec.preimage ((Spec (.of K)).fromSpecResidueField (IsLocalRing.closedPoint K))) _ hk
    (dualLineBundle _ L).val n q

include e in
/-- The original Euler conditions of a bundle and of the unit differ by minus
its degree. The entire polarization term cancels, for every integral twist. -/
theorem fiberDualTwistEulerChar_eq_unit_sub_degree
    (hY : Properties (Over.mk (pullback.snd (i ≫ toSpec A ι) t)))
    (L : LineBundle (pullback (i ≫ toSpec A ι) t)) (n : ℤ) :
    fiberDualTwistEulerChar i t L (IsLocalRing.closedPoint K) n =
      fiberDualTwistEulerChar i t (trivialLineBundle _) (IsLocalRing.closedPoint K) n -
        curveDegree smoothFieldNormality normalComponentsOpen smoothFieldRegularity
          smoothClosedPointDimension smoothFieldDimension Picard.Degree.properCurveProductFormula
          (Over.mk (pullback.snd (i ≫ toSpec A ι) t)) hY (classOf _ L) := by
  have htw (M : LineBundle (pullback (i ≫ toSpec A ι) t)) :
      classOf (Over.mk (pullback.snd (i ≫ toSpec A ι) t)).left
        (pulledTwistLineBundle i t n M) = classOf _ M + n • fiberTwistClass i t 1 :=
    classOf_pulledTwistLineBundle i t n M
  rw [fiberDualTwistEulerChar_fieldPoint i e, fiberDualTwistEulerChar_fieldPoint i e,
    show moduleEulerChar (pullback.snd (i ≫ toSpec A ι) t)
        (pulledTwistLineBundle i t n (dualLineBundle _ L)).val = _ from
      moduleEulerChar_eq_curveDegree_add_one_sub_genus
        (Over.mk (pullback.snd (i ≫ toSpec A ι) t)) hY _,
    show moduleEulerChar (pullback.snd (i ≫ toSpec A ι) t)
        (pulledTwistLineBundle i t n (dualLineBundle _ (trivialLineBundle _))).val = _ from
      moduleEulerChar_eq_curveDegree_add_one_sub_genus
        (Over.mk (pullback.snd (i ≫ toSpec A ι) t)) hY _,
    htw, htw,
    classOf_dual, classOf_dual, classOf_trivial, neg_zero, zero_add,
    map_add, map_neg]
  let d := curveDegree smoothFieldNormality normalComponentsOpen smoothFieldRegularity
    smoothClosedPointDimension smoothFieldDimension Picard.Degree.properCurveProductFormula
    (Over.mk (pullback.snd (i ≫ toSpec A ι) t)) hY
  change (-d (classOf _ L) + d (n • fiberTwistClass i t 1) + 1 -
    coherentGenus K (Over.mk (pullback.snd (i ≫ toSpec A ι) t))) =
      d (n • fiberTwistClass i t 1) + 1 -
        coherentGenus K (Over.mk (pullback.snd (i ≫ toSpec A ι) t)) - d (classOf _ L)
  ring

include e in
/-- If the unit has the given Euler polynomial on this actual field fibre,
that same Euler condition is equivalent to degree zero. The forward implication
already follows from the constant coefficient; the reverse holds at all twists. -/
theorem hasFiberDualEulerPolynomial_iff_degree_zero
    (hY : Properties (Over.mk (pullback.snd (i ≫ toSpec A ι) t)))
    (φ : Polynomial ℚ)
    (hunit : HasFiberDualEulerPolynomial i t φ (trivialLineBundle _)
      (IsLocalRing.closedPoint K))
    (L : LineBundle (pullback (i ≫ toSpec A ι) t)) :
    HasFiberDualEulerPolynomial i t φ L (IsLocalRing.closedPoint K) ↔
      curveDegree smoothFieldNormality normalComponentsOpen smoothFieldRegularity
        smoothClosedPointDimension smoothFieldDimension Picard.Degree.properCurveProductFormula
        (Over.mk (pullback.snd (i ≫ toSpec A ι) t)) hY (classOf _ L) = 0 := by
  constructor
  · intro hL
    have heq : fiberDualTwistEulerChar i t L (IsLocalRing.closedPoint K) 0 =
        fiberDualTwistEulerChar i t (trivialLineBundle _) (IsLocalRing.closedPoint K) 0 := by
      exact_mod_cast (hL 0).trans (hunit 0).symm
    have hd := fiberDualTwistEulerChar_eq_unit_sub_degree i e t hY L 0
    omega
  · intro hL n
    rw [fiberDualTwistEulerChar_eq_unit_sub_degree i e t hY L n, hL, sub_zero]
    exact hunit n

namespace Abel.BoundedFamily

variable [IsLocallyNoetherian (Spec (.of A))]
  [SmoothOfRelativeDimension 1 (i ≫ toSpec A ι)]
  [IsProper (i ≫ toSpec A ι)] [Flat (i ≫ toSpec A ι)]
  [GeometricallyIntegral (i ≫ toSpec A ι)]
  (o : Spec (.of A) ⟶ Y) (ho : o ≫ (i ≫ toSpec A ι) = 𝟙 _)
  (P : LocallyNoetherianOver (Spec (.of A)))
  (R : ((locallyNoetherianOverInclusion (Spec (.of A))).op ⋙
    (fppfPicardSheaf (i ≫ toSpec A ι)).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)

omit [GeometricallyIntegral (i ≫ toSpec A ι)] in
/-- Every field-valued point of the actual Abel parameter maps into the
Euler stratum of the unit, for every tuple length, including the empty tuple. -/
theorem abelMorphismOver_fieldPoint_mem_euler
    (hY : Properties (Over.mk (pullback.snd (i ≫ toSpec A ι) t)))
    (φ : Polynomial ℚ)
    (hunit : HasFiberDualEulerPolynomial i t φ (trivialLineBundle _)
      (IsLocalRing.closedPoint K)) (n : ℕ)
    (a : (⟨Over.mk t, by change IsLocallyNoetherian (Spec _); infer_instance⟩ :
      LocallyNoetherianOver (Spec (.of A))) ⟶
      locallyNoetherianParameterOver (i ≫ toSpec A ι) n) :
    (a ≫ abelMorphismOver (i ≫ toSpec A ι) o ho P R n).hom.left
        (IsLocalRing.closedPoint K) ∈
      (Strata.eulerCondition i N e φ).opens (T := P.obj) (R.homEquiv (𝟙 P)) := by
  let p := i ≫ toSpec A ι
  let L := pullbackLineBundle ((familyScheme p).map a.hom) (lineBundle p o ho n)
  have hdeg : curveDegree smoothFieldNormality normalComponentsOpen smoothFieldRegularity
      smoothClosedPointDimension smoothFieldDimension Picard.Degree.properCurveProductFormula
      (Over.mk (pullback.snd p t)) hY (classOf _ L) = 0 := by
    change curveDegree _ _ _ _ _ _ _ _
      (classOf _ (pullbackLineBundle _ (lineBundle p o ho n))) = 0
    rw [← pullbackClass_classOf, ← RelativePicard.Classes.familyMap_eq_familyScheme_map]
    exact lineBundle_degree_at_field_point p o ho t a.hom.left (Over.w a.hom) hY
  have hpoly := (hasFiberDualEulerPolynomial_iff_degree_zero i e t hY φ hunit L).mpr hdeg
  have hholds : (Strata.eulerCondition i N e φ).HoldsAt
      (R.homEquiv (a ≫ abelMorphismOver p o ho P R n)) (IsLocalRing.closedPoint K) := by
    rw [homEquiv_comp_abelMorphismOver]
    apply ((Strata.eulerCondition i N e φ).holdsAt_app_iff _ _).mpr
    change (Strata.eulerCondition i N e φ).Holds _
      (pullbackClass _ (classOf _ (lineBundle p o ho n))) _
    rw [pullbackClass_classOf]
    exact hpoly
  have h := (Strata.eulerCondition i N e φ).holdsAt_map
    (a ≫ abelMorphismOver p o ho P R n).hom (R.homEquiv (𝟙 P))
    (IsLocalRing.closedPoint K)
  have hn := R.homEquiv_comp (a ≫ abelMorphismOver p o ho P R n) (𝟙 P)
  rw [Category.comp_id] at hn
  change R.homEquiv (a ≫ abelMorphismOver p o ho P R n) =
    ((fppfPicardSheaf p).obj.map (a ≫ abelMorphismOver p o ho P R n).hom.op)
      (R.homEquiv (𝟙 P)) at hn
  rw [← hn] at h
  exact h.mp hholds

/-- Every geometric point of the original Euler stratum containing the unit
lifts through the actual relative Abel map of the actual fibre genus. The
representing equivalence on both sides is exactly `R`. -/
theorem exists_parameter_over_eulerPoint [IsAlgClosed K]
    (hY : Properties (Over.mk (pullback.snd (i ≫ toSpec A ι) t)))
    (φ : Polynomial ℚ)
    (hunit : HasFiberDualEulerPolynomial i t φ (trivialLineBundle _)
      (IsLocalRing.closedPoint K))
    (b : (⟨Over.mk t, by change IsLocallyNoetherian (Spec _); infer_instance⟩ :
      LocallyNoetherianOver (Spec (.of A))) ⟶ P)
    (hb : b.hom.left (IsLocalRing.closedPoint K) ∈
      (Strata.eulerCondition i N e φ).opens (T := P.obj) (R.homEquiv (𝟙 P))) :
    ∃ a : (⟨Over.mk t, by change IsLocallyNoetherian (Spec _); infer_instance⟩ :
      LocallyNoetherianOver (Spec (.of A))) ⟶
        locallyNoetherianParameterOver (i ≫ toSpec A ι)
          (coherentGenus K (Over.mk (pullback.snd (i ≫ toSpec A ι) t))),
      a ≫ abelMorphismOver (i ≫ toSpec A ι) o ho P R
        (coherentGenus K (Over.mk (pullback.snd (i ≫ toSpec A ι) t))) = b := by
  let p := i ≫ toSpec A ι
  let T : LocallyNoetherianOver (Spec (.of A)) :=
    ⟨Over.mk t, by change IsLocallyNoetherian (Spec _); infer_instance⟩
  let : IsSplitEpi p := IsSplitEpi.mk' ⟨o, ho⟩
  have hsurj : Function.Surjective
      ((quotientProjection p ≫ toFppfPicardSheaf p).app (op T.obj)) :=
    ((((relativeFppfIsoOfIsSplitEpiOfIsProperOfFlatOfGeometricallyIntegral p).app
      (op T.obj)).addCommGroupIsoToAddEquiv.bijective).2).comp
        (quotientProjection_app_surjective p (op T.obj))
  obtain ⟨L, hL⟩ := hsurj (R.homEquiv b)
  obtain ⟨L, rfl⟩ := Quotient.exists_rep L
  have hb' : (Strata.eulerCondition i N e φ).HoldsAt (R.homEquiv b)
      (IsLocalRing.closedPoint K) := by
    have h := (Strata.eulerCondition i N e φ).holdsAt_map b.hom
      (R.homEquiv (𝟙 P)) (IsLocalRing.closedPoint K)
    have hn := R.homEquiv_comp b (𝟙 P)
    rw [Category.comp_id] at hn
    change R.homEquiv b = ((fppfPicardSheaf p).obj.map b.hom.op)
      (R.homEquiv (𝟙 P)) at hn
    rw [← hn] at h
    exact h.mpr hb
  rw [← hL] at hb'
  have hpoly : HasFiberDualEulerPolynomial i t φ L (IsLocalRing.closedPoint K) :=
    ((Strata.eulerCondition i N e φ).holdsAt_app_iff (classOf _ L)
      (IsLocalRing.closedPoint K)).mp hb'
  have hdeg := (hasFiberDualEulerPolynomial_iff_degree_zero i e t hY φ hunit L).mp hpoly
  obtain ⟨a, ha, hclass⟩ := exists_parameter_over_geometricPoint_of_degree_zero
    p o ho t hY (classOf _ L) hdeg
  let a' : T ⟶ locallyNoetherianParameterOver p
      (coherentGenus K (Over.mk (pullback.snd p t))) :=
    ObjectProperty.homMk (Over.homMk a ha)
  refine ⟨a', R.homEquiv.injective ?_⟩
  rw [homEquiv_comp_abelMorphismOver]
  rw [← RelativePicard.Classes.familyMap_eq_familyScheme_map]
  exact (congrArg (fun c => (quotientProjection p ≫ toFppfPicardSheaf p).app
    (op T.obj) c) hclass).trans hL

variable [GeometricallyConnected (i ≫ toSpec A ι)]

omit [GeometricallyIntegral (i ≫ toSpec A ι)] in
include e in
/-- An actual neighbourhood simultaneously fixes the original unit Euler
polynomial and the actual genus. Neither constancy statement is an input. -/
theorem exists_unitEuler_genus_neighbourhood (x : Spec (.of A)) :
    ∃ (U : (Spec (.of A)).Opens) (φ : Polynomial ℚ), x ∈ U ∧
      ∀ (F : Type u) [Field F] (t : Spec (.of F) ⟶ Spec (.of A)),
        t (IsLocalRing.closedPoint F) ∈ U →
          HasFiberDualEulerPolynomial i t φ (trivialLineBundle _)
            (IsLocalRing.closedPoint F) ∧
          coherentGenus F (Over.mk (pullback.snd (i ≫ toSpec A ι) t)) =
            relativeGenus (i ≫ toSpec A ι) x := by
  let B : Over (Spec (.of A)) := Over.mk (𝟙 _)
  let : IsLocallyNoetherian B.left := inferInstanceAs (IsLocallyNoetherian (Spec (.of A)))
  obtain ⟨φ, hφ⟩ := Strata.exists_eulerCondition_holds (i := i) (N := N) (e := e) B 0 x
  let C := Strata.eulerCondition i N e φ
  have hφ' : C.HoldsAt (0 : (fppfPicardSheaf (i ≫ toSpec A ι)).obj.obj (op B)) x := by
    have h := (C.holdsAt_app_iff (0 : (familyPicardFunctor (i ≫ toSpec A ι)).obj
      (op B)) x).mpr hφ
    simpa only [map_zero] using h
  let U := C.opens (0 : (fppfPicardSheaf (i ≫ toSpec A ι)).obj.obj (op B)) ⊓
    genusNeighbourhood (i ≫ toSpec A ι) x
  refine ⟨U, φ, ⟨hφ', mem_genusNeighbourhood _ x⟩, ?_⟩
  intro F _ t ht
  let g : Over.mk t ⟶ B := Over.homMk t (by simp [B])
  have hzero := (C.holdsAt_map g 0 (IsLocalRing.closedPoint F)).mpr ht.1
  have hzero' : C.HoldsAt (0 : (fppfPicardSheaf (i ≫ toSpec A ι)).obj.obj
      (op (Over.mk t))) (IsLocalRing.closedPoint F) := by simpa using hzero
  have hunit := (C.holdsAt_app_iff (T := Over.mk t)
    (classOf _ (trivialLineBundle _)) (IsLocalRing.closedPoint F)).mp (by
      simpa only [classOf_trivial, map_zero] using hzero')
  exact ⟨hunit, coherentGenus_eq_on_genusNeighbourhood (i ≫ toSpec A ι) x t ht.2⟩

/-- At every specified base point, one actual neighbourhood admits a single
bounded original Abel family covering every geometric point of one original
Euler stratum. The bound and the unit stratum are constructed, not supplied. -/
theorem exists_neighbourhood_geometricPoint_lifts (x : Spec (.of A)) :
    ∃ (U : (Spec (.of A)).Opens) (φ : Polynomial ℚ), x ∈ U ∧
      ∀ (F : Type u) [Field F] [IsAlgClosed F] (t : Spec (.of F) ⟶ Spec (.of A)),
        t (IsLocalRing.closedPoint F) ∈ U →
        ∀ b : (⟨Over.mk t, by change IsLocallyNoetherian (Spec _); infer_instance⟩ :
      LocallyNoetherianOver (Spec (.of A))) ⟶ P,
          b.hom.left (IsLocalRing.closedPoint F) ∈
              (Strata.eulerCondition i N e φ).opens (T := P.obj) (R.homEquiv (𝟙 P)) →
          ∃ a : (⟨Over.mk t, by change IsLocallyNoetherian (Spec _); infer_instance⟩ :
      LocallyNoetherianOver (Spec (.of A))) ⟶
              locallyNoetherianParameterOver (i ≫ toSpec A ι) (relativeGenus (i ≫ toSpec A ι) x),
            a ≫ abelMorphismOver (i ≫ toSpec A ι) o ho P R
              (relativeGenus (i ≫ toSpec A ι) x) = b := by
  obtain ⟨U, φ, hx, hU⟩ := exists_unitEuler_genus_neighbourhood i e x
  refine ⟨U, φ, hx, ?_⟩
  intro F _ _ t ht b hb
  obtain ⟨hunit, hgenus⟩ := hU F t ht
  have h := exists_parameter_over_eulerPoint i e t o ho P R
    (properties_fieldFibre (i ≫ toSpec A ι) t) φ hunit b hb
  rw [hgenus] at h
  exact h

include o ho in
/-- The original Euler stratum of degree zero is proper on an actual
neighbourhood of each base point. Its proper source is the restricted original
finite tuple parameter, and its surjectivity is constructed on geometric
points from the original fibre tuple theorem and the same representation.
The unit Euler condition is retained for these same `U` and `φ`, so subsequent
kernel constructions do not have to choose a second stratum. -/
theorem exists_neighbourhood_isProper_eulerStratum_and_unit
    [IsSeparated P.obj.hom] [LocallyOfFiniteType P.obj.hom]
    (x : Spec (.of A)) :
    ∃ (U : (Spec (.of A)).Opens) (φ : Polynomial ℚ), x ∈ U ∧
      (∀ (F : Type u) [Field F] (t : Spec (.of F) ⟶ Spec (.of A)),
        t (IsLocalRing.closedPoint F) ∈ U →
          HasFiberDualEulerPolynomial i t φ (trivialLineBundle _)
            (IsLocalRing.closedPoint F)) ∧
      IsProper (pullback.snd
        (((Strata.eulerCondition i N e φ).opens (T := P.obj)
          (R.homEquiv (𝟙 P))).ι ≫ P.obj.hom) U.ι) := by
  obtain ⟨U, φ, hx, hU⟩ := exists_unitEuler_genus_neighbourhood i e x
  let p := i ≫ toSpec A ι
  let g := relativeGenus p x
  let A₀ := parameter p g
  let α : A₀.left ⟶ P.obj.left := (abelMorphismOver p o ho P R g).hom.left
  have hα : α ≫ P.obj.hom = A₀.hom := Over.w (abelMorphismOver p o ho P R g).hom
  let W := (Strata.eulerCondition i N e φ).opens (T := P.obj) (R.homEquiv (𝟙 P))
  let Z := pullback A₀.hom U.ι
  let zU : Z ⟶ U := pullback.snd A₀.hom U.ι
  let f : Z ⟶ P.obj.left := pullback.fst A₀.hom U.ι ≫ α
  have hf : f ≫ P.obj.hom = zU ≫ U.ι := by
    dsimp only [f, zU]
    rw [Category.assoc, hα, pullback.condition]
  have hland : Set.range f ⊆ (W : Set P.obj.left) := by
    rintro _ ⟨z, rfl⟩
    let F := Z.residueField z
    let r : Spec (.of F) ⟶ Z := Z.fromSpecResidueField z
    let t : Spec (.of F) ⟶ Spec (.of A) := (r ≫ zU) ≫ U.ι
    have ht : t (IsLocalRing.closedPoint F) ∈ U :=
      ((r ≫ zU) (IsLocalRing.closedPoint F)).property
    obtain ⟨hunit, _⟩ := hU F t ht
    let a : (⟨Over.mk t, by change IsLocallyNoetherian (Spec _); infer_instance⟩ :
      LocallyNoetherianOver (Spec (.of A))) ⟶
        locallyNoetherianParameterOver p g := ObjectProperty.homMk
      (Over.homMk (r ≫ pullback.fst A₀.hom U.ι) (by
        change (r ≫ pullback.fst A₀.hom U.ι) ≫ A₀.hom =
          (r ≫ pullback.snd A₀.hom U.ι) ≫ U.ι
        simpa only [Category.assoc] using congrArg (fun m => r ≫ m)
          (pullback.condition (f := A₀.hom) (g := U.ι))))
    have h := abelMorphismOver_fieldPoint_mem_euler i e t o ho P R
      (properties_fieldFibre p t) φ hunit g a
    have hr : r (IsLocalRing.closedPoint F) = z := Scheme.fromSpecResidueField_apply _ _
    change f (r (IsLocalRing.closedPoint F)) ∈ W at h
    rw [hr] at h
    exact h
  let β : Z ⟶ W := IsOpenImmersion.lift W.ι f (by
    rw [Scheme.Opens.range_ι]
    exact hland)
  have hβ : β ≫ W.ι = f := IsOpenImmersion.lift_fac _ _ _
  have hβS : β ≫ (W.ι ≫ P.obj.hom) = zU ≫ U.ι := by
    rw [← Category.assoc, hβ, hf]
  let Q := pullback (W.ι ≫ P.obj.hom) U.ι
  let q : Z ⟶ Q := pullback.lift β zU hβS
  have hqU : q ≫ pullback.snd (W.ι ≫ P.obj.hom) U.ι = zU := pullback.lift_snd _ _ _
  have hlift : ∀ (F : Type u) [Field F] [IsAlgClosed F] (r : Spec (.of F) ⟶ Q),
      ∃ aZ : Spec (.of F) ⟶ Z, aZ ≫ q = r := by
    intro F _ _ r
    let tU := r ≫ pullback.snd (W.ι ≫ P.obj.hom) U.ι
    let t := tU ≫ U.ι
    let b₀ := (r ≫ pullback.fst (W.ι ≫ P.obj.hom) U.ι) ≫ W.ι
    have hb₀ : b₀ ≫ P.obj.hom = t := by
      dsimp only [b₀, t, tU]
      simpa only [Category.assoc] using congrArg (fun m => r ≫ m)
        (pullback.condition (f := W.ι ≫ P.obj.hom) (g := U.ι))
    let b : (⟨Over.mk t, by change IsLocallyNoetherian (Spec _); infer_instance⟩ :
      LocallyNoetherianOver (Spec (.of A))) ⟶ P :=
      ObjectProperty.homMk (Over.homMk b₀ hb₀)
    have ht : t (IsLocalRing.closedPoint F) ∈ U :=
      (tU (IsLocalRing.closedPoint F)).property
    have hb : b.hom.left (IsLocalRing.closedPoint F) ∈ W :=
      ((r ≫ pullback.fst (W.ι ≫ P.obj.hom) U.ι) (IsLocalRing.closedPoint F)).property
    obtain ⟨hunit, hgenus⟩ := hU F t ht
    have hlift := exists_parameter_over_eulerPoint i e t o ho P R
      (properties_fieldFibre p t) φ hunit b hb
    rw [hgenus] at hlift
    obtain ⟨a, ha⟩ := hlift
    let aZ : Spec (.of F) ⟶ Z := pullback.lift a.hom.left tU (Over.w a.hom)
    have haα : a.hom.left ≫ α = b₀ := congrArg (fun c => c.hom.left) ha
    have hqfst : q ≫ pullback.fst (W.ι ≫ P.obj.hom) U.ι = β :=
      pullback.lift_fst _ _ _
    have haZq : aZ ≫ q = r := by
      apply pullback.hom_ext
      · apply (cancel_mono W.ι).mp
        calc
          (aZ ≫ q ≫ pullback.fst (W.ι ≫ P.obj.hom) U.ι) ≫ W.ι =
              (aZ ≫ β) ≫ W.ι := by rw [hqfst]
          _ = aZ ≫ f := by rw [Category.assoc, hβ]
          _ = a.hom.left ≫ α := by
            dsimp only [aZ, f]
            rw [← Category.assoc, pullback.lift_fst]
          _ = (r ≫ pullback.fst (W.ι ≫ P.obj.hom) U.ι) ≫ W.ι := haα
      · rw [Category.assoc, hqU]
        exact pullback.lift_snd _ _ _
    exact ⟨aZ, haZq⟩
  have hsurj : Surjective q := q.surjective_of_lifts_algClosedPoints hlift
  let qOver : Over.mk zU ⟶ Over.mk (pullback.snd (W.ι ≫ P.obj.hom) U.ι) :=
    Over.homMk q hqU
  let : Surjective qOver.left := hsurj
  let : IsProper (Over.mk zU).hom :=
    inferInstanceAs (IsProper (pullback.snd (parameter p g).hom U.ι))
  let : IsSeparated (Over.mk (pullback.snd (W.ι ≫ P.obj.hom) U.ι)).hom :=
    inferInstanceAs (IsSeparated (pullback.snd (W.ι ≫ P.obj.hom) U.ι))
  let : LocallyOfFiniteType (Over.mk (pullback.snd (W.ι ≫ P.obj.hom) U.ι)).hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd (W.ι ≫ P.obj.hom) U.ι))
  have hproper : IsProper (pullback.snd (W.ι ≫ P.obj.hom) U.ι) :=
    Scheme.isProper_of_surjective_over_proper qOver
  exact ⟨U, φ, hx, fun F _ t ht => (hU F t ht).1, hproper⟩

include o ho in
/-- The properness-only interface is the projection of the strengthened
construction, with exactly the same neighbourhood and Euler stratum. -/
theorem exists_neighbourhood_isProper_eulerStratum
    [IsSeparated P.obj.hom] [LocallyOfFiniteType P.obj.hom]
    (x : Spec (.of A)) :
    ∃ (U : (Spec (.of A)).Opens) (φ : Polynomial ℚ), x ∈ U ∧
      IsProper (pullback.snd
        (((Strata.eulerCondition i N e φ).opens (T := P.obj)
          (R.homEquiv (𝟙 P))).ι ≫ P.obj.hom) U.ι) := by
  obtain ⟨U, φ, hx, _, hproper⟩ :=
    exists_neighbourhood_isProper_eulerStratum_and_unit i e o ho P R x
  exact ⟨U, φ, hx, hproper⟩

end Abel.BoundedFamily

end AlgebraicGeometry.Scheme.OverField.Curve
