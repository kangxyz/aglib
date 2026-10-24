/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Abel.BoundedFamily.TorsionLocus.FiniteCover
public import Aglib.AlgebraicGeometry.Curves.Abel.BoundedFamily.TorsionLocus.Parameters

/-! # Every original torsion bundle occurs in a finite actual Kummer family

An actual rational parameter lifts through one of the covering open immersions.
The original Cartesian family square then gives a literal fibre map from the
original curve, not only from its identity-base copy. The original geometric
H1 pullback of the chart class has exactly the prescribed original Picard image.
The two composites to the original curve and ground field are literally identities.

The index of the covering families is finite. Their sets of fibre values are
not asserted finite here, and no proper-base-change statement is used.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.EtaleCohomology
open GroupCohomology.Kummer.Coefficients

attribute [local instance] hasSheafifyLarge HasExt.standard

universe u v w

namespace AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily

variable {k : Type u} [Field k] (X : FScheme k)
  [SmoothOfRelativeDimension 1 X.hom] [IsProper X.hom]
  (o : Spec (.of k) ⟶ X.left) (ho : o ≫ X.hom = 𝟙 _)

namespace LocalKummerChart

variable {X o ho} {g n : ℕ} (C : LocalKummerChart X o ho g n)

/-- The actual structure map of the chart base to the original ground field. -/
def structureMap : C.base ⟶ Spec (.of k) :=
  C.baseMap ≫
    (powerNonvanishingι X.hom o ho g n ≫ (parameter X.hom g).hom)

/-- The actual projection of the chart total space to the original curve. -/
def curveMap : C.totalSpace ⟶ X.left :=
  C.totalMap ≫ pullback.fst X.hom
    (powerNonvanishingι X.hom o ho g n ≫ (parameter X.hom g).hom)

/-- The chart family is the original curve's actual constant-family base change. -/
theorem isPullback_curveMap :
    IsPullback C.curveMap C.projection X.hom C.structureMap :=
  C.isPullback.paste_horiz (IsPullback.of_hasPullback X.hom
    (powerNonvanishingι X.hom o ho g n ≫ (parameter X.hom g).hom))

/-- Every actual chart base is Noetherian, hence quasicompact and quasiseparated. -/
instance base_isNoetherian : IsNoetherian C.base := by
  let : IsLocallyNoetherian C.base := isLocallyNoetherian_of_isOpenImmersion C.baseMap
  let : TopologicalSpace.NoetherianSpace C.base :=
    C.baseMap.isOpenEmbedding.isInducing.noetherianSpace
  exact ⟨⟩

/-- The chart's literal line bundle is pulled back along its original total map. -/
theorem lineBundle_class :
    classOf C.totalSpace C.lineBundle =
      pullbackClass C.totalMap (classOf _ (locusLineBundle X o ho g n)) := by
  let f := pullback.snd (powerLocusProjection X o ho g n) C.map
  let a := pullback.fst (powerLocusProjection X o ho g n) C.map
  change pullbackClass (f ⁻¹ᵁ C.openSet).ι
      (pullbackClass a (classOf _ (locusLineBundle X o ho g n))) =
    pullbackClass ((f ⁻¹ᵁ C.openSet).ι ≫ a)
      (classOf _ (locusLineBundle X o ho g n))
  exact (pullbackClass_comp _ _ _).symm

/-- The original constant level is invertible on the actual chart total space. -/
theorem levelInvertible (hunit : IsUnit (n : k)) :
    IsUnit (n : Γ(C.totalSpace, ⊤)) :=
  locusChartOpen_levelInvertible X o ho g n C.map C.openSet hunit

/-- The chosen actual chart class retains its literal Picard image under every
original geometric cohomology pullback, with an independent target Ext universe. -/
theorem cohomologyClass_pullback_image (hn : 0 < n) (hunit : IsUnit (n : k))
    {S : Scheme.{u}} [HasExt.{w} (AbelianSheaf.{u, u + 1} S)]
    (a : S ⟶ C.totalSpace) :
    Sheaf.H.map (inclusion S n) 1
        (EtaleCohomology.Kummer.rootsCohomologyPullback a n hn
          (C.levelInvertible hunit) 1 C.cohomologyClass) =
      EtaleCohomology.Picard.picardCohomologyEquiv S
        (pullbackClass a (classOf C.totalSpace C.lineBundle)) :=
  EtaleCohomology.Picard.kummerPreimage_pullback a C.lineBundle n hn
    (C.levelInvertible hunit) C.cohomologyClass C.cohomologyClass_image

end LocalKummerChart

variable [IsAlgClosed k]

/-- Every original positive-n torsion line bundle is the literal fibre class
of one actual covering chart. The source of the Cartesian square is the
original curve; both original projection composites are identities.
No separate degree-zero premise is needed. -/
theorem exists_chart_fibre_of_class_nsmul_eq_zero (hX : Properties X)
    (n : ℕ) (hn : 0 < n) {ι : Type v}
    (C : ι → LocalKummerChart X o ho (coherentGenus k X) n)
    (hC : ∀ z, ∃ i, z ∈ Set.range (C i).baseMap)
    (L : LineBundle X.left) (hL : n • classOf X.left L = 0) :
    ∃ (i : ι) (b : Spec (.of k) ⟶ (C i).base) (a : X.left ⟶ (C i).totalSpace),
      IsPullback a X.hom (C i).projection b ∧
        b ≫ (C i).structureMap = 𝟙 _ ∧ a ≫ (C i).curveMap = 𝟙 _ ∧
        pullbackClass a (classOf (C i).totalSpace (C i).lineBundle) = classOf X.left L := by
  obtain ⟨z, hz, ⟨e⟩⟩ :=
    exists_powerLocus_parameter_of_class_nsmul_eq_zero X o ho hX L n hn hL
  obtain ⟨i, hi⟩ := hC (z (IsLocalRing.closedPoint k))
  have hzr : Set.range z ⊆ Set.range (C i).baseMap := by
    rintro _ ⟨s, rfl⟩
    have hs : s = IsLocalRing.closedPoint k := Subsingleton.elim _ _
    subst s
    exact hi
  let b := IsOpenImmersion.lift (C i).baseMap z hzr
  have hb : b ≫ (C i).baseMap = z := IsOpenImmersion.lift_fac _ _ _
  let g := coherentGenus k X
  let t := powerNonvanishingι X.hom o ho g n ≫ (parameter X.hom g).hom
  let f := pullback.fst X.hom (𝟙 (Spec (.of k)))
  let p := pullback.snd X.hom (𝟙 (Spec (.of k)))
  have hzt : z ≫ t = 𝟙 _ := by simpa only [Category.assoc] using hz
  have hbS : b ≫ (C i).structureMap = 𝟙 _ := by
    change b ≫ ((C i).baseMap ≫ t) = 𝟙 _
    rw [← Category.assoc, hb, hzt]
  let m := Hom.familyMap X.hom t (𝟙 _) z hzt
  let j := Hom.familyMap X.hom (parameter X.hom g).hom t
    (powerNonvanishingι X.hom o ho g n) rfl
  let r := Hom.familyMap X.hom (parameter X.hom g).hom (𝟙 _)
    (z ≫ powerNonvanishingι X.hom o ho g n) hz
  have hmj : m ≫ j = r :=
    Hom.familyMap_comp X.hom (parameter X.hom g).hom t (𝟙 _)
      (powerNonvanishingι X.hom o ho g n) z rfl hzt
  have hp : f ≫ X.hom = p := by
    simpa only [Category.comp_id] using pullback.condition (f := X.hom) (g := 𝟙 (Spec (.of k)))
  have hdp : inv f ≫ p = X.hom := by
    calc
      inv f ≫ p = inv f ≫ f ≫ X.hom := by rw [hp]
      _ = X.hom := by simp
  have hid : IsPullback (inv f) X.hom p (𝟙 (Spec (.of k))) :=
    IsPullback.of_horiz_isIso ⟨by simpa only [Category.comp_id] using hdp⟩
  have hm : IsPullback m p (powerLocusProjection X o ho g n) z :=
    Hom.familyMap_isPullback X.hom t (𝟙 _) z hzt
  have hout : IsPullback (inv f ≫ m) X.hom
      (powerLocusProjection X o ho g n) (b ≫ (C i).baseMap) := by
    rw [hb]
    simpa only [Category.id_comp] using hid.paste_horiz hm
  let a := (C i).isPullback.lift (inv f ≫ m) (X.hom ≫ b)
    (by rw [hout.w, Category.assoc])
  have hat : a ≫ (C i).totalMap = inv f ≫ m := (C i).isPullback.lift_fst _ _ _
  have hpb : IsPullback a X.hom (C i).projection b := hout.of_right' (C i).isPullback
  have hmf : m ≫ pullback.fst X.hom t = f := Hom.familyMap_fst _ _ _ _ _
  have haX : a ≫ (C i).curveMap = 𝟙 _ := by
    change a ≫ ((C i).totalMap ≫ pullback.fst X.hom t) = 𝟙 _
    rw [← Category.assoc, hat, Category.assoc, hmf, IsIso.inv_hom_id]
  let c := classOf _ (lineBundle X.hom o ho g)
  have he : pullbackClass f (classOf X.left L) = pullbackClass r c :=
    (class_eq_iff _ _ _).mpr ⟨e⟩
  refine ⟨i, b, a, hpb, hbS, haX, ?_⟩
  calc
    pullbackClass a (classOf (C i).totalSpace (C i).lineBundle) =
        pullbackClass a (pullbackClass (C i).totalMap (pullbackClass j c)) := by
      rw [(C i).lineBundle_class]
      rfl
    _ = pullbackClass ((a ≫ (C i).totalMap) ≫ j) c := by
      rw [pullbackClass_comp, pullbackClass_comp]
    _ = pullbackClass (inv f ≫ r) c := by rw [hat, Category.assoc, hmj]
    _ = pullbackClass (inv f) (pullbackClass f (classOf X.left L)) := by
      rw [pullbackClass_comp, ← he]
    _ = classOf X.left L := by
      rw [← pullbackClass_comp, IsIso.inv_hom_id, pullbackClass_id]

/-- Original geometric restrictions of the covering Kummer classes realize
every original torsion line-bundle class through the original inclusion map. -/
theorem exists_chart_kummer_pullback_of_class_nsmul_eq_zero (hX : Properties X)
    (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k)) {ι : Type v}
    (C : ι → LocalKummerChart X o ho (coherentGenus k X) n)
    (hC : ∀ z, ∃ i, z ∈ Set.range (C i).baseMap)
    (L : LineBundle X.left) (hL : n • classOf X.left L = 0) :
    ∃ (i : ι) (b : Spec (.of k) ⟶ (C i).base) (a : X.left ⟶ (C i).totalSpace),
      IsPullback a X.hom (C i).projection b ∧
        b ≫ (C i).structureMap = 𝟙 _ ∧ a ≫ (C i).curveMap = 𝟙 _ ∧
        Sheaf.H.map (inclusion X.left n) 1
            (EtaleCohomology.Kummer.rootsCohomologyPullback a n hn
              ((C i).levelInvertible hunit) 1 (C i).cohomologyClass) =
          EtaleCohomology.Picard.picardCohomologyEquiv X.left (classOf X.left L) := by
  obtain ⟨i, b, a, hpb, hbS, haX, ha⟩ :=
    exists_chart_fibre_of_class_nsmul_eq_zero X o ho hX n hn C hC L hL
  exact ⟨i, b, a, hpb, hbS, haX, ((C i).cohomologyClass_pullback_image hn hunit a).trans
    (congrArg (EtaleCohomology.Picard.picardCohomologyEquiv X.left) ha)⟩

/-- Finitely many actual proper local families, with actual original Kummer
classes, supply every original n-torsion line bundle as a literal fibre image.
This is not finiteness of the set of those fibre images. -/
theorem exists_finite_kummer_families_realizing_torsion (hX : Properties X)
    (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k)) :
    ∃ (s : Finset (powerNonvanishingLocus X.hom o ho (coherentGenus k X) n))
      (C : s → LocalKummerChart X o ho (coherentGenus k X) n),
      (∀ z, ∃ i, z ∈ Set.range (C i).baseMap) ∧
      ∀ (L : LineBundle X.left), n • classOf X.left L = 0 →
        ∃ (i : s) (b : Spec (.of k) ⟶ (C i).base) (a : X.left ⟶ (C i).totalSpace),
          IsPullback a X.hom (C i).projection b ∧
            b ≫ (C i).structureMap = 𝟙 _ ∧ a ≫ (C i).curveMap = 𝟙 _ ∧
            Sheaf.H.map (inclusion X.left n) 1
                (EtaleCohomology.Kummer.rootsCohomologyPullback a n hn
                  ((C i).levelInvertible hunit) 1 (C i).cohomologyClass) =
              EtaleCohomology.Picard.picardCohomologyEquiv X.left (classOf X.left L) := by
  obtain ⟨s, C, hC⟩ :=
    exists_finite_localKummerCharts X o ho (coherentGenus k X) n hX hn hunit
  exact ⟨s, C, hC, fun L hL =>
    exists_chart_kummer_pullback_of_class_nsmul_eq_zero X o ho hX n hn hunit C hC L hL⟩

end AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily
