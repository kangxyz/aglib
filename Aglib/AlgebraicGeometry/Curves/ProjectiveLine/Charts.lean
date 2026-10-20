/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.Structure
public import Aglib.AlgebraicGeometry.Gluing.OpenImmersion
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring

/-!
# Literal homogeneous projective-line charts

The actual homogeneous Proj, two polynomial charts, inverse transition and chart
cover over an arbitrary commutative ring. The final pushout-isomorphism criterion
concerns arbitrary schemes glued along open immersions. Source:
`R5Lab.Aglib.AlgebraicGeometry.Curves.ProjectiveLine.Charts` at R5Lab revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`; all construction/proof bodies retained.
-/

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Polynomial
open scoped Polynomial
universe u

namespace AlgebraicGeometry.Scheme
variable (k : Type u) [Field k]
section ProjectiveComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace ProjectiveLine
variable (k : Type u) [CommRing k]
attribute [local instance] MvPolynomial.gradedAlgebra
abbrev grading := MvPolynomial.homogeneousSubmodule (Fin 2) k
abbrev projectiveP1 : Scheme := Proj (grading k)
instance scalarTower : IsScalarTower k (grading k 0) (MvPolynomial (Fin 2) k) :=
  IsScalarTower.of_algebraMap_eq (R := k) (S := grading k 0) (A := MvPolynomial (Fin 2) k) fun _
    => rfl
instance finiteTypeGradeZero : Algebra.FiniteType (grading k 0) (MvPolynomial (Fin 2) k) :=
  Algebra.FiniteType.of_restrictScalars_finiteType k _ _

def constToGradeZero : k →+* grading k 0 := algebraMap k (grading k 0)
lemma constToGradeZero_bijective : Function.Bijective (constToGradeZero k) := by
  constructor
  · intro x y h
    have h' : MvPolynomial.C x = (MvPolynomial.C y : MvPolynomial (Fin 2) k) :=
      congrArg Subtype.val h
    exact MvPolynomial.C_injective (Fin 2) k h'
  · intro x
    refine ⟨MvPolynomial.constantCoeff x.val, ?_⟩
    apply Subtype.ext
    change MvPolynomial.C (x.val.coeff 0) = x.val
    symm
    exact MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp
      ((MvPolynomial.totalDegree_zero_iff_isHomogeneous (Fin 2)).mpr x.property)

def gradeZeroIso : k ≃+* grading k 0 :=
  RingEquiv.ofBijective (constToGradeZero k) (constToGradeZero_bijective k)

def structureMap : projectiveP1 k ⟶ Spec (.of k) :=
  Proj.toSpecZero (grading k) ≫ Spec.map (CommRingCat.ofHom (constToGradeZero k))
instance structureMap_proper : IsProper (structureMap k) := by
  have : IsIso (Spec.map (CommRingCat.ofHom (constToGradeZero k))) := by
    change IsIso (Scheme.Spec.mapIso (gradeZeroIso k).toCommRingCatIso.op).hom
    infer_instance
  unfold structureMap
  infer_instance

abbrev chartRing (i : Fin 2) :=
  HomogeneousLocalization.Away (grading k) (MvPolynomial.X i)

def dehomogenizePolynomial (i : Fin 2) : MvPolynomial (Fin 2) k →+* k[X] :=
  MvPolynomial.eval₂Hom Polynomial.C (fun j => if j = i then 1 else Polynomial.X)

@[simp] lemma dehomogenizePolynomial_X_self (i : Fin 2) :
    dehomogenizePolynomial k i (MvPolynomial.X i) = 1 := by
  simp [dehomogenizePolynomial]

def dehomogenize (i : Fin 2) : chartRing k i →+* k[X] :=
  (Localization.awayLift (dehomogenizePolynomial k i) (MvPolynomial.X i)
    (by simp)).comp (algebraMap (chartRing k i)
      (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin 2) k)))

/-- Bijectivity of the canonical standard-projective-chart algebra map.
This property is proved for every commutative ring below by
`standardChartBijection_proved` and registered as an instance. It is therefore
not an independent premise of the actual properness results. -/
class StandardChartBijection : Prop where
  bijective : ∀ i : Fin 2, Function.Bijective (dehomogenize k i)

def chart (i : Fin 2) : Spec (.of k[X]) ⟶ projectiveP1 k :=
  Spec.map (CommRingCat.ofHom (dehomogenize k i)) ≫
    Proj.awayι (grading k) (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X k i) (by decide)

instance chart_open [h : StandardChartBijection k] (i : Fin 2) :
    IsOpenImmersion (chart k i) := by
  let e := RingEquiv.ofBijective (dehomogenize k i) (h.bijective i)
  have : IsIso (Spec.map (CommRingCat.ofHom (dehomogenize k i))) := by
    change IsIso (Scheme.Spec.mapIso e.toCommRingCatIso.op).hom
    infer_instance
  exact IsOpenImmersion.comp _ _

lemma chart_opensRange [h : StandardChartBijection k] (i : Fin 2) :
    (chart k i).opensRange = Proj.basicOpen (grading k) (MvPolynomial.X i) := by
  let e := RingEquiv.ofBijective (dehomogenize k i) (h.bijective i)
  have : IsIso (Spec.map (CommRingCat.ofHom (dehomogenize k i))) := by
    change IsIso (Scheme.Spec.mapIso e.toCommRingCatIso.op).hom
    infer_instance
  exact (Scheme.Hom.opensRange_comp_of_isIso _ _).trans
    (Proj.opensRange_awayι _ _ _ _)

lemma adjoin_variables :
    Algebra.adjoin (grading k 0) (Set.range (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) k)) = ⊤
      := by
  set S := Algebra.adjoin (grading k 0)
    (Set.range (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) k))
  refine top_unique fun p hp => ?_
  clear hp
  induction p using MvPolynomial.induction_on with
  | C r => exact S.algebraMap_mem (constToGradeZero k r)
  | add p q hp hq => exact S.add_mem hp hq
  | mul_X p i hp => exact S.mul_mem hp (Algebra.subset_adjoin (Set.mem_range_self i))

lemma basicCharts_cover :
    ⨆ i : Fin 2, Proj.basicOpen (grading k) (MvPolynomial.X i) = ⊤ :=
  Proj.iSup_basicOpen_eq_top' _ _ (fun i => ⟨1, MvPolynomial.isHomogeneous_X k i⟩)
    (adjoin_variables k)

lemma chart_covered [StandardChartBijection k] (z : projectiveP1 k) :
    ∃ (i : Fin 2) (x : Spec (.of k[X])), chart k i x = z := by
  have hz : z ∈ ⨆ i : Fin 2, Proj.basicOpen (grading k) (MvPolynomial.X i) := by
    rw [basicCharts_cover]
    trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hz
  rw [← chart_opensRange k i] at hi
  exact ⟨i, hi⟩

lemma dehomogenize_mk (i : Fin 2) (n : ℕ) (a : MvPolynomial (Fin 2) k)
    (ha : a ∈ grading k (n • 1)) :
    dehomogenize k i (HomogeneousLocalization.Away.mk (grading k)
      (MvPolynomial.isHomogeneous_X k i) n a ha) = dehomogenizePolynomial k i a := by
  simpa only [dehomogenize, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.Away.val_mk, one_pow, mul_one] using
    Localization.awayLift_mk (dehomogenizePolynomial k i) (MvPolynomial.X i) a 1 (by simp) n

lemma dehomogenize_constant (i : Fin 2) (r : k) :
    dehomogenize k i (HomogeneousLocalization.fromZeroRingHom (grading k)
      (Submonoid.powers (MvPolynomial.X i)) (constToGradeZero k r)) = Polynomial.C r := by
  change dehomogenize k i (HomogeneousLocalization.Away.mk (grading k)
    (MvPolynomial.isHomogeneous_X k i) 0 (MvPolynomial.C r) _) = _
  rw [dehomogenize_mk]
  simp [dehomogenizePolynomial]

@[reassoc] lemma chart_over (i : Fin 2) :
    chart k i ≫ structureMap k = Spec.map (CommRingCat.ofHom (algebraMap k k[X])) := by
  rw [chart, structureMap, Category.assoc, ← Category.assoc _ (Proj.toSpecZero _),
    Proj.awayι_toSpecZero, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact dehomogenize_constant k i r


def chartConstant (i : Fin 2) : k →+* chartRing k i :=
  (HomogeneousLocalization.fromZeroRingHom (grading k)
    (Submonoid.powers (MvPolynomial.X i))).comp (constToGradeZero k)

def chartRatio (i : Fin 2) : chartRing k i :=
  HomogeneousLocalization.Away.mk (grading k) (MvPolynomial.isHomogeneous_X k i) 1
    (MvPolynomial.X i.rev) (by simpa using MvPolynomial.isHomogeneous_X k i.rev)

@[simp] lemma dehomogenize_chartConstant (i : Fin 2) (r : k) :
    dehomogenize k i (chartConstant k i r) = Polynomial.C r :=
  dehomogenize_constant k i r

@[simp] lemma dehomogenize_chartRatio (i : Fin 2) :
    dehomogenize k i (chartRatio k i) = Polynomial.X := by
  rw [chartRatio, dehomogenize_mk]
  have hi : i.rev ≠ i := by fin_cases i <;> decide
  simp [dehomogenizePolynomial, hi]

def rehomogenize (i : Fin 2) : k[X] →+* chartRing k i :=
  Polynomial.eval₂RingHom (chartConstant k i) (chartRatio k i)

lemma dehomogenize_rehomogenize (i : Fin 2) :
    (dehomogenize k i).comp (rehomogenize k i) = RingHom.id _ := by
  apply Polynomial.ringHom_ext
  · intro r
    simp [rehomogenize]
  · simp [rehomogenize]

def rehomogenizeEnd (i : Fin 2) : chartRing k i →ₐ[grading k 0] chartRing k i where
  __ := (rehomogenize k i).comp (dehomogenize k i)
  commutes' r := by
    obtain ⟨c, rfl⟩ := (constToGradeZero_bijective k).surjective r
    change rehomogenize k i (dehomogenize k i (chartConstant k i c)) = chartConstant k i c
    simp [rehomogenize]

lemma rehomogenizeEnd_eq_id (i : Fin 2) :
    rehomogenizeEnd k i = AlgHom.id (grading k 0) (chartRing k i) := by
  apply AlgHom.ext_of_adjoin_eq_top
    (HomogeneousLocalization.Away.adjoin_mk_prod_pow_eq_top
      (MvPolynomial.isHomogeneous_X k i) (Fin 2) MvPolynomial.X
      (adjoin_variables k) (fun _ => 1) (MvPolynomial.isHomogeneous_X k))
  rintro x ⟨a, ai, hai, hbound, rfl⟩
  change rehomogenize k i (dehomogenize k i _) = _
  rw [dehomogenize_mk]
  have ha : a = ai 0 + ai 1 := by simpa [Fin.sum_univ_two] using hai.symm
  subst a
  have h0 := hbound 0
  have h1 := hbound 1
  simp only [dehomogenizePolynomial, map_prod, map_pow, MvPolynomial.eval₂Hom_X']
  simp only [Fin.prod_univ_two]
  apply HomogeneousLocalization.val_injective
  simp only [AlgHom.id_apply, HomogeneousLocalization.Away.val_mk]
  clear hai hbound
  generalize h0' : ai 0 = a0 at *
  generalize h1' : ai 1 = a1 at *
  interval_cases a0 <;> interval_cases a1 <;> fin_cases i <;>
    simp only [Fin.zero_eta, Fin.isValue, rehomogenize, chartRatio, Fin.rev, zero_add,
      Nat.add_one_sub_one, Fin.mk_one, ↓reduceIte, coe_eval₂RingHom, eval₂_one, pow_zero,
      one_ne_zero, eval₂_X, mul_one, HomogeneousLocalization.val_one, add_zero,
      Localization.mk_self_mk, Nat.reduceAdd, tsub_self, zero_ne_one, pow_one, one_mul,
      HomogeneousLocalization.Away.val_mk]
  all_goals
    try rw [← Localization.mk_one]
    rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    exact ⟨1, by simp; ring⟩

lemma standardChartBijection_proved : StandardChartBijection k := by
  constructor
  intro i
  have hfg := DFunLike.congr_fun (dehomogenize_rehomogenize k i)
  have hgf := DFunLike.congr_fun (rehomogenizeEnd_eq_id k i)
  constructor
  · intro a b hab
    have h := congrArg (rehomogenize k i) hab
    exact (hgf a).symm.trans (h.trans (hgf b))
  · intro p
    exact ⟨rehomogenize k i p, hfg p⟩

instance standardChartBijection : StandardChartBijection k := standardChartBijection_proved k

lemma rehomogenize_dehomogenize [h : StandardChartBijection k] (i : Fin 2)
    (x : chartRing k i) : rehomogenize k i (dehomogenize k i x) = x := by
  apply (h.bijective i).injective
  exact DFunLike.congr_fun (dehomogenize_rehomogenize k i) (dehomogenize k i x)

lemma chartRing_hom_ext [StandardChartBijection k] (i : Fin 2)
    {S : Type*} [CommRing S] {f g : chartRing k i →+* S}
    (hC : ∀ r, f (chartConstant k i r) = g (chartConstant k i r))
    (hX : f (chartRatio k i) = g (chartRatio k i)) : f = g := by
  have h : f.comp (rehomogenize k i) = g.comp (rehomogenize k i) := by
    apply Polynomial.ringHom_ext
    · intro r
      simpa [rehomogenize] using hC r
    · simpa [rehomogenize] using hX
  ext x
  simpa only [RingHom.comp_apply, rehomogenize_dehomogenize] using
    DFunLike.congr_fun h (dehomogenize k i x)

abbrev chartOverlapRing := HomogeneousLocalization.Away (grading k)
  (MvPolynomial.X 0 * MvPolynomial.X 1)

def overlapMap0 : chartRing k 0 →+* chartOverlapRing k :=
  HomogeneousLocalization.awayMap (grading k) (MvPolynomial.isHomogeneous_X k 1) rfl

def overlapMap1 : chartRing k 1 →+* chartOverlapRing k :=
  HomogeneousLocalization.awayMap (grading k) (MvPolynomial.isHomogeneous_X k 0) (mul_comm _ _)

lemma overlap_ratio_mul : overlapMap0 k (chartRatio k 0) * overlapMap1 k (chartRatio k 1) = 1 := by
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.val_mul, overlapMap0, overlapMap1, chartRatio,
    HomogeneousLocalization.awayMap_mk, HomogeneousLocalization.Away.val_mk,
    HomogeneousLocalization.val_one, Localization.mk_mul]
  rw [← Localization.mk_one, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul, Submonoid.mk_mul_mk,
    show (0 : Fin 2).rev = 1 from rfl, show (1 : Fin 2).rev = 0 from rfl, pow_one]
  ring


instance overlapMap0_algebra : Algebra (chartRing k 0) (chartOverlapRing k) :=
  (overlapMap0 k).toAlgebra

instance overlapMap0_localization :
    IsLocalization.Away (chartRatio k 0) (chartOverlapRing k) := by
  simpa only [HomogeneousLocalization.Away.isLocalizationElem, chartRatio, pow_one,
    show (0 : Fin 2).rev = 1 from rfl, overlapMap0_algebra, overlapMap0] using
    (HomogeneousLocalization.Away.isLocalization_mul (𝒜 := grading k)
      (f := MvPolynomial.X (0 : Fin 2)) (g := MvPolynomial.X (1 : Fin 2))
      (x := MvPolynomial.X 0 * MvPolynomial.X 1)
      (MvPolynomial.isHomogeneous_X k (0 : Fin 2))
      (MvPolynomial.isHomogeneous_X k (1 : Fin 2)) rfl (by decide : (1 : ℕ) ≠ 0))

variable (S : Type u) [CommRing S] [Algebra k S]

def chartValue (i : Fin 2) (s : S) : chartRing k i →+* S :=
  (Polynomial.aeval s).toRingHom.comp (dehomogenize k i)

@[simp] lemma chartValue_constant (i : Fin 2) (s : S) (r : k) :
    chartValue k S i s (chartConstant k i r) = algebraMap k S r := by
  simp [chartValue]

@[simp] lemma chartValue_ratio (i : Fin 2) (s : S) :
    chartValue k S i s (chartRatio k i) = s := by
  simp [chartValue]

def overlapValue (u : Sˣ) : chartOverlapRing k →+* S :=
  IsLocalization.Away.lift (chartRatio k 0)
    (g := chartValue k S 0 (u : S)) (by simp)

@[simp] lemma overlapValue_map0 (u : Sˣ) (x : chartRing k 0) :
    overlapValue k S u (overlapMap0 k x) = chartValue k S 0 (u : S) x :=
  IsLocalization.Away.lift_eq (chartRatio k 0) (by simp) x

lemma overlapMap_constant (r : k) :
    overlapMap1 k (chartConstant k 1 r) = overlapMap0 k (chartConstant k 0 r) := by
  simp [overlapMap0, overlapMap1, chartConstant, HomogeneousLocalization.awayMap_fromZeroRingHom]

lemma overlapValue_map1_ratio (u : Sˣ) :
    overlapValue k S u (overlapMap1 k (chartRatio k 1)) = (↑u⁻¹ : S) := by
  apply u.isUnit.mul_left_cancel
  calc
    (u : S) * overlapValue k S u (overlapMap1 k (chartRatio k 1)) =
        overlapValue k S u (overlapMap0 k (chartRatio k 0) *
          overlapMap1 k (chartRatio k 1)) := by simp
    _ = 1 := by rw [overlap_ratio_mul, map_one]
    _ = (u : S) * (↑u⁻¹ : S) := by simp

lemma overlapValue_comp_map1 [StandardChartBijection k] (u : Sˣ) :
    (overlapValue k S u).comp (overlapMap1 k) = chartValue k S 1 (↑u⁻¹ : S) := by
  apply chartRing_hom_ext k 1
  · intro r
    simp only [RingHom.comp_apply, overlapMap_constant, overlapValue_map0,
      chartValue_constant]
  · simpa only [RingHom.comp_apply, chartValue_ratio] using overlapValue_map1_ratio k S u


lemma chart_transition [StandardChartBijection k] (u : Sˣ) :
    Spec.map (CommRingCat.ofHom (Polynomial.aeval (u : S)).toRingHom) ≫ chart k 0 =
      Spec.map (CommRingCat.ofHom (Polynomial.aeval (↑u⁻¹ : S)).toRingHom) ≫ chart k 1 := by
  have h0 : (overlapValue k S u).comp (overlapMap0 k) = chartValue k S 0 (u : S) :=
    RingHom.ext (overlapValue_map0 k S u)
  have h1 := overlapValue_comp_map1 k S u
  simp only [chart, ← Category.assoc, ← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom (chartValue k S 0 (u : S))) ≫ _ =
    Spec.map (CommRingCat.ofHom (chartValue k S 1 (↑u⁻¹ : S))) ≫ _
  rw [← h0, ← h1]
  simp only [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, overlapMap0, overlapMap1,
    Proj.SpecMap_awayMap_awayι]

lemma chart_preimage_linear (i : Fin 2) (g : MvPolynomial (Fin 2) k)
    (hg : g ∈ grading k 1) :
    chart k i ⁻¹ᵁ Proj.basicOpen (grading k) g =
      PrimeSpectrum.basicOpen (dehomogenizePolynomial k i g) := by
  rw [chart, Scheme.Hom.comp_preimage,
    Proj.awayι_preimage_basicOpen _ (MvPolynomial.isHomogeneous_X k i) (by decide)
      hg (by decide), SpecMap_preimage_basicOpen]
  congr 1
  simp [HomogeneousLocalization.Away.isLocalizationElem, dehomogenize_mk]

end ProjectiveLine

namespace OpenPushoutIso
variable {W U V Z : Scheme.{u}} (f : W ⟶ U) (g : W ⟶ V)
    [IsOpenImmersion f] [IsOpenImmersion g]
    (jU : U ⟶ Z) (jV : V ⟶ Z) [hjU : IsOpenImmersion jU] [IsOpenImmersion jV]
    (comm : f ≫ jU = g ≫ jV)
    (preimage : jU ⁻¹ᵁ jV.opensRange = f.opensRange)

include comm preimage

omit hjU in
lemma cross_eq [IsOpenImmersion jU] {a : U} {b : V} (h : jU a = jV b) :
    pushout.inl f g a = pushout.inr f g b := by
  have ha : a ∈ jU ⁻¹ᵁ jV.opensRange := ⟨b, h.symm⟩
  rw [preimage] at ha
  obtain ⟨w, hw⟩ := ha
  have hv : g w = b := by
    apply jV.isOpenEmbedding.injective
    calc
      jV (g w) = jU (f w) := by
        simpa only [Scheme.Hom.comp_apply] using congrArg (fun e : W ⟶ Z => e w) comm.symm
      _ = jU a := congrArg jU hw
      _ = jV b := h
  rw [← hw, ← hv]
  simpa only [Scheme.Hom.comp_apply] using
    congrArg (fun e : W ⟶ pushout f g => e w) (pushout.condition (f := f) (g := g))

lemma desc_injective : Function.Injective (pushout.desc jU jV comm) := by
  intro x y h
  rcases openPushout_covered f g x with ⟨a, rfl⟩ | ⟨a, rfl⟩ <;>
    rcases openPushout_covered f g y with ⟨b, rfl⟩ | ⟨b, rfl⟩
  · have hab : jU a = jU b := by
      simpa only [← Scheme.Hom.comp_apply, pushout.inl_desc] using h
    exact congrArg (pushout.inl f g) (jU.isOpenEmbedding.injective hab)
  · have hab : jU a = jV b := by
      simpa only [← Scheme.Hom.comp_apply, pushout.inl_desc, pushout.inr_desc] using h
    exact cross_eq f g jU jV comm preimage hab
  · have hab : jU b = jV a := by
      simpa only [← Scheme.Hom.comp_apply, pushout.inl_desc, pushout.inr_desc] using h.symm
    exact (cross_eq f g jU jV comm preimage hab).symm
  · have hab : jV a = jV b := by
      simpa only [← Scheme.Hom.comp_apply, pushout.inr_desc] using h
    exact congrArg (pushout.inr f g) (jV.isOpenEmbedding.injective hab)

lemma desc_open : IsOpenImmersion (pushout.desc jU jV comm) := by
  apply IsOpenImmersion.of_forall_source_exists _ (desc_injective f g jU jV comm preimage)
  intro x
  rcases openPushout_covered f g x with ⟨a, ha⟩ | ⟨b, hb⟩
  · refine ⟨U, pushout.inl f g, inferInstance, ⟨a, ha⟩, ?_⟩
    simpa using (inferInstance : IsOpenImmersion jU)
  · refine ⟨V, pushout.inr f g, inferInstance, ⟨b, hb⟩, ?_⟩
    simpa using (inferInstance : IsOpenImmersion jV)

lemma desc_isIso (cover : ∀ z : Z, (∃ a, jU a = z) ∨ ∃ b, jV b = z) :
    IsIso (pushout.desc jU jV comm) := by
  have := desc_open f g jU jV comm preimage
  have : AlgebraicGeometry.Surjective (pushout.desc jU jV comm) := ⟨by
    intro z
    rcases cover z with ⟨a, ha⟩ | ⟨b, hb⟩
    · refine ⟨pushout.inl f g a, ?_⟩
      simpa only [← Scheme.Hom.comp_apply, pushout.inl_desc] using ha
    · refine ⟨pushout.inr f g b, ?_⟩
      simpa only [← Scheme.Hom.comp_apply, pushout.inr_desc] using hb⟩
  exact (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, inferInstance⟩

end OpenPushoutIso

end ProjectiveComparison
end AlgebraicGeometry.Scheme
