/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.ProjectiveLine.Charts
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor

/-!
# Coordinates for two rational points of the projective line

Two distinct actual sections over the original field determine an automorphism
of the native projective line taking them to affine coordinates zero and one.
The construction allows an infinite endpoint and proves the actual morphism triangles.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Polynomial Matrix
open scoped Polynomial
universe u

namespace AlgebraicGeometry.Scheme.ProjectiveLine.TwoPoints

variable (k : Type u) [Field k]

/-- The rational section with affine parameter `a` in the native projective-line chart indexed
by `i`. -/
def point (i : Fin 2) (a : k) : Spec (.of k) ⟶ ProjectiveLine.projectiveP1 k :=
  Spec.map (CommRingCat.ofHom (evalRingHom a)) ≫ ProjectiveLine.chart k i

@[reassoc] lemma point_over (i : Fin 2) (a : k) :
    point k i a ≫ ProjectiveLine.structureMap k = 𝟙 _ := by
  rw [point, Category.assoc, ProjectiveLine.chart_over]
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1
  ext x
  simp

/-- An affine section over the ORIGINAL field is evaluation at its parameter.
Without the base triangle the ring map can twist the coefficient field. -/
lemma affineSection_is_evaluation
    (t : Spec (.of k) ⟶ Spec (.of k[X]))
    (ht : t ≫ Spec.map (CommRingCat.ofHom (algebraMap k k[X])) = 𝟙 _) :
    ∃ a : k, t = Spec.map (CommRingCat.ofHom (evalRingHom a)) := by
  let f : k[X] →+* k := (Spec.preimage t).hom
  have hf : Spec.map (CommRingCat.ofHom f) = t := Spec.map_preimage t
  have hh := ht
  rw [← hf, ← Spec.map_comp, ← Spec.map_id] at hh
  have hhom := congrArg CommRingCat.Hom.hom (Spec.map_injective hh)
  have hc (c : k) : f (C c) = c := DFunLike.congr_fun hhom c
  have heval : evalRingHom (f X) = f := by
    apply Polynomial.ringHom_ext
    · intro c
      simpa using (hc c).symm
    · simp
  refine ⟨f X, ?_⟩
  rw [← hf, heval]

/-- The actual chart is chosen using the image of the unique Spec(k) point.
The lift is a scheme morphism, not merely an equality of underlying points. -/
lemma section_has_chart
    (s : Spec (.of k) ⟶ ProjectiveLine.projectiveP1 k) (hs : s ≫ ProjectiveLine.structureMap k = 𝟙
      _) :
    ∃ (i : Fin 2) (a : k), s = point k i a := by
  obtain ⟨i, x, hx⟩ := ProjectiveLine.chart_covered k (s (default : Spec (.of k)))
  have hrange : Set.range s ⊆ Set.range (ProjectiveLine.chart k i) := by
    rintro _ ⟨z, rfl⟩
    exact ⟨x, hx.trans (congrArg s (Subsingleton.elim _ _))⟩
  let t := IsOpenImmersion.lift (ProjectiveLine.chart k i) s hrange
  have ht : t ≫ ProjectiveLine.chart k i = s :=
    IsOpenImmersion.lift_fac _ _ _
  have hb : t ≫ Spec.map (CommRingCat.ofHom (algebraMap k k[X])) = 𝟙 _ := by
    rw [← ProjectiveLine.chart_over k i, ← Category.assoc, ht, hs]
  obtain ⟨a, ha⟩ := affineSection_is_evaluation k t hb
  exact ⟨i, a, ht.symm.trans (by rw [ha]; rfl)⟩

/-- A canonical pair of chart forms: finite coordinate or the actual infinity
section. The second chart is essential and is not discarded. -/
def canonicalSection : Option k → (Spec (.of k) ⟶ ProjectiveLine.projectiveP1 k)
  | none => point k 1 0
  | some a => point k 0 a

lemma point_one_eq_finite (a : k) (ha : a ≠ 0) :
    point k 1 a = point k 0 a⁻¹ := by
  let u : kˣ := (Units.mk0 a ha)⁻¹
  have h := ProjectiveLine.chart_transition k k u
  simpa [point, u] using h.symm

lemma section_has_canonicalCoordinate
    (s : Spec (.of k) ⟶ ProjectiveLine.projectiveP1 k) (hs : s ≫ ProjectiveLine.structureMap k = 𝟙
      _) :
    ∃ a : Option k, s = canonicalSection k a := by
  obtain ⟨i, a, rfl⟩ := section_has_chart k s hs
  fin_cases i
  · exact ⟨some a, rfl⟩
  · by_cases ha : a = 0
    · subst a
      exact ⟨none, rfl⟩
    · exact ⟨some a⁻¹, point_one_eq_finite k a ha⟩

/-- Type-valued coordinates retain equality of the SAME section morphism. -/
def coordinate (s : Spec (.of k) ⟶ ProjectiveLine.projectiveP1 k) (hs : s ≫
  ProjectiveLine.structureMap k = 𝟙 _) : Option k :=
  Classical.choose (section_has_canonicalCoordinate k s hs)

lemma coordinate_section (s : Spec (.of k) ⟶ ProjectiveLine.projectiveP1 k) (hs : s ≫
  ProjectiveLine.structureMap k = 𝟙 _) :
    s = canonicalSection k (coordinate k s hs) :=
  Classical.choose_spec (section_has_canonicalCoordinate k s hs)

lemma coordinates_distinct (s t : Spec (.of k) ⟶ ProjectiveLine.projectiveP1 k)
    (hs : s ≫ ProjectiveLine.structureMap k = 𝟙 _) (ht : t ≫ ProjectiveLine.structureMap k = 𝟙 _)
      (hne : s ≠ t) :
    coordinate k s hs ≠ coordinate k t ht := by
  intro h
  apply hne
  exact (coordinate_section k s hs).trans
    ((congrArg (canonicalSection k) h).trans (coordinate_section k t ht).symm)

end AlgebraicGeometry.Scheme.ProjectiveLine.TwoPoints

namespace AlgebraicGeometry.Scheme.ProjectiveLine.TwoPoints

variable (k : Type u) [Field k]

/-- The existing chart0 has homogeneous vector (1,a); chart1 at zero has (0,1). -/
def vector : Option k → Fin 2 → k
  | none => ![0, 1]
  | some a => ![1, a]

/-- The determinant of the two chosen homogeneous vectors for the finite-or-infinite parameters
`p` and `q`. -/
def pairDet (p q : Option k) : k :=
  vector k p 0 * vector k q 1 - vector k p 1 * vector k q 0

lemma pairDet_ne_zero (p q : Option k) (hpq : p ≠ q) : pairDet k p q ≠ 0 := by
  cases p with
  | none =>
      cases q with
      | none => exact False.elim (hpq rfl)
      | some b => simp [pairDet, vector]
  | some a =>
      cases q with
      | none => simp [pairDet, vector]
      | some b =>
          have hab : b ≠ a := by
            intro h
            exact hpq (by rw [h])
          simpa [pairDet, vector] using sub_ne_zero.mpr hab

/-- Row convention: the associated pullback substitutes Xᵢ with row i.
The induced point map sends v to M*v. No assertion that infinity is fixed. -/
def pairMatrix (p q : Option k) : Matrix (Fin 2) (Fin 2) k :=
  !![vector k q 1 - vector k p 1, vector k p 0 - vector k q 0;
      -vector k p 1, vector k p 0]

lemma pairMatrix_det (p q : Option k) : (pairMatrix k p q).det = pairDet k p q := by
  simp [pairMatrix, pairDet, Matrix.det_fin_two]
  ring

/-- The first endpoint becomes (d,0), hence literal chart0 coordinate zero. -/
lemma pairMatrix_first (p q : Option k) :
    (pairMatrix k p q).mulVec (vector k p) = ![pairDet k p q, 0] := by
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    pairMatrix, pairDet] <;> ring

/-- The second endpoint becomes (d,d), hence literal chart0 coordinate one. -/
lemma pairMatrix_second (p q : Option k) :
    (pairMatrix k p q).mulVec (vector k q) = ![pairDet k p q, pairDet k p q] := by
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    pairMatrix, pairDet] <;> ring

/-- An actual GL2 element, valid over every field including characteristic two. -/
def pairGL (p q : Option k) (hpq : p ≠ q) : Matrix.GeneralLinearGroup (Fin 2) k :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (pairMatrix k p q)
    (by rw [pairMatrix_det]; exact pairDet_ne_zero k p q hpq)

end AlgebraicGeometry.Scheme.ProjectiveLine.TwoPoints

namespace AlgebraicGeometry.Scheme.ProjectiveLine.TwoPoints

variable (k : Type u) [Field k]
open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The type of two-by-two matrices over `k`. -/
abbrev Matrix2 := Matrix (Fin 2) (Fin 2) k

/-- The homogeneous linear form given by row `i` of the matrix `M`. -/
def linearForm (M : Matrix2 k) (i : Fin 2) : MvPolynomial (Fin 2) k :=
  MvPolynomial.C (M i 0) * MvPolynomial.X 0 + MvPolynomial.C (M i 1) * MvPolynomial.X 1

lemma linearForm_homogeneous (M : Matrix2 k) (i : Fin 2) :
    (linearForm k M i).IsHomogeneous 1 :=
  ((isHomogeneous_X k (0 : Fin 2)).C_mul _).add
    ((isHomogeneous_X k (1 : Fin 2)).C_mul _)

/-- The graded substitution sending each projective coordinate to the corresponding row form of
`M`. -/
def linearSubstitution (M : Matrix2 k) :
    ProjectiveLine.grading k →+*ᵍ ProjectiveLine.grading k where
  __ := MvPolynomial.eval₂Hom MvPolynomial.C (linearForm k M)
  map_mem := by
    intro n p hp
    change p.IsHomogeneous n at hp
    change (MvPolynomial.eval₂ MvPolynomial.C (linearForm k M) p).IsHomogeneous n
    simpa only [one_mul] using hp.eval₂ MvPolynomial.C (linearForm k M)
      (fun r => isHomogeneous_C _ r) (linearForm_homogeneous k M)

@[simp] lemma linearSubstitution_C (M : Matrix2 k) (a : k) :
    linearSubstitution k M (MvPolynomial.C a) = MvPolynomial.C a := by
  simp [linearSubstitution]

@[simp] lemma linearSubstitution_X (M : Matrix2 k) (i : Fin 2) :
    linearSubstitution k M (MvPolynomial.X i) = linearForm k M i := by
  simp [linearSubstitution]

lemma linearSubstitution_one :
    linearSubstitution k (1 : Matrix2 k) = GradedRingHom.id (ProjectiveLine.grading k) := by
  apply GradedRingHom.ext
  intro p
  have h : (linearSubstitution k (1 : Matrix2 k)).toRingHom = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp
    · intro i
      fin_cases i <;> simp [linearForm]
  exact DFunLike.congr_fun h p

/-- Substituting M after N gives coordinate pullback N*M. -/
lemma linearSubstitution_comp (M N : Matrix2 k) :
    (linearSubstitution k M).comp (linearSubstitution k N) =
      linearSubstitution k (N * M) := by
  apply GradedRingHom.ext
  intro p
  have h : (linearSubstitution k M).toRingHom.comp
      (linearSubstitution k N).toRingHom =
      (linearSubstitution k (N * M)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp
    · intro i
      simp [linearForm, Matrix.mul_apply, Fin.sum_univ_two, map_add, map_mul]
      ring
  exact DFunLike.congr_fun h p

lemma linearSubstitution_irrelevant_mem (M : Matrix2 k)
    (p : MvPolynomial (Fin 2) k)
    (hp : p ∈ HomogeneousIdeal.irrelevant (ProjectiveLine.grading k)) :
    linearSubstitution k M p ∈ HomogeneousIdeal.irrelevant (ProjectiveLine.grading k) := by
  rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply] at hp ⊢
  rw [← GradedRingHom.map_directSumDecompose, hp, map_zero]

/-- Invertibility, not a separately supplied irrelevant-ideal hypothesis, makes
this coordinate substitution a morphism on all of Proj. -/
lemma linearSubstitution_irrelevant_le
    (M : Matrix.GeneralLinearGroup (Fin 2) k) :
    HomogeneousIdeal.irrelevant (ProjectiveLine.grading k) ≤
      (HomogeneousIdeal.irrelevant (ProjectiveLine.grading k)).map
        (linearSubstitution k (M : Matrix2 k)) := by
  intro p hp
  have hmem := Ideal.mem_map_of_mem (linearSubstitution k (M : Matrix2 k))
    (linearSubstitution_irrelevant_mem k (M⁻¹ : Matrix.GeneralLinearGroup (Fin 2) k) p hp)
  have hcomp : (linearSubstitution k (M : Matrix2 k)).comp
      (linearSubstitution k (M⁻¹ : Matrix.GeneralLinearGroup (Fin 2) k)) =
        GradedRingHom.id (ProjectiveLine.grading k) := by
    rw [linearSubstitution_comp]
    have he : (↑(M⁻¹) : Matrix2 k) * (↑M : Matrix2 k) = 1 := by
      exact congrArg (fun x : Matrix.GeneralLinearGroup (Fin 2) k => (x : Matrix2 k))
        (inv_mul_cancel M)
    rw [he, linearSubstitution_one]
  have heval := DFunLike.congr_fun hcomp p
  change linearSubstitution k (M : Matrix2 k)
    (linearSubstitution k (M⁻¹ : Matrix.GeneralLinearGroup (Fin 2) k) p) = p at heval
  rwa [heval] at hmem

/-- The native morphism on the actual permanent Proj(k[X₀,X₁]). -/
def matrixMap (M : Matrix.GeneralLinearGroup (Fin 2) k) :
    ProjectiveLine.projectiveP1 k ⟶ ProjectiveLine.projectiveP1 k :=
  Proj.map (linearSubstitution k (M : Matrix2 k))
    (linearSubstitution_irrelevant_le k M)

/-- Equality transport for native Proj maps, with dependent irrelevant-ideal
proof arguments retained until the graded maps have been identified. -/
lemma projMap_congr
    (f g : ProjectiveLine.grading k →+*ᵍ ProjectiveLine.grading k)
    (hf : HomogeneousIdeal.irrelevant (ProjectiveLine.grading k) ≤
      (HomogeneousIdeal.irrelevant (ProjectiveLine.grading k)).map f)
    (hg : HomogeneousIdeal.irrelevant (ProjectiveLine.grading k) ≤
      (HomogeneousIdeal.irrelevant (ProjectiveLine.grading k)).map g)
    (hfg : f = g) : Proj.map f hf = Proj.map g hg := by
  subst g
  rfl

lemma matrixMap_one : matrixMap k 1 = 𝟙 _ := by
  exact (projMap_congr k _ _ _ (by simp) (linearSubstitution_one k)).trans Proj.map_id

lemma matrixMap_comp (M N : Matrix.GeneralLinearGroup (Fin 2) k) :
    matrixMap k M ≫ matrixMap k N = matrixMap k (N * M) := by
  unfold matrixMap
  rw [← Proj.map_comp]
  exact projMap_congr k _ _ _ _ (linearSubstitution_comp k (M : Matrix2 k) (N : Matrix2 k))

/-- Actual scheme inverse derived from inverse homogeneous substitutions. -/
def matrixIso (M : Matrix.GeneralLinearGroup (Fin 2) k) :
    ProjectiveLine.projectiveP1 k ≅ ProjectiveLine.projectiveP1 k where
  hom := matrixMap k M
  inv := matrixMap k M⁻¹
  hom_inv_id := by rw [matrixMap_comp, inv_mul_cancel, matrixMap_one]
  inv_hom_id := by rw [matrixMap_comp, mul_inv_cancel, matrixMap_one]

lemma linearSubstitution_away_constant (M : Matrix2 k)
    (r : MvPolynomial (Fin 2) k) (a : k) :
    HomogeneousLocalization.Away.map (linearSubstitution k M) r
        (HomogeneousLocalization.fromZeroRingHom (ProjectiveLine.grading k)
          (Submonoid.powers r) (ProjectiveLine.constToGradeZero k a)) =
      HomogeneousLocalization.fromZeroRingHom (ProjectiveLine.grading k)
        (Submonoid.powers (linearSubstitution k M r))
        (ProjectiveLine.constToGradeZero k a) := by
  let f := linearSubstitution k M
  let P := Submonoid.powers r
  let Q := Submonoid.powers (f r)
  have hPQ : P ≤ Q.comap f := by
    rintro _ ⟨n, rfl⟩
    exact ⟨n, by simp⟩
  change HomogeneousLocalization.map f hPQ
      (HomogeneousLocalization.mk
        ⟨0, ProjectiveLine.constToGradeZero k a, 1, one_mem P⟩) =
    HomogeneousLocalization.mk
      ⟨0, ProjectiveLine.constToGradeZero k a, 1, one_mem Q⟩
  rw [HomogeneousLocalization.map_mk]
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_mk, HomogeneousLocalization.val_mk]
  change Localization.mk (f (MvPolynomial.C a)) ⟨f 1, _⟩ =
    Localization.mk (MvPolynomial.C a) ⟨1, _⟩
  simp only [f, map_one, linearSubstitution_C]

/-- Scalar compatibility is checked on the transformed homogeneous basic-open
cover. This does not assert that matrixMap preserves the original affine chart. -/
@[reassoc] lemma matrixMap_over (M : Matrix.GeneralLinearGroup (Fin 2) k) :
    matrixMap k M ≫ ProjectiveLine.structureMap k = ProjectiveLine.structureMap k := by
  let f := linearSubstitution k (M : Matrix2 k)
  let hf := linearSubstitution_irrelevant_le k M
  apply (Proj.mapAffineOpenCover f hf).openCover.hom_ext
  intro s
  change (i : ℕ+) × ↥(ProjectiveLine.grading k (i : ℕ)) at s
  rcases s with ⟨⟨n, hn⟩, ⟨r, hr⟩⟩
  change r ∈ ProjectiveLine.grading k n at hr
  change (Proj.awayι (ProjectiveLine.grading k) (f r)
      (f.map_mem hr) hn) ≫ Proj.map f hf ≫ ProjectiveLine.structureMap k =
    (Proj.awayι (ProjectiveLine.grading k) (f r)
      (f.map_mem hr) hn) ≫ ProjectiveLine.structureMap k
  refine (Proj.awayι_comp_map_assoc f hf hn r hr
    (ProjectiveLine.structureMap k)).trans ?_
  simp only [ProjectiveLine.structureMap, Category.assoc,
    Proj.awayι_toSpecZero_assoc, ← Spec.map_comp]
  apply congrArg (fun g : CommRingCat.of k ⟶
    CommRingCat.of (HomogeneousLocalization.Away (ProjectiveLine.grading k) (f r)) =>
      Spec.map g)
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact linearSubstitution_away_constant k (M : Matrix2 k) r a

/-- The actual original-k automorphism, not just an unbased scheme iso. -/
def matrixOverIso (M : Matrix.GeneralLinearGroup (Fin 2) k) :
    Over.mk (ProjectiveLine.structureMap k) ≅ Over.mk (ProjectiveLine.structureMap k) :=
  Over.isoMk (matrixIso k M) (matrixMap_over k M)

end AlgebraicGeometry.Scheme.ProjectiveLine.TwoPoints

namespace AlgebraicGeometry.Scheme.ProjectiveLine.TwoPoints

variable (k : Type u) [Field k]
open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

lemma linear_mem_point (i : Fin 2) (a : k)
    (g : MvPolynomial (Fin 2) k) (hg : g ∈ ProjectiveLine.grading k 1) :
    g ∈ (point k i a (default : Spec (.of k))).asHomogeneousIdeal ↔
      (ProjectiveLine.dehomogenizePolynomial k i g).eval a = 0 := by
  apply not_iff_not.mp
  change point k i a (default : Spec (.of k)) ∈
      Proj.basicOpen (ProjectiveLine.grading k) g ↔ _
  rw [point, Scheme.Hom.comp_apply]
  change Spec.map (CommRingCat.ofHom (evalRingHom a)) (default : Spec (.of k)) ∈
    ProjectiveLine.chart k i ⁻¹ᵁ Proj.basicOpen (ProjectiveLine.grading k) g ↔ _
  rw [ProjectiveLine.chart_preimage_linear k i g hg]
  rfl

lemma section_has_chart_zero (s : Spec (.of k) ⟶ ProjectiveLine.projectiveP1 k)
    (hs : s ≫ ProjectiveLine.structureMap k = 𝟙 _)
    (h0 : MvPolynomial.X (0 : Fin 2) ∉
      (s (default : Spec (.of k))).asHomogeneousIdeal) :
    ∃ a : k, s = point k 0 a := by
  have hrange : Set.range s ⊆ Set.range (ProjectiveLine.chart k 0) := by
    rintro _ ⟨z, rfl⟩
    change s z ∈ (ProjectiveLine.chart k 0).opensRange
    rw [ProjectiveLine.chart_opensRange]
    change MvPolynomial.X (0 : Fin 2) ∉ (s z).asHomogeneousIdeal
    simpa only [Subsingleton.elim z (default : Spec (.of k))] using h0
  let t := IsOpenImmersion.lift (ProjectiveLine.chart k 0) s hrange
  have ht : t ≫ ProjectiveLine.chart k 0 = s := IsOpenImmersion.lift_fac _ _ _
  have hb : t ≫ Spec.map (CommRingCat.ofHom (algebraMap k k[X])) = 𝟙 _ := by
    rw [← ProjectiveLine.chart_over k 0, ← Category.assoc, ht, hs]
  obtain ⟨a, ha⟩ := affineSection_is_evaluation k t hb
  exact ⟨a, ht.symm.trans (by rw [ha]; rfl)⟩

/-- Linear equations recognize the exact original-k section in chart0. -/
lemma section_eq_point_zero_chart (s : Spec (.of k) ⟶ ProjectiveLine.projectiveP1 k)
    (hs : s ≫ ProjectiveLine.structureMap k = 𝟙 _) (b : k)
    (h0 : MvPolynomial.X (0 : Fin 2) ∉
      (s (default : Spec (.of k))).asHomogeneousIdeal)
    (hb : MvPolynomial.X (1 : Fin 2) -
      MvPolynomial.C b * MvPolynomial.X (0 : Fin 2) ∈
        (s (default : Spec (.of k))).asHomogeneousIdeal) :
    s = point k 0 b := by
  obtain ⟨a, rfl⟩ := section_has_chart_zero k s hs h0
  have hh := (linear_mem_point k 0 a _
    ((MvPolynomial.isHomogeneous_X k (1 : Fin 2)).sub
      ((MvPolynomial.isHomogeneous_X k (0 : Fin 2)).C_mul b))).mp hb
  have hab : a = b := sub_eq_zero.mp (by
    simpa [ProjectiveLine.dehomogenizePolynomial] using hh)
  rw [hab]

/-- Evaluation of the actual graded substitution at either canonical chart form. -/
lemma linearForm_mem_canonicalSection (M : Matrix2 k) (i : Fin 2) (p : Option k) :
    linearForm k M i ∈
        (canonicalSection k p (default : Spec (.of k))).asHomogeneousIdeal ↔
      M.mulVec (vector k p) i = 0 := by
  cases p with
  | none =>
      rw [canonicalSection, linear_mem_point k 1 0 _ (linearForm_homogeneous k M i)]
      simp [ProjectiveLine.dehomogenizePolynomial, linearForm, vector,
        Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  | some a =>
      rw [canonicalSection, linear_mem_point k 0 a _ (linearForm_homogeneous k M i)]
      simp [ProjectiveLine.dehomogenizePolynomial, linearForm, vector,
        Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- Pullback of a homogeneous coordinate records the native Proj point action. -/
lemma coordinate_mem_matrixMap (M : Matrix.GeneralLinearGroup (Fin 2) k)
    (i : Fin 2) (x : ProjectiveLine.projectiveP1 k) :
    MvPolynomial.X i ∈ (matrixMap k M x).asHomogeneousIdeal ↔
      linearForm k (M : Matrix2 k) i ∈ x.asHomogeneousIdeal := by
  change linearSubstitution k (M : Matrix2 k) (MvPolynomial.X i) ∈
    x.asHomogeneousIdeal ↔ _
  rw [linearSubstitution_X]

/-- Difference of the two target coordinates at the native Proj image. -/
lemma difference_mem_matrixMap (M : Matrix.GeneralLinearGroup (Fin 2) k)
    (x : ProjectiveLine.projectiveP1 k) :
    MvPolynomial.X (1 : Fin 2) - MvPolynomial.X (0 : Fin 2) ∈
        (matrixMap k M x).asHomogeneousIdeal ↔
      linearForm k (M : Matrix2 k) 1 - linearForm k (M : Matrix2 k) 0 ∈
        x.asHomogeneousIdeal := by
  change linearSubstitution k (M : Matrix2 k)
    (MvPolynomial.X (1 : Fin 2) - MvPolynomial.X (0 : Fin 2)) ∈
      x.asHomogeneousIdeal ↔ _
  rw [map_sub, linearSubstitution_X, linearSubstitution_X]

lemma difference_mem_canonicalSection (M : Matrix2 k) (p : Option k) :
    linearForm k M 1 - linearForm k M 0 ∈
        (canonicalSection k p (default : Spec (.of k))).asHomogeneousIdeal ↔
      M.mulVec (vector k p) 1 - M.mulVec (vector k p) 0 = 0 := by
  cases p with
  | none =>
      rw [canonicalSection, linear_mem_point k 1 0 _
        ((linearForm_homogeneous k M 1).sub (linearForm_homogeneous k M 0))]
      simp [ProjectiveLine.dehomogenizePolynomial, linearForm, vector,
        Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  | some a =>
      rw [canonicalSection, linear_mem_point k 0 a _
        ((linearForm_homogeneous k M 1).sub (linearForm_homogeneous k M 0))]
      simp [ProjectiveLine.dehomogenizePolynomial, linearForm, vector,
        Matrix.mulVec, dotProduct, Fin.sum_univ_two]

@[reassoc] lemma canonicalSection_over (p : Option k) :
    canonicalSection k p ≫ ProjectiveLine.structureMap k = 𝟙 _ := by
  cases p <;> exact point_over k _ _

lemma pairGL_first_triangle (p q : Option k) (hpq : p ≠ q) :
    canonicalSection k p ≫ matrixMap k (pairGL k p q hpq) = point k 0 0 := by
  let M := pairGL k p q hpq
  have hM : (M : Matrix2 k) = pairMatrix k p q := rfl
  refine section_eq_point_zero_chart k _ ?_ 0 ?_ ?_
  · rw [Category.assoc, matrixMap_over, canonicalSection_over]
  · change MvPolynomial.X (0 : Fin 2) ∉
      (matrixMap k M (canonicalSection k p (default : Spec (.of k)))).asHomogeneousIdeal
    rw [coordinate_mem_matrixMap, linearForm_mem_canonicalSection, hM,
      pairMatrix_first]
    exact pairDet_ne_zero k p q hpq
  · simp only [MvPolynomial.C_0, zero_mul, sub_zero]
    change MvPolynomial.X (1 : Fin 2) ∈
      (matrixMap k M (canonicalSection k p (default : Spec (.of k)))).asHomogeneousIdeal
    rw [coordinate_mem_matrixMap, linearForm_mem_canonicalSection, hM,
      pairMatrix_first]
    rfl

lemma pairGL_second_triangle (p q : Option k) (hpq : p ≠ q) :
    canonicalSection k q ≫ matrixMap k (pairGL k p q hpq) = point k 0 1 := by
  let M := pairGL k p q hpq
  have hM : (M : Matrix2 k) = pairMatrix k p q := rfl
  refine section_eq_point_zero_chart k _ ?_ 1 ?_ ?_
  · rw [Category.assoc, matrixMap_over, canonicalSection_over]
  · change MvPolynomial.X (0 : Fin 2) ∉
      (matrixMap k M (canonicalSection k q (default : Spec (.of k)))).asHomogeneousIdeal
    rw [coordinate_mem_matrixMap, linearForm_mem_canonicalSection, hM,
      pairMatrix_second]
    exact pairDet_ne_zero k p q hpq
  · simp only [MvPolynomial.C_1, one_mul]
    change MvPolynomial.X (1 : Fin 2) - MvPolynomial.X (0 : Fin 2) ∈
      (matrixMap k M (canonicalSection k q (default : Spec (.of k)))).asHomogeneousIdeal
    rw [difference_mem_matrixMap, difference_mem_canonicalSection, hM,
      pairMatrix_second]
    simp

/-- The two actual original-k sections, their
actual base triangles, and their inequality. In particular infinity is allowed. -/
def normalizePair (s t : Spec (.of k) ⟶ ProjectiveLine.projectiveP1 k)
    (hs : s ≫ ProjectiveLine.structureMap k = 𝟙 _) (ht : t ≫ ProjectiveLine.structureMap k = 𝟙 _)
      (hne : s ≠ t) :
    Over.mk (ProjectiveLine.structureMap k) ≅ Over.mk (ProjectiveLine.structureMap k) :=
  matrixOverIso k (pairGL k (coordinate k s hs) (coordinate k t ht)
    (coordinates_distinct k s t hs ht hne))

@[reassoc] lemma normalizePair_first (s t : Spec (.of k) ⟶ ProjectiveLine.projectiveP1 k)
    (hs : s ≫ ProjectiveLine.structureMap k = 𝟙 _) (ht : t ≫ ProjectiveLine.structureMap k = 𝟙 _)
      (hne : s ≠ t) :
    s ≫ (normalizePair k s t hs ht hne).hom.left =
      Spec.map (CommRingCat.ofHom (evalRingHom (0 : k))) ≫ ProjectiveLine.chart k 0 := by
  change s ≫ matrixMap k _ = point k 0 0
  calc
    s ≫ matrixMap k _ = canonicalSection k (coordinate k s hs) ≫ matrixMap k _ :=
      congrArg (fun x => x ≫ matrixMap k _) (coordinate_section k s hs)
    _ = point k 0 0 := pairGL_first_triangle k _ _ _

@[reassoc] lemma normalizePair_second (s t : Spec (.of k) ⟶ ProjectiveLine.projectiveP1 k)
    (hs : s ≫ ProjectiveLine.structureMap k = 𝟙 _) (ht : t ≫ ProjectiveLine.structureMap k = 𝟙 _)
      (hne : s ≠ t) :
    t ≫ (normalizePair k s t hs ht hne).hom.left =
      Spec.map (CommRingCat.ofHom (evalRingHom (1 : k))) ≫ ProjectiveLine.chart k 0 := by
  change t ≫ matrixMap k _ = point k 0 1
  calc
    t ≫ matrixMap k _ = canonicalSection k (coordinate k t ht) ≫ matrixMap k _ :=
      congrArg (fun x => x ≫ matrixMap k _) (coordinate_section k t ht)
    _ = point k 0 1 := pairGL_second_triangle k _ _ _

@[reassoc] lemma normalizePair_over (s t : Spec (.of k) ⟶ ProjectiveLine.projectiveP1 k)
    (hs : s ≫ ProjectiveLine.structureMap k = 𝟙 _) (ht : t ≫ ProjectiveLine.structureMap k = 𝟙 _)
      (hne : s ≠ t) :
    (normalizePair k s t hs ht hne).hom.left ≫ ProjectiveLine.structureMap k =
      ProjectiveLine.structureMap k :=
  (normalizePair k s t hs ht hne).hom.w

end AlgebraicGeometry.Scheme.ProjectiveLine.TwoPoints

/- Migration source: LocalModels/IntrinsicSplitNode/PairCoordinates.lean.
Frozen R5 packet f8a3314ddecffcada2ec721d26d56a937bed9690.
SHA-256 c27a78308a36971a8baff6e7cda714dff9164f41df04dbe1c985a46e152d834e.
The source nodal point wrappers are expanded to the same literal evaluation maps. -/
