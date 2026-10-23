/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.ProjectiveLine.Charts
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Reindex
public import Aglib.AlgebraicGeometry.ProjectiveSpace.BaseChange.Cartesian
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor

/-!
# Linear changes on the original projective line over a ring

Invertible matrices act by their original homogeneous coordinate substitutions
on the same native polynomial Proj. Composition and coefficient changes keep
those maps and the actual structure triangles. All assertions hold over
commutative rings, including nonreduced rings; no field assumption is used.

The field-specific two-point normalization uses this implementation through its
original compatibility names. Coefficient naturality and the cartesian
coefficient square also support gluing projective lines over affine open sets.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial Matrix
open scoped Polynomial
universe u

namespace AlgebraicGeometry.Scheme.ProjectiveLine.LinearChange

variable (k : Type u) [CommRing k]
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

end AlgebraicGeometry.Scheme.ProjectiveLine.LinearChange

namespace AlgebraicGeometry.Scheme.ProjectiveLine.LinearChange

open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]

/-- The original coefficient map on the same literal two-coordinate Proj. -/
def coefficientMap (f : R →+* S) :
    ProjectiveLine.projectiveP1 S ⟶ ProjectiveLine.projectiveP1 R :=
  Proj.map (MvPolynomial.gradedMap (ι := Fin 2) f)
    (by rw [MvPolynomial.irrelevant_map_gradedMap])

@[simp] theorem coefficientMap_id : coefficientMap (RingHom.id R) = 𝟙 _ := by
  simp only [coefficientMap, MvPolynomial.gradedMap_id, Proj.map_id]

/-- The original coefficient morphism reverses ring-map composition. -/
theorem coefficientMap_comp (f : R →+* S) (g : S →+* T) :
    coefficientMap (g.comp f) = coefficientMap g ≫ coefficientMap f := by
  simp only [coefficientMap, MvPolynomial.gradedMap_comp]
  exact Proj.map_comp _ _ _ _

/-- The original matrix substitution commutes with the original coefficient homomorphism. -/
theorem linearSubstitution_map (f : R →+* S) (M : Matrix2 R) :
    (MvPolynomial.gradedMap f).comp (linearSubstitution R M) =
      (linearSubstitution S (M.map f)).comp (MvPolynomial.gradedMap f) := by
  apply GradedRingHom.ext
  intro p
  have h : ((MvPolynomial.gradedMap f).comp (linearSubstitution R M)).toRingHom =
      ((linearSubstitution S (M.map f)).comp (MvPolynomial.gradedMap f)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      change MvPolynomial.map f (linearSubstitution R M (MvPolynomial.C a)) =
        linearSubstitution S (M.map f) (MvPolynomial.map f (MvPolynomial.C a))
      simp only [linearSubstitution_C, MvPolynomial.map_C]
    · intro i
      change MvPolynomial.map f (linearSubstitution R M (MvPolynomial.X i)) =
        linearSubstitution S (M.map f) (MvPolynomial.map f (MvPolynomial.X i))
      simp only [linearSubstitution_X, MvPolynomial.map_X]
      simp [linearForm]
  exact DFunLike.congr_fun h p

/-- Coefficient naturality of the original forward projective matrix maps. -/
theorem coefficientMap_matrixMap (f : R →+* S)
    (M : Matrix.GeneralLinearGroup (Fin 2) R) :
    coefficientMap f ≫ matrixMap R M =
      matrixMap S (Matrix.GeneralLinearGroup.map f M) ≫ coefficientMap f := by
  have h := linearSubstitution_map f (M : Matrix2 R)
  change (MvPolynomial.gradedMap f).comp (linearSubstitution R (M : Matrix2 R)) =
    (linearSubstitution S (Matrix.GeneralLinearGroup.map f M : Matrix2 S)).comp
      (MvPolynomial.gradedMap f) at h
  unfold coefficientMap matrixMap
  rw [← Proj.map_comp, ← Proj.map_comp]
  congr 1

/-- Coordinate-universe transport commutes with the same original coefficient map. -/
theorem coefficientMap_finUlift (f : R →+* S) :
    coefficientMap f ≫ (AlgebraicGeometry.ProjectiveSpace.finUliftIso R 2).hom =
      (AlgebraicGeometry.ProjectiveSpace.finUliftIso S 2).hom ≫
        AlgebraicGeometry.ProjectiveSpace.map f (ULift.{u} (Fin 2)) := by
  have h : (MvPolynomial.gradedMap (ι := Fin 2) f).comp
      (MvPolynomial.gradedRename R (Equiv.ulift : ULift.{u} (Fin 2) ≃ Fin 2)) =
      (MvPolynomial.gradedRename S (Equiv.ulift : ULift.{u} (Fin 2) ≃ Fin 2)).comp
        (MvPolynomial.gradedMap f) := by
    apply GradedRingHom.ext
    intro p
    have he : ((MvPolynomial.gradedMap (ι := Fin 2) f).comp
        (MvPolynomial.gradedRename R (Equiv.ulift : ULift.{u} (Fin 2) ≃ Fin 2))).toRingHom =
        ((MvPolynomial.gradedRename S (Equiv.ulift : ULift.{u} (Fin 2) ≃ Fin 2)).comp
          (MvPolynomial.gradedMap f)).toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro a
        change MvPolynomial.map f (MvPolynomial.rename Equiv.ulift (MvPolynomial.C a)) =
          MvPolynomial.rename Equiv.ulift (MvPolynomial.map f (MvPolynomial.C a))
        simp
      · intro i
        change MvPolynomial.map f (MvPolynomial.rename Equiv.ulift (MvPolynomial.X i)) =
          MvPolynomial.rename Equiv.ulift (MvPolynomial.map f (MvPolynomial.X i))
        simp
    exact DFunLike.congr_fun he p
  dsimp only [coefficientMap, AlgebraicGeometry.ProjectiveSpace.finUliftIso,
    AlgebraicGeometry.ProjectiveSpace.reindexIso, AlgebraicGeometry.ProjectiveSpace.map]
  rw [← Proj.map_comp, ← Proj.map_comp]
  simp only [Equiv.symm_symm]
  congr 1

/-- The same two-coordinate coefficient morphism is the original cartesian base change. -/
theorem coefficientMap_isPullback (f : R →+* S) :
    IsPullback (coefficientMap f) (ProjectiveLine.structureMap S)
      (ProjectiveLine.structureMap R) (Spec.map (CommRingCat.ofHom f)) := by
  let eR := AlgebraicGeometry.ProjectiveSpace.finUliftIso R 2
  let eS := AlgebraicGeometry.ProjectiveSpace.finUliftIso S 2
  have hR : eR.hom ≫ AlgebraicGeometry.ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)) =
      ProjectiveLine.structureMap R :=
    AlgebraicGeometry.ProjectiveSpace.finUliftIso_hom_toSpec R 2
  have hS : eS.hom ≫ AlgebraicGeometry.ProjectiveSpace.toSpec S (ULift.{u} (Fin 2)) =
      ProjectiveLine.structureMap S :=
    AlgebraicGeometry.ProjectiveSpace.finUliftIso_hom_toSpec S 2
  refine (AlgebraicGeometry.ProjectiveSpace.isPullback_map f (ULift.{u} (Fin 2))).of_iso
    eS.symm eR.symm (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · have h := congrArg (fun q => eS.inv ≫ q ≫ eR.inv) (coefficientMap_finUlift f)
    simpa only [eR, eS, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc,
      Iso.inv_hom_id_assoc, Iso.hom_inv_id, Category.comp_id] using h.symm
  · change _ ≫ 𝟙 _ = eS.inv ≫ ProjectiveLine.structureMap S
    rw [← hS]
    simp
  · change _ ≫ 𝟙 _ = eR.inv ≫ ProjectiveLine.structureMap R
    rw [← hR]
    simp
  · simp

@[reassoc] theorem coefficientMap_over (f : R →+* S) :
    coefficientMap f ≫ ProjectiveLine.structureMap R =
      ProjectiveLine.structureMap S ≫ Spec.map (CommRingCat.ofHom f) :=
  (coefficientMap_isPullback f).w

end AlgebraicGeometry.Scheme.ProjectiveLine.LinearChange
