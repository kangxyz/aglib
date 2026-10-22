/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.ProjectiveTranslation
public import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.VariableChangeChart

/-!
# Native admissible variable changes on the projective Weierstrass cubic

The actual native unit-scale coordinates give a degree-preserving map on the
original cubic quotient over every commutative base ring. The inverse is the
actual inverse native change. Both Proj maps fix base-ring constants and
preserve the actual infinity section by a common-chart evaluation argument.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open WeierstrassCurve.Projective

namespace WeierstrassCurve.VariableChange

universe u
variable {R : Type u} [CommRing R]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The native pure scaling substitution `(x, y) ↦ (u² x, u³ y)`. -/
def scalingChange (u : Rˣ) : WeierstrassCurve.VariableChange R :=
  ⟨u, 0, 0, 0⟩

/-- The powers of the scaling unit on the original projective coordinates `X, Y, Z`. -/
def coordinateWeight : Fin 3 → ℕ := ![2, 3, 0]

/-- The literal diagonal homogeneous pullback `(X, Y, Z) ↦ (u² X, u³ Y, Z)`. -/
def scalingCoordinates (u : Rˣ) : Fin 3 → MvPolynomial (Fin 3) R :=
  fun i => MvPolynomial.C ((u : R) ^ coordinateWeight i) * MvPolynomial.X i

/-- Substitution by the diagonal coordinates in the ordinary homogeneous polynomial ring. -/
def scalingPolynomial (u : Rˣ) :
    MvPolynomial (Fin 3) R →+* MvPolynomial (Fin 3) R :=
  MvPolynomial.eval₂Hom MvPolynomial.C (scalingCoordinates u)

@[simp] lemma scalingPolynomial_C (u : Rˣ) (a : R) :
    scalingPolynomial u (MvPolynomial.C a) = MvPolynomial.C a := by
  simp [scalingPolynomial]

@[simp] lemma scalingPolynomial_X (u : Rˣ) (i : Fin 3) :
    scalingPolynomial u (MvPolynomial.X i) = scalingCoordinates u i := by
  simp [scalingPolynomial]

lemma scalingCoordinates_homogeneous (u : Rˣ) (i : Fin 3) :
    (scalingCoordinates u i).IsHomogeneous 1 :=
  (MvPolynomial.isHomogeneous_X R i).C_mul _

lemma scalingPolynomial_homogeneous (u : Rˣ) {n : ℕ}
    {p : MvPolynomial (Fin 3) R} (hp : p.IsHomogeneous n) :
    (scalingPolynomial u p).IsHomogeneous n := by
  change (MvPolynomial.eval₂ MvPolynomial.C (scalingCoordinates u) p).IsHomogeneous n
  simpa only [one_mul] using hp.eval₂ MvPolynomial.C (scalingCoordinates u)
    (fun a => MvPolynomial.isHomogeneous_C _ a) (scalingCoordinates_homogeneous u)

/-- The actual homogeneous cubic transforms by the unit factor `u⁶`. -/
lemma scalingPolynomial_cubic (W : WeierstrassCurve R) (u : Rˣ) :
    scalingPolynomial u W.toProjective.polynomial =
      MvPolynomial.C ((u : R) ^ 6) * (scalingChange u • W).toProjective.polynomial := by
  let U : MvPolynomial (Fin 3) R := MvPolynomial.C (u : R)
  let Uinv : MvPolynomial (Fin 3) R := MvPolynomial.C (↑u⁻¹ : R)
  have h (m : ℕ) : U ^ m * Uinv ^ m = 1 := by
    dsimp only [U, Uinv]
    rw [← mul_pow, ← map_mul, u.mul_inv, map_one, one_pow]
  have h1 : U ^ 6 * Uinv = U ^ 5 := by
    linear_combination U ^ 5 * h 1
  have h2 : U ^ 6 * Uinv ^ 2 = U ^ 4 := by
    linear_combination U ^ 4 * h 2
  have h3 : U ^ 6 * Uinv ^ 3 = U ^ 3 := by
    linear_combination U ^ 3 * h 3
  have h4 : U ^ 6 * Uinv ^ 4 = U ^ 2 := by
    linear_combination U ^ 2 * h 4
  have h6 := h 6
  simp [WeierstrassCurve.Projective.polynomial, scalingChange,
    WeierstrassCurve.variableChange_def, scalingCoordinates, coordinateWeight,
    map_add, map_sub, map_mul, map_pow]
  dsimp only [U, Uinv] at h1 h2 h3 h4 h6
  linear_combination
    -MvPolynomial.C W.a₁ * MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2 * h1 +
      MvPolynomial.C W.a₂ * MvPolynomial.X 0 ^ 2 * MvPolynomial.X 2 * h2 -
      MvPolynomial.C W.a₃ * MvPolynomial.X 1 * MvPolynomial.X 2 ^ 2 * h3 +
      MvPolynomial.C W.a₄ * MvPolynomial.X 0 * MvPolynomial.X 2 ^ 2 * h4 +
      MvPolynomial.C W.a₆ * MvPolynomial.X 2 ^ 3 * h6

/-- The native shear `(x, y) ↦ (x, y + s x)`. -/
def shearChange (s : R) : WeierstrassCurve.VariableChange R :=
  ⟨1, 0, s, 0⟩

/-- The literal homogeneous shear, fixing the original `X` and `Z` coordinates. -/
def shearCoordinates (s : R) : Fin 3 → MvPolynomial (Fin 3) R :=
  ![MvPolynomial.X 0, MvPolynomial.X 1 + MvPolynomial.C s * MvPolynomial.X 0,
    MvPolynomial.X 2]

/-- Substitution by the homogeneous shear coordinates. -/
def shearPolynomial (s : R) :
    MvPolynomial (Fin 3) R →+* MvPolynomial (Fin 3) R :=
  MvPolynomial.eval₂Hom MvPolynomial.C (shearCoordinates s)

@[simp] lemma shearPolynomial_C (s a : R) :
    shearPolynomial s (MvPolynomial.C a) = MvPolynomial.C a := by
  simp [shearPolynomial]

@[simp] lemma shearPolynomial_X (s : R) (i : Fin 3) :
    shearPolynomial s (MvPolynomial.X i) = shearCoordinates s i := by
  simp [shearPolynomial]

lemma shearCoordinates_homogeneous (s : R) (i : Fin 3) :
    (shearCoordinates s i).IsHomogeneous 1 := by
  fin_cases i
  · exact MvPolynomial.isHomogeneous_X R 0
  · exact (MvPolynomial.isHomogeneous_X R 1).add
      ((MvPolynomial.isHomogeneous_X R 0).C_mul s)
  · exact MvPolynomial.isHomogeneous_X R 2

lemma shearPolynomial_homogeneous (s : R) {n : ℕ}
    {p : MvPolynomial (Fin 3) R} (hp : p.IsHomogeneous n) :
    (shearPolynomial s p).IsHomogeneous n := by
  change (MvPolynomial.eval₂ MvPolynomial.C (shearCoordinates s) p).IsHomogeneous n
  simpa only [one_mul] using hp.eval₂ MvPolynomial.C (shearCoordinates s)
    (fun a => MvPolynomial.isHomogeneous_C _ a) (shearCoordinates_homogeneous s)

lemma shearPolynomial_cubic (W : WeierstrassCurve R) (s : R) :
    shearPolynomial s W.toProjective.polynomial =
      (shearChange s • W).toProjective.polynomial := by
  simp [WeierstrassCurve.Projective.polynomial, shearPolynomial, shearCoordinates,
    shearChange, WeierstrassCurve.variableChange_def, map_ofNat]
  ring

/-- The native change is exactly scaling followed by shear and translation in its group law. -/
lemma scaling_shear_translation (C : WeierstrassCurve.VariableChange R) :
    scalingChange C.u * shearChange C.s *
      WeierstrassCurve.VariableChange.mk 1 C.r 0 C.t = C := by
  ext <;> simp [scalingChange, shearChange, WeierstrassCurve.VariableChange.mul_def]

lemma action_scaling_shear_translation (W : WeierstrassCurve R)
    (C : WeierstrassCurve.VariableChange R) :
    C • W = scalingChange C.u •
      (shearChange C.s • WeierstrassCurve.translate W C.r C.t) := by
  calc
    C • W = (scalingChange C.u * shearChange C.s *
        WeierstrassCurve.VariableChange.mk 1 C.r 0 C.t) • W :=
      congrArg (fun D : WeierstrassCurve.VariableChange R => D • W)
        (scaling_shear_translation C).symm
    _ = _ := by rw [mul_smul, mul_smul]; rfl

/-- The full native homogeneous coordinate substitution over the original base ring. -/
def projectiveCoordinates (C : WeierstrassCurve.VariableChange R) :
    Fin 3 → MvPolynomial (Fin 3) R :=
  ![MvPolynomial.C ((C.u : R) ^ 2) * MvPolynomial.X 0 +
      MvPolynomial.C C.r * MvPolynomial.X 2,
    MvPolynomial.C ((C.u : R) ^ 3) * MvPolynomial.X 1 +
      MvPolynomial.C (C.s * (C.u : R) ^ 2) * MvPolynomial.X 0 +
        MvPolynomial.C C.t * MvPolynomial.X 2,
    MvPolynomial.X 2]

/-- The literal full forward polynomial pullback with its native unit scale. -/
def projectivePolynomial (C : WeierstrassCurve.VariableChange R) :
    MvPolynomial (Fin 3) R →+* MvPolynomial (Fin 3) R :=
  MvPolynomial.eval₂Hom MvPolynomial.C (projectiveCoordinates C)

@[simp] lemma projectivePolynomial_C (C : WeierstrassCurve.VariableChange R) (a : R) :
    projectivePolynomial C (MvPolynomial.C a) = MvPolynomial.C a := by
  simp [projectivePolynomial]

@[simp] lemma projectivePolynomial_X0 (C : WeierstrassCurve.VariableChange R) :
    projectivePolynomial C (MvPolynomial.X 0) =
      MvPolynomial.C ((C.u : R) ^ 2) * MvPolynomial.X 0 +
        MvPolynomial.C C.r * MvPolynomial.X 2 := by
  simp [projectivePolynomial, projectiveCoordinates]

@[simp] lemma projectivePolynomial_X1 (C : WeierstrassCurve.VariableChange R) :
    projectivePolynomial C (MvPolynomial.X 1) =
      MvPolynomial.C ((C.u : R) ^ 3) * MvPolynomial.X 1 +
        MvPolynomial.C C.s * MvPolynomial.C ((C.u : R) ^ 2) * MvPolynomial.X 0 +
          MvPolynomial.C C.t * MvPolynomial.X 2 := by
  simp [projectivePolynomial, projectiveCoordinates, map_mul]

@[simp] lemma projectivePolynomial_X2 (C : WeierstrassCurve.VariableChange R) :
    projectivePolynomial C (MvPolynomial.X 2) = MvPolynomial.X 2 := by
  simp [projectivePolynomial, projectiveCoordinates]

private lemma projectiveCoordinates_homogeneous (C : WeierstrassCurve.VariableChange R)
    (i : Fin 3) : (projectiveCoordinates C i).IsHomogeneous 1 := by
  fin_cases i
  · exact ((MvPolynomial.isHomogeneous_X R 0).C_mul ((C.u : R) ^ 2)).add
      ((MvPolynomial.isHomogeneous_X R 2).C_mul C.r)
  · exact (((MvPolynomial.isHomogeneous_X R 1).C_mul ((C.u : R) ^ 3)).add
      ((MvPolynomial.isHomogeneous_X R 0).C_mul (C.s * (C.u : R) ^ 2))).add
        ((MvPolynomial.isHomogeneous_X R 2).C_mul C.t)
  · exact MvPolynomial.isHomogeneous_X R 2

lemma projectivePolynomial_homogeneous (C : WeierstrassCurve.VariableChange R) {n : ℕ}
    {p : MvPolynomial (Fin 3) R} (hp : p.IsHomogeneous n) :
    (projectivePolynomial C p).IsHomogeneous n := by
  change (MvPolynomial.eval₂ MvPolynomial.C (projectiveCoordinates C) p).IsHomogeneous n
  simpa only [one_mul] using hp.eval₂ MvPolynomial.C (projectiveCoordinates C)
    (fun a => MvPolynomial.isHomogeneous_C _ a) (projectiveCoordinates_homogeneous C)

lemma projectivePolynomial_mul (C D : WeierstrassCurve.VariableChange R) :
    (projectivePolynomial C).comp (projectivePolynomial D) = projectivePolynomial (C * D) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp
  · intro i
    fin_cases i <;>
      simp [WeierstrassCurve.VariableChange.mul_def, map_add, map_mul, map_pow] <;> ring

lemma projectivePolynomial_one :
    projectivePolynomial (1 : WeierstrassCurve.VariableChange R) = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp
  · intro i
    fin_cases i <;> simp [WeierstrassCurve.VariableChange.one_def]

lemma projectivePolynomial_inverse (C : WeierstrassCurve.VariableChange R)
    (p : MvPolynomial (Fin 3) R) :
    projectivePolynomial C⁻¹ (projectivePolynomial C p) = p := by
  have h := DFunLike.congr_fun (projectivePolynomial_mul C⁻¹ C) p
  simpa only [inv_mul_cancel, projectivePolynomial_one, RingHom.comp_apply,
    RingHom.id_apply] using h

lemma projectivePolynomial_inverse' (C : WeierstrassCurve.VariableChange R)
    (p : MvPolynomial (Fin 3) R) :
    projectivePolynomial C (projectivePolynomial C⁻¹ p) = p := by
  simpa only [inv_inv] using projectivePolynomial_inverse C⁻¹ p

/-- The full homogeneous substitution has exactly the native `u⁶` cubic factor. -/
lemma projectivePolynomial_cubic (W : WeierstrassCurve R)
    (C : WeierstrassCurve.VariableChange R) :
    projectivePolynomial C W.toProjective.polynomial =
      MvPolynomial.C ((C.u : R) ^ 6) * (C • W).toProjective.polynomial := by
  let U : MvPolynomial (Fin 3) R := MvPolynomial.C (C.u : R)
  let Uinv : MvPolynomial (Fin 3) R := MvPolynomial.C (↑C.u⁻¹ : R)
  have h (m : ℕ) : U ^ m * Uinv ^ m = 1 := by
    dsimp only [U, Uinv]
    rw [← mul_pow, ← map_mul, C.u.mul_inv, map_one, one_pow]
  have h1 : U ^ 6 * Uinv = U ^ 5 := by
    linear_combination U ^ 5 * h 1
  have h2 : U ^ 6 * Uinv ^ 2 = U ^ 4 := by
    linear_combination U ^ 4 * h 2
  have h3 : U ^ 6 * Uinv ^ 3 = U ^ 3 := by
    linear_combination U ^ 3 * h 3
  have h4 : U ^ 6 * Uinv ^ 4 = U ^ 2 := by
    linear_combination U ^ 2 * h 4
  have h6 := h 6
  simp [projectivePolynomial, projectiveCoordinates,
    WeierstrassCurve.Projective.polynomial, WeierstrassCurve.variableChange_def,
    map_add, map_sub, map_mul, map_pow, map_ofNat]
  dsimp only [U, Uinv] at h1 h2 h3 h4 h6
  linear_combination
    -(MvPolynomial.C W.a₁ + 2 * MvPolynomial.C C.s) *
      MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2 * h1 +
      (MvPolynomial.C W.a₂ - MvPolynomial.C C.s * MvPolynomial.C W.a₁ +
        3 * MvPolynomial.C C.r - MvPolynomial.C C.s ^ 2) *
        MvPolynomial.X 0 ^ 2 * MvPolynomial.X 2 * h2 -
      (MvPolynomial.C W.a₃ + MvPolynomial.C C.r * MvPolynomial.C W.a₁ +
        2 * MvPolynomial.C C.t) * MvPolynomial.X 1 * MvPolynomial.X 2 ^ 2 * h3 +
      (MvPolynomial.C W.a₄ - MvPolynomial.C C.s * MvPolynomial.C W.a₃ +
        2 * MvPolynomial.C C.r * MvPolynomial.C W.a₂ -
        (MvPolynomial.C C.t + MvPolynomial.C C.r * MvPolynomial.C C.s) *
          MvPolynomial.C W.a₁ + 3 * MvPolynomial.C C.r ^ 2 -
        2 * MvPolynomial.C C.s * MvPolynomial.C C.t) *
        MvPolynomial.X 0 * MvPolynomial.X 2 ^ 2 * h4 +
      (MvPolynomial.C W.a₆ + MvPolynomial.C C.r * MvPolynomial.C W.a₄ +
        MvPolynomial.C C.r ^ 2 * MvPolynomial.C W.a₂ + MvPolynomial.C C.r ^ 3 -
        MvPolynomial.C C.t * MvPolynomial.C W.a₃ - MvPolynomial.C C.t ^ 2 -
        MvPolynomial.C C.r * MvPolynomial.C C.t * MvPolynomial.C W.a₁) *
        MvPolynomial.X 2 ^ 3 * h6

lemma inverseProjectivePolynomial_cubic (W : WeierstrassCurve R)
    (C : WeierstrassCurve.VariableChange R) :
    projectivePolynomial C⁻¹ (C • W).toProjective.polynomial =
      MvPolynomial.C ((↑((C⁻¹).u) : R) ^ 6) * W.toProjective.polynomial := by
  rw [projectivePolynomial_cubic, inv_smul_smul]

/-- The actual full admissible pullback on the original homogeneous cubic quotient. -/
def projectiveHomogeneous (W : WeierstrassCurve R) (C : WeierstrassCurve.VariableChange R) :
    homogeneousCoordinateRing W →ₐ[R] homogeneousCoordinateRing (C • W) where
  toRingHom := Ideal.quotientMap _ (projectivePolynomial C) (by
    apply Ideal.span_le.mpr
    intro p hp
    rcases Set.mem_singleton_iff.mp hp with rfl
    change projectivePolynomial C W.toProjective.polynomial ∈ cubicIdeal (C • W)
    rw [projectivePolynomial_cubic]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_singleton _)))
  commutes' a := by
    change Ideal.Quotient.mk _ (projectivePolynomial C (MvPolynomial.C a)) = _
    rw [projectivePolynomial_C]
    rfl

/-- The actual inverse pullback uses the inverse native variable change. -/
def inverseProjectiveHomogeneous (W : WeierstrassCurve R)
    (C : WeierstrassCurve.VariableChange R) :
    homogeneousCoordinateRing (C • W) →ₐ[R] homogeneousCoordinateRing W where
  toRingHom := Ideal.quotientMap _ (projectivePolynomial C⁻¹) (by
    apply Ideal.span_le.mpr
    intro p hp
    rcases Set.mem_singleton_iff.mp hp with rfl
    change projectivePolynomial C⁻¹ (C • W).toProjective.polynomial ∈ cubicIdeal W
    rw [inverseProjectivePolynomial_cubic]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_singleton _)))
  commutes' a := by
    change Ideal.Quotient.mk _ (projectivePolynomial C⁻¹ (MvPolynomial.C a)) = _
    rw [projectivePolynomial_C]
    rfl

/-- The original `X` coordinate has exactly the native admissible substitution. -/
@[simp] lemma projectiveHomogeneous_x (W : WeierstrassCurve R)
    (C : WeierstrassCurve.VariableChange R) :
    projectiveHomogeneous W C (coordinate W 0) =
      algebraMap R (homogeneousCoordinateRing (C • W)) ((C.u : R) ^ 2) * coordinate (C • W) 0 +
        algebraMap R (homogeneousCoordinateRing (C • W)) C.r * coordinate (C • W) 2 := by
  change Ideal.Quotient.mk _ (projectivePolynomial C (MvPolynomial.X 0)) = _
  rw [projectivePolynomial_X0]
  rfl

/-- The original `Y` coordinate includes the original scale, shear, and translation. -/
@[simp] lemma projectiveHomogeneous_y (W : WeierstrassCurve R)
    (C : WeierstrassCurve.VariableChange R) :
    projectiveHomogeneous W C (coordinate W 1) =
      algebraMap R (homogeneousCoordinateRing (C • W)) ((C.u : R) ^ 3) * coordinate (C • W) 1 +
        algebraMap R (homogeneousCoordinateRing (C • W)) C.s *
          algebraMap R (homogeneousCoordinateRing (C • W)) ((C.u : R) ^ 2) *
            coordinate (C • W) 0 +
        algebraMap R (homogeneousCoordinateRing (C • W)) C.t * coordinate (C • W) 2 := by
  change Ideal.Quotient.mk _ (projectivePolynomial C (MvPolynomial.X 1)) = _
  rw [projectivePolynomial_X1]
  rfl

@[simp] lemma projectiveHomogeneous_z (W : WeierstrassCurve R)
    (C : WeierstrassCurve.VariableChange R) :
    projectiveHomogeneous W C (coordinate W 2) = coordinate (C • W) 2 := by
  change Ideal.Quotient.mk _ (projectivePolynomial C (MvPolynomial.X 2)) = _
  rw [projectivePolynomial_X2]
  rfl

/-- The full pullback preserves the original ordinary total-degree grading. -/
def projectiveGraded (W : WeierstrassCurve R) (C : WeierstrassCurve.VariableChange R) :
    grading W →+*ᵍ grading (C • W) where
  __ := (projectiveHomogeneous W C).toRingHom
  map_mem := by
    intro n a ha
    obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp ha
    exact Submodule.mem_map.mpr ⟨projectivePolynomial C p,
      projectivePolynomial_homogeneous C hp, rfl⟩

/-- The inverse full pullback preserves the same grading. -/
def inverseProjectiveGraded (W : WeierstrassCurve R)
    (C : WeierstrassCurve.VariableChange R) :
    grading (C • W) →+*ᵍ grading W where
  __ := (inverseProjectiveHomogeneous W C).toRingHom
  map_mem := by
    intro n a ha
    obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp ha
    exact Submodule.mem_map.mpr ⟨projectivePolynomial C⁻¹ p,
      projectivePolynomial_homogeneous C⁻¹ hp, rfl⟩

lemma inverseProjective_comp_projective (W : WeierstrassCurve R)
    (C : WeierstrassCurve.VariableChange R) :
    (inverseProjectiveGraded W C).comp (projectiveGraded W C) =
      GradedRingHom.id (grading W) := by
  apply GradedRingHom.ext
  intro a
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  change Ideal.Quotient.mk _ (projectivePolynomial C⁻¹ (projectivePolynomial C p)) = _
  rw [projectivePolynomial_inverse]
  rfl

lemma projective_comp_inverseProjective (W : WeierstrassCurve R)
    (C : WeierstrassCurve.VariableChange R) :
    (projectiveGraded W C).comp (inverseProjectiveGraded W C) =
      GradedRingHom.id (grading (C • W)) := by
  apply GradedRingHom.ext
  intro a
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  change Ideal.Quotient.mk _ (projectivePolynomial C (projectivePolynomial C⁻¹ p)) = _
  rw [projectivePolynomial_inverse']
  rfl

private lemma graded_irrelevant_mem {V W : WeierstrassCurve R}
    (f : grading V →+*ᵍ grading W) (a : homogeneousCoordinateRing V)
    (ha : a ∈ HomogeneousIdeal.irrelevant (grading V)) :
    f a ∈ HomogeneousIdeal.irrelevant (grading W) := by
  rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply] at ha ⊢
  rw [← GradedRingHom.map_directSumDecompose, ha, map_zero]

private lemma irrelevant_le_of_inverse {V W : WeierstrassCurve R}
    (f : grading V →+*ᵍ grading W) (g : grading W →+*ᵍ grading V)
    (h : f.comp g = GradedRingHom.id (grading W)) :
    HomogeneousIdeal.irrelevant (grading W) ≤
      (HomogeneousIdeal.irrelevant (grading V)).map f := by
  intro a ha
  have hm := Ideal.mem_map_of_mem f (graded_irrelevant_mem g a ha)
  have he := DFunLike.congr_fun h a
  change f (g a) = a at he
  rwa [he] at hm

private lemma nativeProjMap_congr {V W : WeierstrassCurve R}
    (f g : grading V →+*ᵍ grading W)
    (hf : HomogeneousIdeal.irrelevant (grading W) ≤
      (HomogeneousIdeal.irrelevant (grading V)).map f)
    (hg : HomogeneousIdeal.irrelevant (grading W) ≤
      (HomogeneousIdeal.irrelevant (grading V)).map g)
    (h : f = g) : Proj.map f hf = Proj.map g hg := by
  subst g
  rfl

private lemma native_away_constant {V W : WeierstrassCurve R}
    (f : grading V →+*ᵍ grading W)
    (hc : ∀ a : R, f (algebraMap R _ a) = algebraMap R _ a)
    (r : homogeneousCoordinateRing V) (a : R) :
    HomogeneousLocalization.Away.map f r
      (HomogeneousLocalization.fromZeroRingHom (grading V)
        (Submonoid.powers r) (constToGradeZero V a)) =
    HomogeneousLocalization.fromZeroRingHom (grading W)
      (Submonoid.powers (f r)) (constToGradeZero W a) := by
  let P := Submonoid.powers r
  let Q := Submonoid.powers (f r)
  have hPQ : P ≤ Q.comap f := by
    rintro _ ⟨n, rfl⟩
    exact ⟨n, by simp⟩
  change HomogeneousLocalization.map f hPQ
      (HomogeneousLocalization.mk ⟨0, constToGradeZero V a, 1, one_mem P⟩) =
    HomogeneousLocalization.mk ⟨0, constToGradeZero W a, 1, one_mem Q⟩
  rw [HomogeneousLocalization.map_mk]
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_mk, HomogeneousLocalization.val_mk]
  change Localization.mk (f (algebraMap R _ a)) ⟨f 1, _⟩ =
    Localization.mk (algebraMap R _ a) ⟨1, _⟩
  simp only [map_one, hc]

private lemma nativeProjMap_over {V W : WeierstrassCurve R}
    (f : grading V →+*ᵍ grading W)
    (hf : HomogeneousIdeal.irrelevant (grading W) ≤
      (HomogeneousIdeal.irrelevant (grading V)).map f)
    (hc : ∀ a : R, f (algebraMap R _ a) = algebraMap R _ a) :
    Proj.map f hf ≫ structureMap V = structureMap W := by
  apply (Proj.mapAffineOpenCover f hf).openCover.hom_ext
  intro s
  change (i : ℕ+) × ↥(grading V (i : ℕ)) at s
  rcases s with ⟨⟨n, hn⟩, ⟨r, hr⟩⟩
  change r ∈ grading V n at hr
  change Proj.awayι (grading W) (f r) (f.map_mem hr) hn ≫
      Proj.map f hf ≫ structureMap V =
    Proj.awayι (grading W) (f r) (f.map_mem hr) hn ≫ structureMap W
  refine (Proj.awayι_comp_map_assoc f hf hn r hr (structureMap V)).trans ?_
  simp only [structureMap, Category.assoc, Proj.awayι_toSpecZero_assoc, ← Spec.map_comp]
  apply congrArg (fun g : CommRingCat.of R ⟶
    CommRingCat.of (HomogeneousLocalization.Away (grading W) (f r)) => Spec.map g)
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact native_away_constant f hc r a

lemma projective_irrelevant (W : WeierstrassCurve R) (C : WeierstrassCurve.VariableChange R) :
    HomogeneousIdeal.irrelevant (grading (C • W)) ≤
      (HomogeneousIdeal.irrelevant (grading W)).map (projectiveGraded W C) :=
  irrelevant_le_of_inverse _ _
    (projective_comp_inverseProjective W C)

lemma inverseProjective_irrelevant (W : WeierstrassCurve R)
    (C : WeierstrassCurve.VariableChange R) :
    HomogeneousIdeal.irrelevant (grading W) ≤
      (HomogeneousIdeal.irrelevant (grading (C • W))).map (inverseProjectiveGraded W C) :=
  irrelevant_le_of_inverse _ _
    (inverseProjective_comp_projective W C)

/-- The actual native Proj isomorphism from `C • W` to the same original `W`. -/
def projectiveIso (W : WeierstrassCurve R) (C : WeierstrassCurve.VariableChange R) :
    scheme (C • W) ≅ scheme W where
  hom := Proj.map (projectiveGraded W C) (projective_irrelevant W C)
  inv := Proj.map (inverseProjectiveGraded W C) (inverseProjective_irrelevant W C)
  hom_inv_id := by
    rw [← Proj.map_comp]
    exact (nativeProjMap_congr _ _ _
      (by simp) (projective_comp_inverseProjective W C)).trans Proj.map_id
  inv_hom_id := by
    rw [← Proj.map_comp]
    exact (nativeProjMap_congr _ _ _
      (by simp) (inverseProjective_comp_projective W C)).trans Proj.map_id

lemma projectiveIso_over (W : WeierstrassCurve R) (C : WeierstrassCurve.VariableChange R) :
    (projectiveIso W C).hom ≫ structureMap W = structureMap (C • W) :=
  nativeProjMap_over _ _
    (fun a => (projectiveHomogeneous W C).commutes a)

/-- The native admissible isomorphism over the unchanged original base ring. -/
def projectiveOverIso (W : WeierstrassCurve R) (C : WeierstrassCurve.VariableChange R) :
    curveOver (C • W) ≅ curveOver W :=
  Over.isoMk (projectiveIso W C) (projectiveIso_over W C)

private lemma projectivePolynomial_infinity_homogeneous
    (C : WeierstrassCurve.VariableChange R) {n : ℕ}
    {p : MvPolynomial (Fin 3) R} (hp : p.IsHomogeneous n) :
    MvPolynomial.eval ![0, 1, 0] (projectivePolynomial C p) =
      (↑(C.u ^ 3) : R) ^ n * MvPolynomial.eval ![0, 1, 0] p := by
  have he : (MvPolynomial.eval ![0, 1, 0]).comp (projectivePolynomial C) =
      MvPolynomial.eval (fun i => (C.u : R) ^ 3 * ![0, 1, 0] i) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp
    · intro i
      fin_cases i <;> simp [projectivePolynomial, projectiveCoordinates]
  change ((MvPolynomial.eval ![0, 1, 0]).comp (projectivePolynomial C)) p = _
  rw [he]
  simpa only [MvPolynomial.eval, Units.val_pow_eq_pow_val] using
    WeierstrassCurve.Projective.homogeneous_eval_scale p hp
      (RingHom.id R) ![0, 1, 0] ((C.u : R) ^ 3)

private lemma projectiveHomogeneous_infinity (W : WeierstrassCurve R)
    (C : WeierstrassCurve.VariableChange R) {n : ℕ}
    (a : homogeneousCoordinateRing W) (ha : a ∈ grading W n) :
    infinityEval (C • W) (projectiveHomogeneous W C a) =
      (↑(C.u ^ 3) : R) ^ n * infinityEval W a := by
  obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp ha
  change MvPolynomial.eval ![0, 1, 0] (projectivePolynomial C p) =
    (↑(C.u ^ 3) : R) ^ n * MvPolynomial.eval ![0, 1, 0] p
  exact projectivePolynomial_infinity_homogeneous C hp

private def infinityEvaluationAway (W : WeierstrassCurve R)
    (q : homogeneousCoordinateRing W) (v : Rˣ) (hv : infinityEval W q = (v : R)) :
    HomogeneousLocalization.Away (grading W) q →+* R :=
  (Localization.awayLift (infinityEval W) q (by rw [hv]; exact v.isUnit)).comp
    (algebraMap (HomogeneousLocalization.Away (grading W) q) (Localization.Away q))

private lemma infinityEvaluationAway_mk (W : WeierstrassCurve R)
    (q : homogeneousCoordinateRing W) (v : Rˣ) (hv : infinityEval W q = (v : R))
    {d : ℕ} (hq : q ∈ grading W d) (n : ℕ) (a : homogeneousCoordinateRing W)
    (ha : a ∈ grading W (n • d)) :
    infinityEvaluationAway W q v hv (HomogeneousLocalization.Away.mk (grading W) hq n a ha) =
      infinityEval W a * (↑(v⁻¹) : R) ^ n := by
  have hm : infinityEval W q * (↑(v⁻¹) : R) = 1 := by
    rw [hv]
    exact v.mul_inv
  simpa only [infinityEvaluationAway, RingHom.comp_apply,
    HomogeneousLocalization.algebraMap_apply, HomogeneousLocalization.Away.val_mk] using
    Localization.awayLift_mk (infinityEval W) q a (↑(v⁻¹) : R) hm n

private lemma infinityEvaluationAway_product (W : WeierstrassCurve R)
    (a b q : homogeneousCoordinateRing W) (ua ub : Rˣ)
    (hva : infinityEval W a = (ua : R)) (hvb : infinityEval W b = (ub : R))
    {d e : ℕ} (ha : a ∈ grading W d) (hb : b ∈ grading W e)
    (hq : q = a * b) (hvq : infinityEval W q = (↑(ua * ub) : R)) :
    (infinityEvaluationAway W q (ua * ub) hvq).comp
        (HomogeneousLocalization.awayMap (grading W) hb hq) =
      infinityEvaluationAway W a ua hva := by
  apply RingHom.ext
  intro x
  obtain ⟨n, c, hc, rfl⟩ := HomogeneousLocalization.Away.mk_surjective (grading W) ha x
  rw [RingHom.comp_apply, HomogeneousLocalization.awayMap_mk,
    infinityEvaluationAway_mk, infinityEvaluationAway_mk, map_mul, map_pow, hvb]
  have hi : (↑((ua * ub)⁻¹) : R) = (↑(ub⁻¹) : R) * (↑(ua⁻¹) : R) := by
    rw [mul_inv_rev, Units.val_mul]
  rw [hi, mul_pow]
  have hunit : (ub : R) ^ n * (↑(ub⁻¹) : R) ^ n = 1 :=
    pow_mul_pow_eq_one n ub.mul_inv
  linear_combination infinityEval W c * (↑(ua⁻¹) : R) ^ n * hunit

/-- The full native projective change preserves the actual infinity section over any base ring. -/
@[reassoc] lemma projectiveIso_infinity (W : WeierstrassCurve R)
    (C : WeierstrassCurve.VariableChange R) :
    infinitySection (C • W) ≫ (projectiveIso W C).hom = infinitySection W := by
  let V := C • W
  let f : grading W →+*ᵍ grading V := projectiveGraded W C
  let y : homogeneousCoordinateRing V := coordinate V 1
  let L : homogeneousCoordinateRing V := f (coordinate W 1)
  let q : homogeneousCoordinateRing V := y * L
  let u : Rˣ := C.u ^ 3
  have hy : y ∈ grading V 1 := coordinate_mem V 1
  have hL : L ∈ grading V 1 := f.map_mem (coordinate_mem W 1)
  have hvy : infinityEval V y = (↑(1 : Rˣ) : R) := by simp [y]
  have hvL : infinityEval V L = (u : R) := by
    have h := projectiveHomogeneous_infinity W C (coordinate W 1) (coordinate_mem W 1)
    change infinityEval (C • W) (projectiveHomogeneous W C (coordinate W 1)) =
      (↑(C.u ^ 3) : R)
    simpa only [pow_one, infinityEval_coordinate,
      Matrix.cons_val_one, Matrix.cons_val_zero, mul_one] using h
  have hvq : infinityEval V q = (u : R) := by
    change infinityEval V (y * L) = (u : R)
    rw [map_mul, hvy, hvL, Units.val_one, one_mul]
  let E := infinityEvaluationAway V q u hvq
  let dy : chartRing V 1 →+* HomogeneousLocalization.Away (grading V) q :=
    HomogeneousLocalization.awayMap (grading V) (f := y) hL (rfl : q = y * L)
  let dl : HomogeneousLocalization.Away (grading V) L →+*
      HomogeneousLocalization.Away (grading V) q :=
    HomogeneousLocalization.awayMap (grading V) (f := L) hy (mul_comm y L)
  have hey : E.comp dy = infinityChartEval V := by
    change (infinityEvaluationAway V q u hvq).comp
        (HomogeneousLocalization.awayMap (grading V) hL (rfl : q = y * L)) =
      infinityEvaluationAway V y 1 hvy
    simpa only [one_mul] using infinityEvaluationAway_product V y L q 1 u hvy hvL
      hy hL rfl (by simpa only [one_mul] using hvq)
  have hel : E.comp dl = infinityEvaluationAway V L u hvL := by
    change (infinityEvaluationAway V q u hvq).comp
        (HomogeneousLocalization.awayMap (grading V) hy (mul_comm y L)) =
      infinityEvaluationAway V L u hvL
    simpa only [mul_one] using infinityEvaluationAway_product V L y q u 1 hvL hvy
      hL hy (mul_comm y L) (by simpa only [mul_one] using hvq)
  let fm : chartRing W 1 →+* HomogeneousLocalization.Away (grading V) L :=
    HomogeneousLocalization.Away.map f (coordinate W 1)
  have hef : (infinityEvaluationAway V L u hvL).comp fm = infinityChartEval W := by
    apply RingHom.ext
    intro x
    obtain ⟨n, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective
      (grading W) (coordinate_mem W 1) x
    change infinityEvaluationAway V L u hvL
        (HomogeneousLocalization.Away.map f (coordinate W 1)
          (HomogeneousLocalization.Away.mk (grading W) (coordinate_mem W 1) n a ha)) = _
    rw [HomogeneousLocalization.Away.map_mk, infinityEvaluationAway_mk,
      infinityChartEval_mk]
    have ha' : a ∈ grading W n := by simpa using ha
    have he := projectiveHomogeneous_infinity W C a ha'
    change infinityEval V (projectiveHomogeneous W C a) * (↑(u⁻¹) : R) ^ n =
      infinityEval W a
    rw [he]
    have hu : (u : R) ^ n * (↑(u⁻¹) : R) ^ n = 1 :=
      pow_mul_pow_eq_one n u.mul_inv
    change (u : R) ^ n * infinityEval W a * (↑(u⁻¹) : R) ^ n = infinityEval W a
    calc
      _ = infinityEval W a * ((u : R) ^ n * (↑(u⁻¹) : R) ^ n) := by ring
      _ = _ := by rw [hu, mul_one]
  let iL := Proj.awayι (grading V) L hL (by decide : 0 < 1)
  let iq := Proj.awayι (grading V) q (SetLike.mul_mem_graded hy hL) (by decide : 0 < 2)
  have hdy : Spec.map (CommRingCat.ofHom dy) ≫ chart V 1 = iq := by
    exact Proj.SpecMap_awayMap_awayι (𝒜 := grading V) (f := y) (g := L) (x := q)
      (f_deg := hy) (hm := by decide) (g_deg := hL) (hx := rfl)
  have hdl : Spec.map (CommRingCat.ofHom dl) ≫ iL = iq := by
    exact Proj.SpecMap_awayMap_awayι (𝒜 := grading V) (f := L) (g := y) (x := q)
      (f_deg := hL) (hm := by decide) (g_deg := hy) (hx := mul_comm y L)
  have hc : Spec.map (CommRingCat.ofHom dy) ≫ chart V 1 =
      Spec.map (CommRingCat.ofHom dl) ≫ iL := hdy.trans hdl.symm
  have hlift : Spec.map (CommRingCat.ofHom (E.comp dl)) ≫ iL = infinitySection V := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, ← hc,
      ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hey]
    rfl
  change infinitySection V ≫ Proj.map f (projective_irrelevant W C) = infinitySection W
  rw [← hlift, Category.assoc]
  rw [Proj.awayι_comp_map f (projective_irrelevant W C) (by decide : 0 < 1)
    (coordinate W 1) (coordinate_mem W 1)]
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  change Spec.map (CommRingCat.ofHom ((E.comp dl).comp fm)) ≫ chart W 1 = _
  rw [hel, hef]
  rfl

section Field

variable {F : Type u} [Field F]

lemma projectiveIso_infinityPoint (W : WeierstrassCurve F)
    (C : WeierstrassCurve.VariableChange F) :
    (projectiveIso W C).hom (infinityPoint (C • W)) = infinityPoint W :=
  WeierstrassCurve.Projective.Translation.nativeProjMap_infinityPoint _ _
    (projectiveHomogeneous_z W C)

end Field

end WeierstrassCurve.VariableChange
