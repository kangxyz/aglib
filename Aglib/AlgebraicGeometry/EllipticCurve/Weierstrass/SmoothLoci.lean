/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.InfinityChart
public import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.Points
public import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
public import Mathlib.RingTheory.Smooth.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.Tactic.LinearCombination

/-!
# Explicit smooth opens and singular support of the Weierstrass cubic

The literal affine and infinity equations give actual submersive presentations
after inverting their selected Jacobians. The resulting morphisms are smooth
of relative dimension one. The full infinity complement lies in the specified
smooth open. Singular-point uniqueness is proved in every characteristic.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Polynomial
universe u

namespace WeierstrassCurve.Projective

open MvPolynomial

variable {R : Type u} [CommRing R]

/-- The literal infinity equation, with variables `u=X/Y`, `v=Z/Y`. -/
def infinityEquation (W : WeierstrassCurve R) : MvPolynomial (Fin 2) R :=
  X 0 ^ 3 + MvPolynomial.C W.a₂ * X 0 ^ 2 * X 1 + MvPolynomial.C W.a₄ * X 0 * X 1 ^ 2 +
    MvPolynomial.C W.a₆ * X 1 ^ 3 - MvPolynomial.C W.a₁ * X 0 * X 1 - MvPolynomial.C W.a₃ * X 1 ^
      2 - X 1

/-- The two-variable quotient by the literal infinity-chart equation. -/
abbrev infinityEquationRing (W : WeierstrassCurve R) :=
  MvPolynomial (Fin 2) R ⧸ Ideal.span (Set.range (fun _ : Unit => infinityEquation W))

/-- The coordinate `u` in the two-variable infinity equation ring. -/
def infinityEquationU (W : WeierstrassCurve R) : infinityEquationRing W :=
  Ideal.Quotient.mk _ (X 0)
/-- The coordinate `v` in the two-variable infinity equation ring. -/
def infinityEquationV (W : WeierstrassCurve R) : infinityEquationRing W :=
  Ideal.Quotient.mk _ (X 1)

/-- The algebra map from the two-variable infinity equation ring to the monic infinity ring. -/
def infinityEquationToRing (W : WeierstrassCurve R) :
    infinityEquationRing W →ₐ[R] infinityRing W :=
  Ideal.Quotient.liftₐ _ (aeval ![infinityU W, infinityV W]) (by
    change Ideal.span _ ≤ RingHom.ker (MvPolynomial.aeval ![infinityU W, infinityV W]).toRingHom
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change MvPolynomial.aeval _ (infinityEquation W) = 0
    simp only [infinityEquation, map_add, map_sub, map_mul, map_pow, MvPolynomial.aeval_C,
      MvPolynomial.aeval_X,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination -(infinity_relation W))

@[simp] lemma infinityEquationToRing_u (W : WeierstrassCurve R) :
    infinityEquationToRing W (infinityEquationU W) = infinityU W := by
  simp [infinityEquationToRing, infinityEquationU]
@[simp] lemma infinityEquationToRing_v (W : WeierstrassCurve R) :
    infinityEquationToRing W (infinityEquationV W) = infinityV W := by
  simp [infinityEquationToRing, infinityEquationV]

lemma infinityEquation_relation (W : WeierstrassCurve R) :
    infinityEquationU W ^ 3 + algebraMap R _ W.a₂ * infinityEquationU W ^ 2 * infinityEquationV W +
      algebraMap R _ W.a₄ * infinityEquationU W * infinityEquationV W ^ 2 +
      algebraMap R _ W.a₆ * infinityEquationV W ^ 3 -
      algebraMap R _ W.a₁ * infinityEquationU W * infinityEquationV W -
      algebraMap R _ W.a₃ * infinityEquationV W ^ 2 - infinityEquationV W = 0 := by
  have h : Ideal.Quotient.mk (Ideal.span (Set.range (fun _ : Unit => infinityEquation W)))
      (infinityEquation W) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.subset_span ⟨(), rfl⟩)
  conv_lhs at h => arg 2; unfold infinityEquation
  simpa only [map_add, map_sub, map_mul, map_pow, infinityEquationU, infinityEquationV,
    Ideal.Quotient.algebraMap_eq, IsScalarTower.algebraMap_apply R (MvPolynomial (Fin 2) R),
    MvPolynomial.algebraMap_eq] using h

/-- The algebra map from the monic infinity ring to the two-variable equation presentation. -/
def infinityRingToEquation (W : WeierstrassCurve R) :
    infinityRing W →ₐ[R] infinityEquationRing W :=
  AdjoinRoot.liftAlgHom _ (Polynomial.aeval (infinityEquationV W)) (infinityEquationU W) (by
    simp only [infinityPolynomial, Polynomial.eval₂_add, Polynomial.eval₂_sub,
      Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X,
      AlgHom.coe_toRingHom, map_sub, map_mul, map_pow, Polynomial.aeval_C,
      Polynomial.aeval_X]
    linear_combination infinityEquation_relation W)

@[simp] lemma infinityRingToEquation_u (W : WeierstrassCurve R) :
    infinityRingToEquation W (infinityU W) = infinityEquationU W := by
  simp [infinityRingToEquation, infinityU, AdjoinRoot.liftAlgHom, AdjoinRoot.lift_root]
@[simp] lemma infinityRingToEquation_v (W : WeierstrassCurve R) :
    infinityRingToEquation W (infinityV W) = infinityEquationV W := by
  simp [infinityRingToEquation, infinityV, AdjoinRoot.liftAlgHom, AdjoinRoot.lift_of]

/-- The two-variable presentation is the already constructed literal infinity ring. -/
def infinityEquationEquiv (W : WeierstrassCurve R) :
    infinityEquationRing W ≃ₐ[R] infinityRing W := by
  refine AlgEquiv.ofAlgHom (infinityEquationToRing W) (infinityRingToEquation W) ?_ ?_
  · apply AdjoinRoot.algHom_ext'
    · apply Polynomial.algHom_ext
      change infinityEquationToRing W (infinityRingToEquation W (infinityV W)) = infinityV W
      simp
    · change infinityEquationToRing W (infinityRingToEquation W (infinityU W)) = infinityU W
      simp
  · apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;>
      change infinityRingToEquation W (infinityEquationToRing W _) = _
    · change infinityRingToEquation W (infinityEquationToRing W (infinityEquationU W)) = _
      rw [infinityEquationToRing_u, infinityRingToEquation_u]
      rfl
    · change infinityRingToEquation W (infinityEquationToRing W (infinityEquationV W)) = _
      rw [infinityEquationToRing_v, infinityRingToEquation_v]
      rfl

/-- Select the derivative with respect to the literal `v` coordinate. -/
def infinityPresentation (W : WeierstrassCurve R) :
    Algebra.PreSubmersivePresentation R (infinityEquationRing W) (Fin 2) Unit where
  __ := Algebra.Presentation.naive (v := fun _ : Unit => infinityEquation W)
  map := fun _ => 1
  map_inj := Function.injective_of_subsingleton _

/-- The Jacobian of the infinity presentation, selecting differentiation in `v`. -/
def infinityJacobian (W : WeierstrassCurve R) : infinityEquationRing W :=
  (infinityPresentation W).jacobian

lemma infinityJacobian_eq (W : WeierstrassCurve R) :
    infinityJacobian W = Ideal.Quotient.mk _ (pderiv 1 (infinityEquation W)) := by
  rw [infinityJacobian, Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det,
    Matrix.det_unique, Algebra.PreSubmersivePresentation.jacobiMatrix_apply,
    Algebra.Generators.algebraMap_apply]
  change aeval (fun i : Fin 2 => (Ideal.Quotient.mk _ (X i) : infinityEquationRing W))
    (pderiv 1 (infinityEquation W)) = _
  have he : MvPolynomial.aeval (fun i : Fin 2 => (Ideal.Quotient.mk _ (X i) : infinityEquationRing
    W)) =
      Ideal.Quotient.mkₐ R (Ideal.span (Set.range (fun _ : Unit => infinityEquation W))) := by
    ext i
    simp
  exact congrArg (fun f : MvPolynomial (Fin 2) R →ₐ[R] infinityEquationRing W =>
    f (pderiv 1 (infinityEquation W))) he

/-- The infinity equation ring localized away from its selected Jacobian. -/
abbrev infinitySmoothRing (W : WeierstrassCurve R) := Localization.Away (infinityJacobian W)

/-- Invert exactly the chosen infinity-chart Jacobian. -/
def infinitySmoothPresentation (W : WeierstrassCurve R) :
    Algebra.SubmersivePresentation R (infinitySmoothRing W) (Unit ⊕ Fin 2) (Unit ⊕ Unit) where
  __ := (Algebra.PreSubmersivePresentation.localizationAway
    (infinitySmoothRing W) (infinityJacobian W)).comp (infinityPresentation W)
  jacobian_isUnit := by
    rw [Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
      Algebra.PreSubmersivePresentation.localizationAway_jacobian, Algebra.smul_def]
    exact (IsLocalization.Away.algebraMap_isUnit (infinityJacobian W)).mul
      (IsLocalization.Away.algebraMap_isUnit (infinityJacobian W))

/-- The selected infinity Jacobian localization is standard smooth of relative dimension one. -/
instance infinitySmoothRing_standardSmooth (W : WeierstrassCurve R) :
    Algebra.IsStandardSmoothOfRelativeDimension 1 R (infinitySmoothRing W) :=
  (infinitySmoothPresentation W).isStandardSmoothOfRelativeDimension (by
    simp [Algebra.Presentation.dimension])

end WeierstrassCurve.Projective

namespace WeierstrassCurve.Projective

open MvPolynomial

variable {R : Type u} [CommRing R]

/-- The old infinity section evaluated on the explicit two-coordinate quotient. -/
def infinityEquationEval (W : WeierstrassCurve R) : infinityEquationRing W →+* R :=
  (infinityChartEval W).comp ((toInfinityProjectiveChart W).comp
    (infinityEquationToRing W).toRingHom)

@[simp] lemma infinityEquationEval_u (W : WeierstrassCurve R) :
    infinityEquationEval W (infinityEquationU W) = 0 := by
  simp [infinityEquationEval]
@[simp] lemma infinityEquationEval_v (W : WeierstrassCurve R) :
    infinityEquationEval W (infinityEquationV W) = 0 := by
  simp [infinityEquationEval]
@[simp] lemma infinityEquationEval_constant (W : WeierstrassCurve R) (r : R) :
    infinityEquationEval W (algebraMap R (infinityEquationRing W) r) = r := by
  simp only [infinityEquationEval, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, AlgHom.commutes, toInfinityProjectiveChart_constant]
  exact infinityChartEval_constant W r

/-- The selected Jacobian equals -1 along the entire infinity section. -/
@[simp] lemma infinityEquationEval_jacobian (W : WeierstrassCurve R) :
    infinityEquationEval W (infinityJacobian W) = -1 := by
  rw [infinityJacobian_eq]
  have he : (infinityEquationEval W).comp (Ideal.Quotient.mk _) = MvPolynomial.eval (fun _ : Fin 2
    => 0) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, MvPolynomial.eval_C]
      rw [← MvPolynomial.algebraMap_eq, Ideal.Quotient.mk_algebraMap]
      exact infinityEquationEval_constant W r
    · intro i
      fin_cases i <;> simp [infinityEquationEval, infinityEquationToRing]
  change ((infinityEquationEval W).comp (Ideal.Quotient.mk _)) _ = _
  rw [he]
  simp [infinityEquation]

/-- The lifted section on the actual Jacobian localization. -/
def infinitySmoothEval (W : WeierstrassCurve R) : infinitySmoothRing W →+* R :=
  Localization.awayLift (infinityEquationEval W) (infinityJacobian W) (by simp)

@[simp] lemma infinitySmoothEval_algebraMap (W : WeierstrassCurve R)
    (a : infinityEquationRing W) :
    infinitySmoothEval W (algebraMap _ (infinitySmoothRing W) a) = infinityEquationEval W a := by
  simp only [infinitySmoothEval, Localization.awayLift, IsLocalization.Away.lift_eq]

/-- Literal open immersion of the Jacobian localization into the projective cubic. -/
def infinitySmoothChart (W : WeierstrassCurve R) :
    Spec (.of (infinitySmoothRing W)) ⟶ scheme W :=
  Spec.map (CommRingCat.ofHom (algebraMap (infinityEquationRing W) (infinitySmoothRing W))) ≫
    (Scheme.Spec.mapIso (infinityEquationEquiv W).symm.toRingEquiv.toCommRingCatIso.op).hom ≫
      infinityAffineChart W

/-- The selected smooth infinity chart is open in the original projective cubic. -/
instance infinitySmoothChart_open (W : WeierstrassCurve R) :
    IsOpenImmersion (infinitySmoothChart W) := by
  unfold infinitySmoothChart
  infer_instance

@[reassoc] lemma infinitySmoothChart_structure (W : WeierstrassCurve R) :
    infinitySmoothChart W ≫ structureMap W =
      Spec.map (CommRingCat.ofHom (algebraMap R (infinitySmoothRing W))) := by
  simp only [infinitySmoothChart, Category.assoc, infinityAffineChart_structure]
  change Spec.map _ ≫ Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  change algebraMap (infinityEquationRing W) (infinitySmoothRing W)
    ((infinityEquationEquiv W).symm (algebraMap R (infinityRing W) r)) = _
  rw [AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply R (infinityEquationRing W)]
  rfl

/-- The selected infinity chart is smooth of relative dimension one over the coefficient
spectrum. -/
instance infinitySmoothChart_smoothOne (W : WeierstrassCurve R) :
    SmoothOfRelativeDimension 1 (infinitySmoothChart W ≫ structureMap W) := by
  rw [infinitySmoothChart_structure]
  apply HasRingHomProperty.Spec_iff.mpr
  apply RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso
  exact (RingHom.isStandardSmoothOfRelativeDimension_algebraMap 1).mpr inferInstance

/-- The original infinity section, lifted into the specified smooth open. -/
def infinitySmoothSection (W : WeierstrassCurve R) :
    Spec (.of R) ⟶ Spec (.of (infinitySmoothRing W)) :=
  Spec.map (CommRingCat.ofHom (infinitySmoothEval W))

@[reassoc] lemma infinitySmoothSection_chart (W : WeierstrassCurve R) :
    infinitySmoothSection W ≫ infinitySmoothChart W = infinitySection W := by
  simp only [infinitySmoothSection, infinitySmoothChart, infinityAffineChart,
    infinitySection]
  change Spec.map _ ≫ Spec.map _ ≫ Spec.map _ ≫ Spec.map _ ≫ chart W 1 = _
  rw [← Spec.map_comp_assoc, ← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
  congr 1
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  change infinitySmoothEval W (algebraMap (infinityEquationRing W) (infinitySmoothRing W)
    ((infinityEquationEquiv W).symm (fromInfinityProjectiveChart W a))) = infinityChartEval W a
  rw [infinitySmoothEval_algebraMap]
  change infinityChartEval W (toInfinityProjectiveChart W
    ((infinityEquationEquiv W) ((infinityEquationEquiv W).symm
      (fromInfinityProjectiveChart W a)))) = _
  rw [AlgEquiv.apply_symm_apply, to_fromInfinityProjectiveChart]

@[reassoc] lemma infinitySmoothSection_structure (W : WeierstrassCurve R) :
    infinitySmoothSection W ≫ infinitySmoothChart W ≫ structureMap W = 𝟙 _ := by
  rw [← Category.assoc, infinitySmoothSection_chart, infinitySection_structure]

/-- A concrete open in the same projective scheme. -/
def infinitySmoothOpen (W : WeierstrassCurve R) : (scheme W).Opens :=
  (infinitySmoothChart W).opensRange

theorem infinitySection_range_subset_smoothOpen (W : WeierstrassCurve R) :
    Set.range (infinitySection W) ⊆ (infinitySmoothOpen W : Set (scheme W)) := by
  rintro _ ⟨x, rfl⟩
  change infinitySection W x ∈ Set.range (infinitySmoothChart W)
  exact ⟨infinitySmoothSection W x, congrArg (fun f => f x)
    (infinitySmoothSection_chart W)⟩

/-- The range open of the infinity Jacobian chart is smooth of relative dimension one over the
base. -/
instance infinitySmoothOpen_smoothOne (W : WeierstrassCurve R) :
    SmoothOfRelativeDimension 1 ((infinitySmoothOpen W).ι ≫ structureMap W) := by
  rw [infinitySmoothOpen, ← (infinitySmoothChart W).isoOpensRange_inv_comp, Category.assoc]
  exact inferInstanceAs (SmoothOfRelativeDimension (0 + 1) _)

/-- An unconditional smooth neighbourhood of the entire literal infinity section. -/
theorem infinitySection_smoothNeighbourhood (W : WeierstrassCurve R) :
    ∃ U : (scheme W).Opens, Set.range (infinitySection W) ⊆ (U : Set (scheme W)) ∧
      SmoothOfRelativeDimension 1 (U.ι ≫ structureMap W) :=
  ⟨infinitySmoothOpen W, infinitySection_range_subset_smoothOpen W, inferInstance⟩

end WeierstrassCurve.Projective

namespace WeierstrassCurve.Projective

/-- Two actual singular solutions of the same Weierstrass cubic coincide.
The proof divides by neither 2 nor 3 and also works in a prime quotient. -/
theorem affine_singular_unique {A : Type u} [CommRing A] [IsDomain A]
    (W : WeierstrassCurve A) (r s x y : A)
    (he₀ : W.toAffine.Equation r s)
    (hx₀ : W.toAffine.polynomialX.evalEval r s = 0)
    (hy₀ : W.toAffine.polynomialY.evalEval r s = 0)
    (he : W.toAffine.Equation x y)
    (hx : W.toAffine.polynomialX.evalEval x y = 0)
    (hy : W.toAffine.polynomialY.evalEval x y = 0) :
    x = r ∧ y = s := by
  rw [WeierstrassCurve.Affine.equation_iff'] at he₀ he
  rw [WeierstrassCurve.Affine.evalEval_polynomialX] at hx₀ hx
  rw [WeierstrassCurve.Affine.evalEval_polynomialY] at hy₀ hy
  have hcube : (x - r) ^ 3 = 0 := by
    linear_combination 2 * he - 2 * he₀ - (x-r) * hx - (y-s) * hy -
      (x-r) * hx₀ - (y-s) * hy₀
  have hxr : x = r := sub_eq_zero.mp ((pow_eq_zero_iff (by decide)).mp hcube)
  subst x
  have hsquare : (y - s) ^ 2 = 0 := by
    linear_combination he - he₀ - (y-s) * hy₀
  exact ⟨rfl, sub_eq_zero.mp ((pow_eq_zero_iff (by decide)).mp hsquare)⟩

section Prime
variable {k : Type u} [Field k]

/-- Actual partial derivative in the existing affine coordinate ring. -/
def affineGradientX (W : WeierstrassCurve k) : affineRing W :=
  algebraMap k _ W.a₁ * affineY W -
    (3 * affineX W ^ 2 + 2 * algebraMap k _ W.a₂ * affineX W + algebraMap k _ W.a₄)

/-- Actual partial derivative in the existing affine coordinate ring. -/
def affineGradientY (W : WeierstrassCurve k) : affineRing W :=
  2 * affineY W + algebraMap k _ W.a₁ * affineX W + algebraMap k _ W.a₃

/-- Every prime containing both actual partial derivatives is precisely the
kernel of the specified rational singular point. This includes all scheme
points, with no rationality assumption on the prime under examination. -/
theorem affine_singular_prime_eq (W : WeierstrassCurve k) (r s : k)
    (he₀ : W.toAffine.Equation r s)
    (hx₀ : W.toAffine.polynomialX.evalEval r s = 0)
    (hy₀ : W.toAffine.polynomialY.evalEval r s = 0)
    (p : Ideal (affineRing W)) [p.IsPrime]
    (hx : affineGradientX W ∈ p) (hy : affineGradientY W ∈ p) :
    p = RingHom.ker (affinePointEval W r s he₀) := by
  let q : affineRing W →+* affineRing W ⧸ p := Ideal.Quotient.mk p
  let f : k →+* affineRing W ⧸ p := q.comp (algebraMap k (affineRing W))
  have he₀' : (W.map f).toAffine.Equation (f r) (f s) := by
    rw [WeierstrassCurve.Affine.equation_iff'] at he₀ ⊢
    simpa only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
      WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆,
      map_add, map_sub, map_mul, map_pow, map_zero] using congrArg f he₀
  have hx₀' : (W.map f).toAffine.polynomialX.evalEval (f r) (f s) = 0 := by
    rw [WeierstrassCurve.Affine.evalEval_polynomialX] at hx₀ ⊢
    simpa only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₄,
      map_add, map_sub, map_mul, map_pow, map_zero, map_ofNat] using congrArg f hx₀
  have hy₀' : (W.map f).toAffine.polynomialY.evalEval (f r) (f s) = 0 := by
    rw [WeierstrassCurve.Affine.evalEval_polynomialY] at hy₀ ⊢
    simpa only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃,
      map_add, map_mul, map_zero, map_ofNat] using congrArg f hy₀
  have he' : (W.map f).toAffine.Equation (q (affineX W)) (q (affineY W)) := by
    rw [WeierstrassCurve.Affine.equation_iff']
    have h := congrArg q (affine_relation W)
    simp only [map_add, map_sub, map_mul, map_pow, map_zero] at h
    change q (affineY W) ^ 2 + f W.a₁ * q (affineX W) * q (affineY W) +
      f W.a₃ * q (affineY W) - (q (affineX W) ^ 3 +
        f W.a₂ * q (affineX W) ^ 2 + f W.a₄ * q (affineX W) + f W.a₆) = 0
    linear_combination h
  have hx' : (W.map f).toAffine.polynomialX.evalEval (q (affineX W)) (q (affineY W)) = 0 := by
    rw [WeierstrassCurve.Affine.evalEval_polynomialX]
    have h : q (affineGradientX W) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hx
    simpa only [affineGradientX, f, map_add, map_sub, map_mul, map_pow, map_ofNat,
      RingHom.comp_apply, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
      WeierstrassCurve.map_a₄] using h
  have hy' : (W.map f).toAffine.polynomialY.evalEval (q (affineX W)) (q (affineY W)) = 0 := by
    rw [WeierstrassCurve.Affine.evalEval_polynomialY]
    have h : q (affineGradientY W) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hy
    simpa only [affineGradientY, f, map_add, map_mul, map_ofNat, RingHom.comp_apply,
      WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃] using h
  obtain ⟨hxr, hys⟩ := affine_singular_unique (W.map f) (f r) (f s)
    (q (affineX W)) (q (affineY W)) he₀' hx₀' hy₀' he' hx' hy'
  have hq : q = f.comp (affinePointEval W r s he₀) := by
    apply AdjoinRoot.ringHom_ext
    · apply Polynomial.ringHom_ext
      · intro a
        change q (algebraMap k (affineRing W) a) = f (affinePointEval W r s he₀
          (algebraMap k (affineRing W) a))
        rw [affinePointEval_constant]
        rfl
      · change q (affineX W) = f (affinePointEval W r s he₀ (affineX W))
        simpa only [affinePointEval_x] using hxr
    · change q (affineY W) = f (affinePointEval W r s he₀ (affineY W))
      simpa only [affinePointEval_y] using hys
  calc
    p = RingHom.ker q := (Ideal.mk_ker).symm
    _ = RingHom.ker (f.comp (affinePointEval W r s he₀)) := congrArg RingHom.ker hq
    _ = RingHom.ker (affinePointEval W r s he₀) :=
      RingHom.ker_comp_of_injective _ f.injective

end Prime

end WeierstrassCurve.Projective

namespace WeierstrassCurve.Projective

variable {k : Type u} [Field k]

/-- The actual prime-spectrum point defined by evaluation at the singular coordinates. -/
abbrev affineSingularPoint (W : WeierstrassCurve k) (r s : k)
    (he : W.toAffine.Equation r s) : PrimeSpectrum (affineRing W) :=
  (affinePointOver W r s he).left (IsLocalRing.closedPoint k)

lemma affineSingularPoint_asIdeal (W : WeierstrassCurve k) (r s : k)
    (he : W.toAffine.Equation r s) :
    (affineSingularPoint W r s he).asIdeal = RingHom.ker (affinePointEval W r s he) := by
  change Ideal.comap (affinePointEval W r s he) (IsLocalRing.maximalIdeal k) = _
  rw [IsLocalRing.maximalIdeal_eq_bot]
  rfl

theorem affine_singular_point_iff (W : WeierstrassCurve k) (r s : k)
    (he : W.toAffine.Equation r s)
    (hx : W.toAffine.polynomialX.evalEval r s = 0)
    (hy : W.toAffine.polynomialY.evalEval r s = 0)
    (p : PrimeSpectrum (affineRing W)) :
    p = affineSingularPoint W r s he ↔
      affineGradientX W ∈ p.asIdeal ∧ affineGradientY W ∈ p.asIdeal := by
  constructor
  · rintro rfl
    rw [affineSingularPoint_asIdeal]
    constructor
    · change affinePointEval W r s he (affineGradientX W) = 0
      rw [WeierstrassCurve.Affine.evalEval_polynomialX] at hx
      simpa only [affineGradientX, map_sub, map_add, map_mul, map_pow, map_ofNat,
        affinePointEval_constant, affinePointEval_x, affinePointEval_y] using hx
    · change affinePointEval W r s he (affineGradientY W) = 0
      rw [WeierstrassCurve.Affine.evalEval_polynomialY] at hy
      simpa only [affineGradientY, map_add, map_mul, map_ofNat,
        affinePointEval_constant, affinePointEval_x, affinePointEval_y] using hy
  · rintro ⟨hpx, hpy⟩
    apply PrimeSpectrum.ext
    rw [affineSingularPoint_asIdeal]
    exact affine_singular_prime_eq W r s he hx hy p.asIdeal hpx hpy

/-- The two literal affine Jacobian principal opens cover exactly the complement
of the actual singular point, including non-rational prime-spectrum points. -/
theorem affine_jacobian_open_union (W : WeierstrassCurve k) (r s : k)
    (he : W.toAffine.Equation r s)
    (hx : W.toAffine.polynomialX.evalEval r s = 0)
    (hy : W.toAffine.polynomialY.evalEval r s = 0) :
    (PrimeSpectrum.basicOpen (affineGradientX W) : Set (PrimeSpectrum (affineRing W))) ∪
      (PrimeSpectrum.basicOpen (affineGradientY W) : Set (PrimeSpectrum (affineRing W))) =
        {p | p ≠ affineSingularPoint W r s he} := by
  ext p
  simp only [Set.mem_union, Set.mem_ofPred_eq,
    ne_eq, affine_singular_point_iff W r s he hx hy p, not_and_or]
  rfl

end WeierstrassCurve.Projective

namespace WeierstrassCurve.Projective

open MvPolynomial

variable {R : Type u} [CommRing R]

/-- The literal affine equation, with variables x and y. -/
def affineEquation (W : WeierstrassCurve R) : MvPolynomial (Fin 2) R :=
  X 1 ^ 2 + MvPolynomial.C W.a₁ * X 0 * X 1 + MvPolynomial.C W.a₃ * X 1 -
    (X 0 ^ 3 + MvPolynomial.C W.a₂ * X 0 ^ 2 + MvPolynomial.C W.a₄ * X 0 + MvPolynomial.C W.a₆)

/-- The two-variable quotient by the literal affine Weierstrass equation. -/
abbrev affineEquationRing (W : WeierstrassCurve R) :=
  MvPolynomial (Fin 2) R ⧸ Ideal.span (Set.range (fun _ : Unit => affineEquation W))

/-- The coordinate `x` in the two-variable affine equation ring. -/
def affineEquationX (W : WeierstrassCurve R) : affineEquationRing W :=
  Ideal.Quotient.mk _ (X 0)
/-- The coordinate `y` in the two-variable affine equation ring. -/
def affineEquationY (W : WeierstrassCurve R) : affineEquationRing W :=
  Ideal.Quotient.mk _ (X 1)

/-- The algebra map from the two-variable affine equation ring to the native affine coordinate
ring. -/
def affineEquationToRing (W : WeierstrassCurve R) :
    affineEquationRing W →ₐ[R] affineRing W :=
  Ideal.Quotient.liftₐ _ (aeval ![affineX W, affineY W]) (by
    change Ideal.span _ ≤ RingHom.ker (MvPolynomial.aeval ![affineX W, affineY W]).toRingHom
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change MvPolynomial.aeval _ (affineEquation W) = 0
    simp only [affineEquation, map_add, map_sub, map_mul, map_pow, MvPolynomial.aeval_C,
      MvPolynomial.aeval_X,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination affine_relation W)

@[simp] lemma affineEquationToRing_u (W : WeierstrassCurve R) :
    affineEquationToRing W (affineEquationX W) = affineX W := by
  simp [affineEquationToRing, affineEquationX]
@[simp] lemma affineEquationToRing_v (W : WeierstrassCurve R) :
    affineEquationToRing W (affineEquationY W) = affineY W := by
  simp [affineEquationToRing, affineEquationY]

lemma affineEquation_relation (W : WeierstrassCurve R) :
    affineEquationY W ^ 2 + algebraMap R _ W.a₁ * affineEquationX W * affineEquationY W +
      algebraMap R _ W.a₃ * affineEquationY W - (affineEquationX W ^ 3 +
        algebraMap R _ W.a₂ * affineEquationX W ^ 2 + algebraMap R _ W.a₄ * affineEquationX W +
        algebraMap R _ W.a₆) = 0 := by
  have h : Ideal.Quotient.mk (Ideal.span (Set.range (fun _ : Unit => affineEquation W)))
      (affineEquation W) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.subset_span ⟨(), rfl⟩)
  conv_lhs at h => arg 2; unfold affineEquation
  simpa only [map_add, map_sub, map_mul, map_pow, affineEquationX, affineEquationY,
    Ideal.Quotient.algebraMap_eq, IsScalarTower.algebraMap_apply R (MvPolynomial (Fin 2) R),
    MvPolynomial.algebraMap_eq] using h

/-- The algebra map from the native affine coordinate ring to its two-variable equation
presentation. -/
def affineRingToEquation (W : WeierstrassCurve R) :
    affineRing W →ₐ[R] affineEquationRing W :=
  AdjoinRoot.liftAlgHom _ (Polynomial.aeval (affineEquationX W)) (affineEquationY W) (by
    simp only [WeierstrassCurve.Affine.polynomial, Polynomial.eval₂_add, Polynomial.eval₂_sub,
      Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X,
      AlgHom.coe_toRingHom, map_add, map_mul, map_pow, Polynomial.aeval_C,
      Polynomial.aeval_X]
    linear_combination affineEquation_relation W)

@[simp] lemma affineRingToEquation_u (W : WeierstrassCurve R) :
    affineRingToEquation W (affineX W) = affineEquationX W := by
  simp [affineRingToEquation, affineX, AdjoinRoot.liftAlgHom, AdjoinRoot.lift_of]
@[simp] lemma affineRingToEquation_v (W : WeierstrassCurve R) :
    affineRingToEquation W (affineY W) = affineEquationY W := by
  simp [affineRingToEquation, affineY, AdjoinRoot.liftAlgHom, AdjoinRoot.lift_root]

/-- The two-variable presentation is the existing actual affine coordinate ring. -/
def affineEquationEquiv (W : WeierstrassCurve R) :
    affineEquationRing W ≃ₐ[R] affineRing W := by
  refine AlgEquiv.ofAlgHom (affineEquationToRing W) (affineRingToEquation W) ?_ ?_
  · apply AdjoinRoot.algHom_ext'
    · apply Polynomial.algHom_ext
      change affineEquationToRing W (affineRingToEquation W (affineX W)) = affineX W
      simp
    · change affineEquationToRing W (affineRingToEquation W (affineY W)) = affineY W
      simp
  · apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;>
      change affineRingToEquation W (affineEquationToRing W _) = _
    · change affineRingToEquation W (affineEquationToRing W (affineEquationX W)) = _
      rw [affineEquationToRing_u, affineRingToEquation_u]
      rfl
    · change affineRingToEquation W (affineEquationToRing W (affineEquationY W)) = _
      rw [affineEquationToRing_v, affineRingToEquation_v]
      rfl

/-- Select one actual partial derivative of the literal affine equation. -/
def affinePresentation (W : WeierstrassCurve R) (i : Fin 2) :
    Algebra.PreSubmersivePresentation R (affineRing W) (Fin 2) Unit where
  __ := (Algebra.Presentation.naive (v := fun _ : Unit => affineEquation W)).ofAlgEquiv
    (affineEquationEquiv W)
  map := fun _ => i
  map_inj := Function.injective_of_subsingleton _

/-- The affine partial derivative selected by the coordinate index `i`. -/
def affineJacobian (W : WeierstrassCurve R) (i : Fin 2) : affineRing W :=
  (affinePresentation W i).jacobian

lemma affineJacobian_eq (W : WeierstrassCurve R) (i : Fin 2) :
    affineJacobian W i = aeval ![affineX W, affineY W] (pderiv i (affineEquation W)) := by
  rw [affineJacobian, Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det,
    Matrix.det_unique, Algebra.PreSubmersivePresentation.jacobiMatrix_apply,
    Algebra.Generators.algebraMap_apply]
  have hv : (affinePresentation W i).val = ![affineX W, affineY W] := by
    funext j
    fin_cases j <;> simp [affinePresentation, Algebra.Presentation.ofAlgEquiv,
      Algebra.Generators.ofAlgEquiv, Algebra.Presentation.naive, Algebra.Generators.naive,
      affineEquationEquiv, affineEquationToRing]
  rw [hv]
  rfl

lemma affineJacobian_zero (W : WeierstrassCurve R) :
    affineJacobian W 0 = algebraMap R _ W.a₁ * affineY W -
      (3 * affineX W ^ 2 + 2 * algebraMap R _ W.a₂ * affineX W + algebraMap R _ W.a₄) := by
  rw [affineJacobian_eq]
  simp [affineEquation]
  ring

lemma affineJacobian_one (W : WeierstrassCurve R) :
    affineJacobian W 1 = 2 * affineY W + algebraMap R _ W.a₁ * affineX W + algebraMap R _ W.a₃ := by
  rw [affineJacobian_eq]
  simp [affineEquation]

/-- The affine coordinate ring localized away from the selected partial derivative. -/
abbrev affineSmoothRing (W : WeierstrassCurve R) (i : Fin 2) := Localization.Away (affineJacobian
  W i)

/-- The actual partial-derivative localization has a submersive presentation. -/
def affineSmoothPresentation (W : WeierstrassCurve R) (i : Fin 2) :
    Algebra.SubmersivePresentation R (affineSmoothRing W i) (Unit ⊕ Fin 2) (Unit ⊕ Unit) where
  __ := (Algebra.PreSubmersivePresentation.localizationAway
    (affineSmoothRing W i) (affineJacobian W i)).comp (affinePresentation W i)
  jacobian_isUnit := by
    rw [Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
      Algebra.PreSubmersivePresentation.localizationAway_jacobian, Algebra.smul_def]
    exact (IsLocalization.Away.algebraMap_isUnit (affineJacobian W i)).mul
      (IsLocalization.Away.algebraMap_isUnit (affineJacobian W i))

/-- Each selected affine Jacobian localization is standard smooth of relative dimension one. -/
instance affineSmoothRing_standardSmooth (W : WeierstrassCurve R) (i : Fin 2) :
    Algebra.IsStandardSmoothOfRelativeDimension 1 R (affineSmoothRing W i) :=
  (affineSmoothPresentation W i).isStandardSmoothOfRelativeDimension (by
    simp [Algebra.Presentation.dimension])

end WeierstrassCurve.Projective

namespace WeierstrassCurve.Projective

variable {R : Type u} [CommRing R]

/-- The selected affine Jacobian localization mapped into the original projective cubic. -/
def affineSmoothChart (W : WeierstrassCurve R) (i : Fin 2) :
    Spec (.of (affineSmoothRing W i)) ⟶ scheme W :=
  Spec.map (CommRingCat.ofHom (algebraMap (affineRing W) (affineSmoothRing W i))) ≫ affineChart W

/-- The selected affine Jacobian chart is an open immersion. -/
instance affineSmoothChart_open (W : WeierstrassCurve R) (i : Fin 2) :
    IsOpenImmersion (affineSmoothChart W i) := by
  unfold affineSmoothChart
  infer_instance

@[reassoc] lemma affineSmoothChart_structure (W : WeierstrassCurve R) (i : Fin 2) :
    affineSmoothChart W i ≫ structureMap W =
      Spec.map (CommRingCat.ofHom (algebraMap R (affineSmoothRing W i))) := by
  rw [affineSmoothChart, Category.assoc, affineChart_structure, ← Spec.map_comp]
  congr 1

/-- The selected affine Jacobian chart is smooth of relative dimension one over the base. -/
instance affineSmoothChart_smoothOne (W : WeierstrassCurve R) (i : Fin 2) :
    SmoothOfRelativeDimension 1 (affineSmoothChart W i ≫ structureMap W) := by
  rw [affineSmoothChart_structure]
  apply HasRingHomProperty.Spec_iff.mpr
  apply RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso
  exact (RingHom.isStandardSmoothOfRelativeDimension_algebraMap 1).mpr inferInstance

lemma affineChart_mem_smoothChart_iff (W : WeierstrassCurve R) (i : Fin 2)
    (p : Spec (.of (affineRing W))) :
    affineChart W p ∈ (affineSmoothChart W i).opensRange ↔ affineJacobian W i ∉ p.asIdeal := by
  change affineChart W p ∈ Set.range (affineSmoothChart W i) ↔ _
  have hr : Set.range (Spec.map (CommRingCat.ofHom
      (algebraMap (affineRing W) (affineSmoothRing W i)))) =
      (PrimeSpectrum.basicOpen (affineJacobian W i) : Set (PrimeSpectrum (affineRing W))) :=
    PrimeSpectrum.localization_away_comap_range _ _
  change (∃ q, affineChart W
    (Spec.map (CommRingCat.ofHom (algebraMap (affineRing W) (affineSmoothRing W i))) q) =
      affineChart W p) ↔ _
  simp only [(affineChart W).isOpenEmbedding.injective.eq_iff]
  change p ∈ Set.range (Spec.map (CommRingCat.ofHom
    (algebraMap (affineRing W) (affineSmoothRing W i)))) ↔ _
  rw [hr]
  rfl

end WeierstrassCurve.Projective

namespace WeierstrassCurve.Projective

open MvPolynomial
variable {R : Type u} [CommRing R]

lemma infinityJacobian_formula (W : WeierstrassCurve R) :
    infinityJacobian W = algebraMap R _ W.a₂ * infinityEquationU W ^ 2 +
      2 * algebraMap R _ W.a₄ * infinityEquationU W * infinityEquationV W +
      3 * algebraMap R _ W.a₆ * infinityEquationV W ^ 2 -
      algebraMap R _ W.a₁ * infinityEquationU W -
      2 * algebraMap R _ W.a₃ * infinityEquationV W - 1 := by
  rw [infinityJacobian_eq]
  have hp : pderiv 1 (infinityEquation W) =
      MvPolynomial.C W.a₂ * X 0 ^ 2 + 2 * MvPolynomial.C W.a₄ * X 0 * X 1 + 3 * MvPolynomial.C
        W.a₆ * X 1 ^ 2 -
        MvPolynomial.C W.a₁ * X 0 - 2 * MvPolynomial.C W.a₃ * X 1 - 1 := by
    simp [infinityEquation]
    ring
  rw [hp]
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, map_one,
    infinityEquationU, infinityEquationV, Ideal.Quotient.algebraMap_eq,
    IsScalarTower.algebraMap_apply R (MvPolynomial (Fin 2) R), MvPolynomial.algebraMap_eq]

lemma infinityJacobian_notMem_of_coordinates_mem (W : WeierstrassCurve R)
    (p : Ideal (infinityEquationRing W)) [p.IsPrime]
    (hu : infinityEquationU W ∈ p) (hv : infinityEquationV W ∈ p) :
    infinityJacobian W ∉ p := by
  let q := Ideal.Quotient.mk p
  have hu' : q (infinityEquationU W) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hu
  have hv' : q (infinityEquationV W) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hv
  have hj : q (infinityJacobian W) = -1 := by
    rw [infinityJacobian_formula]
    simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, map_one, hu', hv']
    ring
  intro hjp
  have hz : q (infinityJacobian W) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hjp
  rw [hj] at hz
  have hone : (1 : infinityEquationRing W) ∈ p := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa only [map_one] using (neg_eq_zero.mp hz)
  exact (inferInstance : p.IsPrime).ne_top (Ideal.eq_top_of_isUnit_mem p hone isUnit_one)

/-- The two-variable infinity equation scheme mapped to the original cubic through the monic
chart. -/
def infinityEquationChart (W : WeierstrassCurve R) :
    Spec (.of (infinityEquationRing W)) ⟶ scheme W :=
  (Scheme.Spec.mapIso (infinityEquationEquiv W).symm.toRingEquiv.toCommRingCatIso.op).hom ≫
    infinityAffineChart W

lemma infinityEquationChart_coordinate_zero (W : WeierstrassCurve R)
    (p : Spec (.of (infinityEquationRing W))) :
    coordinate W 0 ∈ (infinityEquationChart W p).asHomogeneousIdeal ↔
      infinityEquationU W ∈ p.asIdeal := by
  change coordinate W 0 ∈ (chart W 1
    (Spec.map (CommRingCat.ofHom (fromInfinityProjectiveChart W))
      ((Scheme.Spec.mapIso (infinityEquationEquiv W).symm.toRingEquiv.toCommRingCatIso.op).hom
        p))).asHomogeneousIdeal ↔ _
  rw [coordinate_mem_chart_iff]
  change (infinityEquationEquiv W).symm
    (fromInfinityProjectiveChart W (normalizedCoordinate W 1 0)) ∈ p.asIdeal ↔ _
  rw [fromInfinityProjectiveChart_normalizedCoordinate]
  change infinityRingToEquation W (infinityU W) ∈ p.asIdeal ↔ _
  rw [infinityRingToEquation_u]

lemma infinityEquationChart_coordinate_two (W : WeierstrassCurve R)
    (p : Spec (.of (infinityEquationRing W))) :
    coordinate W 2 ∈ (infinityEquationChart W p).asHomogeneousIdeal ↔
      infinityEquationV W ∈ p.asIdeal := by
  change coordinate W 2 ∈ (chart W 1
    (Spec.map (CommRingCat.ofHom (fromInfinityProjectiveChart W))
      ((Scheme.Spec.mapIso (infinityEquationEquiv W).symm.toRingEquiv.toCommRingCatIso.op).hom
        p))).asHomogeneousIdeal ↔ _
  rw [coordinate_mem_chart_iff]
  change (infinityEquationEquiv W).symm
    (fromInfinityProjectiveChart W (normalizedCoordinate W 1 2)) ∈ p.asIdeal ↔ _
  rw [fromInfinityProjectiveChart_normalizedCoordinate]
  change infinityRingToEquation W (infinityV W) ∈ p.asIdeal ↔ _
  rw [infinityRingToEquation_v]

/-- The smaller Jacobian infinity open still contains every point with Z=0. -/
theorem mem_infinitySmoothChart_of_z_mem (W : WeierstrassCurve R) (p : scheme W)
    (hz : coordinate W 2 ∈ p.asHomogeneousIdeal) : p ∈ (infinitySmoothChart W).opensRange := by
  have hy : p ∈ (infinityAffineChart W).opensRange := by
    rw [infinityAffineChart_range]
    exact coordinate_y_not_mem_of_z_mem W p hz
  obtain ⟨qA, rfl⟩ := hy
  let e := Scheme.Spec.mapIso (infinityEquationEquiv W).symm.toRingEquiv.toCommRingCatIso.op
  obtain ⟨qB, rfl⟩ := e.hom.surjective qA
  have hv : infinityEquationV W ∈ qB.asIdeal :=
    (infinityEquationChart_coordinate_two W qB).mp hz
  have hu : infinityEquationU W ∈ qB.asIdeal :=
    (infinityEquationChart_coordinate_zero W qB).mp
      (coordinate_x_mem_of_z_mem W _ hz)
  have hj := infinityJacobian_notMem_of_coordinates_mem W qB.asIdeal hu hv
  have hl : qB ∈ Set.range (Spec.map (CommRingCat.ofHom
      (algebraMap (infinityEquationRing W) (infinitySmoothRing W)))) := by
    rw [show Set.range (Spec.map (CommRingCat.ofHom
      (algebraMap (infinityEquationRing W) (infinitySmoothRing W)))) =
      (PrimeSpectrum.basicOpen (infinityJacobian W) : Set (PrimeSpectrum (infinityEquationRing
        W))) from
        PrimeSpectrum.localization_away_comap_range _ _]
    exact hj
  obtain ⟨q, hq⟩ := hl
  refine ⟨q, ?_⟩
  change infinityAffineChart W (e.hom (Spec.map (CommRingCat.ofHom
    (algebraMap (infinityEquationRing W) (infinitySmoothRing W))) q)) = _
  rw [hq]

/-- A coverage statement on actual points, rather than just the larger Y/Z atlas. -/
theorem affine_or_smoothInfinity (W : WeierstrassCurve R) (p : scheme W) :
    p ∈ (affineChart W).opensRange ∨ p ∈ (infinitySmoothChart W).opensRange := by
  by_cases hz : coordinate W 2 ∈ p.asHomogeneousIdeal
  · exact Or.inr (mem_infinitySmoothChart_of_z_mem W p hz)
  · left
    rw [affineChart_range]
    exact hz


end WeierstrassCurve.Projective

/- Migration sources: PointedResolution.Weierstrass.SmoothLoci and the exact
general-CommRing infinity coverage slice of DVRNode:312–425.
Frozen R5 f8a3314ddecffcada2ec721d26d56a937bed9690.
SmoothLoci SHA-256 713376ddb862ce8c4525e52645a47eb691c1226665a34e8dd764444ec6bcbc57.
DVRNode SHA-256 fe38de93b452fcb595b6def1a29f64a03b8ab2e6827928324d02c4b31c6b7fb1.
All original coefficient maps, gradient hypotheses and selected Jacobian opens are retained. -/
