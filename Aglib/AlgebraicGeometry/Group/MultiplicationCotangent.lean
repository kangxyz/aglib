/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.RationalPoint.Cotangent
public import Aglib.AlgebraicGeometry.Group.MultiplicationEtale

/-!
# The actual first-order power formula and nonconstant multiplication

The original scheme group multiplication induces addition on cotangent
pullbacks at its identity. The product comparison is proved from the native
axes, projections and smooth cotangent dimensions. Iteration computes the
cotangent pullback of the literal power morphism.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj
open AlgebraicGeometry.Scheme.OverField

universe u

namespace AlgebraicGeometry.Scheme.Group.Multiplication

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k]

/-- The original multiplication carries the pair of identity points to identity. -/
theorem multiplication_pair_pointed (G : Grp (FScheme k)) :
    lift η[G.X] η[G.X] ≫ μ[G.X] = η[G.X] := by
  change η[G.X] * η[G.X] = η[G.X]
  rw [MonObj.one_eq_one]
  exact _root_.one_mul _

/-- The actual group law pulls a cotangent vector back to the sum of its two
projection pullbacks. The unit laws and proved product comparison determine it. -/
theorem groupLaw_cotangent (G : Grp (FScheme k)) (d : ℕ)
    [SmoothOfRelativeDimension d G.X.hom] :
    Cotangent.map (lift η[G.X] η[G.X]) η[G.X] μ[G.X] (multiplication_pair_pointed G) =
      Cotangent.map (lift η[G.X] η[G.X]) η[G.X] (fst G.X G.X) (lift_fst _ _) +
      Cotangent.map (lift η[G.X] η[G.X]) η[G.X] (snd G.X G.X) (lift_snd _ _) := by
  have hleft : (Cotangent.map η[G.X] (lift η[G.X] η[G.X])
      (Cotangent.axisLeft η[G.X] η[G.X]) (Cotangent.axisLeft_point _ _)).comp
      (Cotangent.map (lift η[G.X] η[G.X]) η[G.X] μ[G.X]
        (multiplication_pair_pointed G)) = LinearMap.id := by
    rw [← Cotangent.map_comp]
    exact (Cotangent.map_congr _ _
      (MonObj.lift_comp_one_right (𝟙 G.X) (toUnit G.X)) _ _).trans (Cotangent.map_id _)
  have hright : (Cotangent.map η[G.X] (lift η[G.X] η[G.X])
      (Cotangent.axisRight η[G.X] η[G.X]) (Cotangent.axisRight_point _ _)).comp
      (Cotangent.map (lift η[G.X] η[G.X]) η[G.X] μ[G.X]
        (multiplication_pair_pointed G)) = LinearMap.id := by
    rw [← Cotangent.map_comp]
    exact (Cotangent.map_congr _ _
      (MonObj.lift_comp_one_left (toUnit G.X) (𝟙 G.X)) _ _).trans (Cotangent.map_id _)
  apply LinearMap.ext
  intro a
  apply Cotangent.axes_injective η[G.X] η[G.X] d d
  calc
    _ = (a, a) := by
      apply Prod.ext
      · exact LinearMap.congr_fun hleft a
      · exact LinearMap.congr_fun hright a
    _ = _ := by
      simpa only [Cotangent.projections, LinearMap.coprod_apply, LinearMap.add_apply,
        LinearMap.comp_apply, LinearMap.id_apply] using
        (LinearMap.congr_fun (Cotangent.axes_projections η[G.X] η[G.X]) (a, a)).symm

/-- Cotangent pullback of the actual product of two pointed morphisms is the
sum of their pullbacks. Neither input morphism is assumed to be a homomorphism. -/
theorem cotangent_mul (G : Grp (FScheme k)) (d : ℕ)
    [SmoothOfRelativeDimension d G.X.hom] {T : FScheme k}
    (t : 𝟙_ (FScheme k) ⟶ T) (f g : T ⟶ G.X)
    (hf : t ≫ f = η[G.X]) (hg : t ≫ g = η[G.X]) :
    Cotangent.map t η[G.X] (f * g) (by
      rw [MonObj.comp_mul, hf, hg, MonObj.one_eq_one]
      exact _root_.one_mul _) =
      Cotangent.map t η[G.X] f hf + Cotangent.map t η[G.X] g hg := by
  change Cotangent.map t η[G.X] (lift f g ≫ μ[G.X]) _ = _
  rw [Cotangent.map_comp t (lift η[G.X] η[G.X]) η[G.X] (lift f g) μ[G.X]
    (by rw [comp_lift, hf, hg]) (multiplication_pair_pointed G)]
  rw [groupLaw_cotangent G d, LinearMap.comp_add]
  congr 1
  · rw [← Cotangent.map_comp]
    exact Cotangent.map_congr _ _ (lift_fst f g) _ _
  · rw [← Cotangent.map_comp]
    exact Cotangent.map_congr _ _ (lift_snd f g) _ _

/-- The actual cotangent pullback of multiplication by `n`. -/
def multiplicationCotangent (G : Grp (FScheme k)) (n : ℕ) :
    Cotangent.Space η[G.X] →ₗ[k] Cotangent.Space η[G.X] :=
  Cotangent.map η[G.X] η[G.X] ((𝟙 G.X) ^ n) (multiplication_pointed G n)

/-- Multiplication by `n` acts by the literal natural scalar on the actual
identity cotangent space of every smooth group of fixed relative dimension. -/
theorem multiplicationCotangent_eq_nsmul (G : Grp (FScheme k)) (d : ℕ)
    [SmoothOfRelativeDimension d G.X.hom] (n : ℕ) :
    multiplicationCotangent G n = n • LinearMap.id := by
  induction n with
  | zero =>
      simpa only [multiplicationCotangent, pow_zero, zero_smul, CategoryTheory.Hom.one_def]
        using Cotangent.map_constant η[G.X] η[G.X]
  | succ n ih =>
      calc
        multiplicationCotangent G (n + 1) = multiplicationCotangent G n + LinearMap.id := by
          simpa only [multiplicationCotangent, pow_succ, Cotangent.map_id] using
            cotangent_mul G d η[G.X] ((𝟙 G.X) ^ n) (𝟙 G.X)
              (multiplication_pointed G n) (Category.comp_id _)
        _ = _ := by rw [ih, succ_nsmul]

/-- The same identity expressed over the original base field, without a new
cotangent space or coordinate action. -/
theorem multiplicationCotangent_eq_scalar (G : Grp (FScheme k)) (d : ℕ)
    [SmoothOfRelativeDimension d G.X.hom] (n : ℕ) :
    multiplicationCotangent G n = (n : k) • LinearMap.id := by
  rw [Nat.cast_smul_eq_nsmul, multiplicationCotangent_eq_nsmul G d n]

/-- The local endomorphism is the original multiplication stalk map, transported
only by its proved identity-point equality. -/
def multiplicationLocalMap (G : Grp (FScheme k)) (n : ℕ) :
    (Cotangent.pointData η[G.X]).localRing →+* (Cotangent.pointData η[G.X]).localRing :=
  Cotangent.localMap η[G.X] η[G.X] ((𝟙 G.X) ^ n) (multiplication_pointed G n)

/-- The first-order power formula in the actual origin stalk, modulo the square
of its actual maximal ideal. -/
theorem multiplicationLocalMap_sub_natCast_mem_square (G : Grp (FScheme k)) (d : ℕ)
    [SmoothOfRelativeDimension d G.X.hom] (n : ℕ)
    (a : IsLocalRing.maximalIdeal (Cotangent.pointData η[G.X]).localRing) :
    multiplicationLocalMap G n a -
        (n : (Cotangent.pointData η[G.X]).localRing) * a ∈
      IsLocalRing.maximalIdeal (Cotangent.pointData η[G.X]).localRing ^ 2 := by
  have h := LinearMap.congr_fun (multiplicationCotangent_eq_nsmul G d n)
    ((IsLocalRing.maximalIdeal _).toCotangent a)
  change (IsLocalRing.maximalIdeal _).toCotangent
      ⟨multiplicationLocalMap G n a, _⟩ =
    n • (IsLocalRing.maximalIdeal _).toCotangent a at h
  rw [← map_nsmul] at h
  have hval : (↑(n • a) : (Cotangent.pointData η[G.X]).localRing) = n • (a : _) :=
    map_nsmul (IsLocalRing.maximalIdeal (Cotangent.pointData η[G.X]).localRing).subtype n a
  simpa only [hval, nsmul_eq_mul] using (Ideal.toCotangent_eq _).mp h

/-- An invertible natural scalar cannot make the original multiplication
constant on a positive-dimensional smooth group. -/
theorem multiplication_ne_one_of_smooth_of_isUnit (G : Grp (FScheme k)) (d : ℕ)
    [SmoothOfRelativeDimension d G.X.hom] (hd : 0 < d) (n : ℕ)
    (hn : IsUnit (n : k)) : (𝟙 G.X) ^ n ≠ 1 := by
  let : Smooth G.X.hom := SmoothOfRelativeDimension.smooth d G.X.hom
  let : Nontrivial (Cotangent.Space η[G.X]) := Module.finrank_pos_iff.mp
    (by rw [Cotangent.finrank η[G.X] d]; exact hd)
  obtain ⟨a, ha⟩ := exists_ne (0 : Cotangent.Space η[G.X])
  intro h
  have hz : multiplicationCotangent G n = 0 := by
    unfold multiplicationCotangent
    exact (Cotangent.map_congr _ _ h _ (by
      rw [MonObj.comp_one]
      exact (MonObj.one_eq_one G.X).symm)).trans (Cotangent.map_constant _ _)
  have he := LinearMap.congr_fun (multiplicationCotangent_eq_scalar G d n) a
  rw [hz, LinearMap.zero_apply, LinearMap.smul_apply, LinearMap.id_apply] at he
  exact (smul_ne_zero hn.ne_zero ha) he.symm

/-- Positive-dimensional curve geometry supplies nonconstancy of literal
multiplication from invertibility in the original field. -/
theorem multiplication_ne_one_of_isUnit (G : Grp (FScheme k))
    (hG : Curve.Properties G.X) (n : ℕ) (hn : IsUnit (n : k)) :
    (𝟙 G.X) ^ n ≠ 1 := by
  let := hG.smooth
  exact multiplication_ne_one_of_smooth_of_isUnit G 1 (by decide) n hn

/-- Actual multiplication by an invertible natural scalar is finite and
surjective on the original smooth proper geometrically connected curve group. -/
theorem multiplication_finite_surjective_of_isUnit (G : Grp (FScheme k))
    (hG : Curve.Properties G.X) (n : ℕ) (hn : IsUnit (n : k)) :
    IsFinite ((𝟙 G.X) ^ n).left ∧ Surjective ((𝟙 G.X) ^ n).left :=
  multiplication_finite_surjective_of_ne_one G hG n (multiplication_ne_one_of_isUnit G hG n hn)

/-- Over the original characteristic-zero field, invertible multiplication is
finite etale and surjective without a nonconstancy supplier. -/
theorem multiplication_finite_etale_of_isUnit [CharZero k] (G : Grp (FScheme k))
    (hG : Curve.Properties G.X) (n : ℕ) (hn : IsUnit (n : k)) :
    IsFinite ((𝟙 G.X) ^ n).left ∧ Etale ((𝟙 G.X) ^ n).left ∧
      Surjective ((𝟙 G.X) ^ n).left :=
  multiplication_finite_etale_of_ne_one G hG n (multiplication_ne_one_of_isUnit G hG n hn)

/-- Positive multiplication is finite etale and surjective in characteristic
zero, since the positive natural scalar is a unit of the original field. -/
theorem multiplication_finite_etale_of_pos [CharZero k] (G : Grp (FScheme k))
    (hG : Curve.Properties G.X) (n : ℕ) (hn : 0 < n) :
    IsFinite ((𝟙 G.X) ^ n).left ∧ Etale ((𝟙 G.X) ^ n).left ∧
      Surjective ((𝟙 G.X) ^ n).left :=
  multiplication_finite_etale_of_isUnit G hG n
    (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)))

/-- The original prescribed-origin law gives the same finite surjective
multiplication morphism, with no nonconstancy input. -/
theorem pointedGroupLaw_multiplication_finite_surjective_of_isUnit
    {C : FScheme k} {c : 𝟙_ (FScheme k) ⟶ C} (L : PointedGroupLaw C c)
    (hC : Curve.Properties C) (n : ℕ) (hn : IsUnit (n : k)) :
    letI : GrpObj C := L.law
    IsFinite ((𝟙 C) ^ n).left ∧ Surjective ((𝟙 C) ^ n).left := by
  let : GrpObj C := L.law
  exact multiplication_finite_surjective_of_isUnit { X := C, grp := L.law } hC n hn

/-- The characteristic-zero finite-etale result retains the exact native law
stored by `PointedGroupLaw C c` and the same literal power map. -/
theorem pointedGroupLaw_multiplication_finite_etale_of_isUnit [CharZero k]
    {C : FScheme k} {c : 𝟙_ (FScheme k) ⟶ C} (L : PointedGroupLaw C c)
    (hC : Curve.Properties C) (n : ℕ) (hn : IsUnit (n : k)) :
    letI : GrpObj C := L.law
    IsFinite ((𝟙 C) ^ n).left ∧ Etale ((𝟙 C) ^ n).left ∧
      Surjective ((𝟙 C) ^ n).left := by
  let : GrpObj C := L.law
  exact multiplication_finite_etale_of_isUnit { X := C, grp := L.law } hC n hn

end AlgebraicGeometry.Scheme.Group.Multiplication
