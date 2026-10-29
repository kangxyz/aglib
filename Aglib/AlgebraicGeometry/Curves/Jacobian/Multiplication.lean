/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.DegreeZero
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finiteness.KummerCurveTorsion
public import Aglib.AlgebraicGeometry.Group.MultiplicationSurjective

/-!
# Multiplication by `n` on the Jacobian of a curve, and divisibility of `Pic⁰`

Let `k` be an algebraically closed field, `X` a smooth proper geometrically connected curve over
`k` (`Curve.Properties X`), and let `P`, locally of finite type and separated over `k`, represent
`Pic_{X/k,(fppf)}` on locally Noetherian test schemes through `R` (for instance the Picard scheme
of `exists_representableBy_fppfPicardSheaf_properties`), with group law
`picardCommGrpObj X.hom P R` and identity component `J = Pic⁰_{X/k}`
(`identityComponentOver P.obj`, with `grpObjIdentityComponentOver`). Let `n` be a natural number
invertible in `k`, and `[n] = (𝟙 J) ^ n : J ⟶ J` the multiplication by `n`. Then:

* `isFinite_multiplication_identityComponentOver_of_isUnit_of_isAlgClosed`: **`[n]` is
  finite**;
* `surjective_multiplication_identityComponentOver_of_isUnit_of_isAlgClosed`: **`[n]` is
  surjective**;
* `exists_pow_eq_identityComponentOver_of_isUnit_of_isAlgClosed`: every `k`-point of `J` is an
  `n`-th power;
* `exists_nsmul_eq_of_curveDegree_eq_zero_of_isUnit_of_isAlgClosed` and
  `surjective_nsmul_curveDegree_ker_of_isUnit_of_isAlgClosed`: **`Pic⁰(X) = ker(deg : Pic(X) → ℤ)`
  is `n`-divisible**: every class of degree zero is `n` times a class of degree zero.

For an abelian variety these are Stacks, Groupoid Schemes, Proposition 9.11 (3) and (4), Tag
03RP. Stacks, Étale Cohomology, Section 69, Tag 03RN, uses the surjectivity of
`n : Pic⁰(X) → Pic⁰(X)` in the proof of Lemma 69.1, Tag 03RQ, through `Pic⁰(X) = Pic⁰_{X/k}(k)`,
for a smooth projective curve over an algebraically closed field. The proof here applies
[MultiplicationSurjective](../../Group/MultiplicationSurjective.lean) to `J`, which is proper
(`isProper_identityComponentOver_of_isAlgClosed`) and connected. Its hypothesis, finiteness of
`{p | p ^ n = y}` for every `k`-point `y` of `J`, follows from the identification of the
`k`-points of `J` with the degree-zero classes as groups (`degreeZeroAddEquivOfIsAlgClosed`) and
the finiteness of the `n`-torsion of `Pic(X)` for `n` invertible in `k`
(`KummerFamilyValues.finite_picard_torsion`): the set is empty or a translate of the
`n`-torsion of the degree-zero classes. Smoothness of `J` and `dim J = g` are not used.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.RelativePicard AlgebraicGeometry.Scheme.Group
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.Scheme.OverField.Curve

variable {k : Type u} [Field k] [IsAlgClosed k] {X : FScheme k} (hX : Properties X)
  (P : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType P.obj.hom]
  [IsSeparated P.obj.hom]
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙ (fppfPicardSheaf X.hom).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)

include hX in
/-- **The `k`-point fibres of multiplication by `n` on `J` are finite** for `n` invertible in `k`:
the `k`-points `p` of `J = Pic⁰_{X/k}` with `p ^ n = y` correspond to the degree-zero classes `c`
with `n • c` the class of `y`, a translate of a subset of the finite `n`-torsion of `Pic(X)`. -/
theorem finite_setOf_pow_eq_identityComponentOver_of_isUnit_of_isAlgClosed (n : ℕ)
    (hn : IsUnit (n : k)) :
    letI := picardCommGrpObj X.hom P R
    ∀ y : 𝟙_ (Over (Spec (.of k))) ⟶ identityComponentOver P.obj, {p | p ^ n = y}.Finite := by
  let := picardCommGrpObj X.hom P R
  intro y
  obtain ⟨o, ho⟩ := hX.exists_rationalPoint_of_isAlgClosed
  have htors := EtaleCohomology.KummerFamilyValues.finite_picard_torsion X o ho hX n
    (Nat.pos_of_ne_zero fun h => by simp [h] at hn) hn
  let e := degreeZeroAddEquivOfIsAlgClosed hX P R
  rcases Set.eq_empty_or_nonempty {p | p ^ n = y} with h | ⟨p₀, hp₀⟩
  · rw [h]
    exact Set.finite_empty
  let φ : (𝟙_ (Over (Spec (.of k))) ⟶ identityComponentOver P.obj) → PicardGroup X.left :=
    fun p => ((e.symm (Additive.ofMul p) : _) : PicardGroup X.left) - (e.symm (Additive.ofMul p₀))
  have hφ : Function.Injective φ := fun p q h =>
    Additive.ofMul.injective (e.symm.injective (Subtype.ext (sub_left_injective h)))
  have hpow (q : 𝟙_ (Over (Spec (.of k))) ⟶ identityComponentOver P.obj) :
      n • ((e.symm (Additive.ofMul q) : _) : PicardGroup X.left) =
        ((e.symm (Additive.ofMul (q ^ n)) : _) : PicardGroup X.left) := by
    rw [ofMul_pow, map_nsmul, AddSubgroup.coe_nsmul]
  have hp₀' : p₀ ^ n = y := hp₀
  have hsub : {p | p ^ n = y} ⊆ φ ⁻¹' {c | n • c = 0} := fun p (hp : p ^ n = y) => by
    change n • (_ - _) = (0 : PicardGroup X.left)
    rw [smul_sub, hpow, hpow, hp, hp₀', sub_self]
  exact (htors.preimage hφ.injOn).subset hsub

include hX in
/-- **Multiplication by `n` on the Jacobian is finite** for `n` invertible in `k` (for an abelian
variety: Stacks, Groupoid Schemes, Lemma 9.8, Tag 0BFG): `[n] = (𝟙 J) ^ n` on
`J = Pic⁰_{X/k}` of a curve over an algebraically closed field. -/
theorem isFinite_multiplication_identityComponentOver_of_isUnit_of_isAlgClosed (n : ℕ)
    (hn : IsUnit (n : k)) :
    letI := picardCommGrpObj X.hom P R
    IsFinite ((𝟙 (identityComponentOver P.obj)) ^ n).left := by
  let := picardCommGrpObj X.hom P R
  have := isProper_identityComponentOver_of_isAlgClosed hX P R
  exact Multiplication.multiplication_isFinite_of_finite_setOf_pow_eq_of_isAlgClosed _ n
    (finite_setOf_pow_eq_identityComponentOver_of_isUnit_of_isAlgClosed hX P R n hn)

include hX in
/-- **Multiplication by `n` on the Jacobian is surjective** for `n` invertible in `k` (for an
abelian variety: Stacks, Groupoid Schemes, Proposition 9.11(3), Tag 03RP): `[n] = (𝟙 J) ^ n` on
`J = Pic⁰_{X/k}` of a curve over an algebraically closed field. -/
theorem surjective_multiplication_identityComponentOver_of_isUnit_of_isAlgClosed (n : ℕ)
    (hn : IsUnit (n : k)) :
    letI := picardCommGrpObj X.hom P R
    Surjective ((𝟙 (identityComponentOver P.obj)) ^ n).left := by
  let := picardCommGrpObj X.hom P R
  have := isProper_identityComponentOver_of_isAlgClosed hX P R
  exact Multiplication.multiplication_surjective_of_finite_setOf_pow_eq_of_isAlgClosed _ n
    (finite_setOf_pow_eq_identityComponentOver_of_isUnit_of_isAlgClosed hX P R n hn)

include hX in
/-- **The `k`-points of the Jacobian form an `n`-divisible group** for `n` invertible in `k` (for
an abelian variety: Stacks, Groupoid Schemes, Proposition 9.11(4), Tag 03RP): every `k`-point of
`J = Pic⁰_{X/k}` is an `n`-th power for the group law of `grpObjIdentityComponentOver`. -/
theorem exists_pow_eq_identityComponentOver_of_isUnit_of_isAlgClosed (n : ℕ) (hn : IsUnit (n : k)) :
    letI := picardCommGrpObj X.hom P R
    ∀ y : 𝟙_ (Over (Spec (.of k))) ⟶ identityComponentOver P.obj, ∃ p, p ^ n = y := by
  let := picardCommGrpObj X.hom P R
  have := isProper_identityComponentOver_of_isAlgClosed hX P R
  exact Multiplication.exists_pow_eq_of_finite_setOf_pow_eq_of_isAlgClosed _ n
    (finite_setOf_pow_eq_identityComponentOver_of_isUnit_of_isAlgClosed hX P R n hn)

/-- **`Pic⁰(X)` is `n`-divisible** for `n` invertible in `k` (Stacks, Groupoid Schemes,
Proposition 9.11(4), Tag 03RP, through `Pic⁰(X) = Pic⁰_{X/k}(k)`; used in the proof of Stacks,
Étale Cohomology, Lemma 69.1, Tag 03RQ): for a curve `X` over an algebraically closed field, every
class of degree zero is `n` times a class of degree zero. -/
theorem exists_nsmul_eq_of_curveDegree_eq_zero_of_isUnit_of_isAlgClosed (n : ℕ)
    (hn : IsUnit (n : k)) (c : PicardGroup X.left)
    (hc : curveDegree smoothFieldNormality normalComponentsOpen smoothFieldRegularity
      smoothClosedPointDimension smoothFieldDimension Picard.Degree.properCurveProductFormula
      X hX c = 0) :
    ∃ c' : PicardGroup X.left,
      curveDegree smoothFieldNormality normalComponentsOpen smoothFieldRegularity
        smoothClosedPointDimension smoothFieldDimension Picard.Degree.properCurveProductFormula
        X hX c' = 0 ∧ n • c' = c := by
  obtain ⟨P, R, hP, hsep, -⟩ := exists_representableBy_fppfPicardSheaf_properties hX
  let := picardCommGrpObj X.hom P R
  let e := degreeZeroAddEquivOfIsAlgClosed hX P R
  obtain ⟨p, hp⟩ := exists_pow_eq_identityComponentOver_of_isUnit_of_isAlgClosed hX P R n hn
    (Additive.toMul (e ⟨c, hc⟩))
  refine ⟨e.symm (Additive.ofMul p), (e.symm (Additive.ofMul p)).2, ?_⟩
  rw [← AddSubgroup.coe_nsmul, ← map_nsmul, ← ofMul_pow, hp, ofMul_toMul, AddEquiv.symm_apply_apply]

/-- **`Pic⁰(X)` is `n`-divisible**, as a subgroup: multiplication by `n` is surjective on
`ker(deg : Pic(X) → ℤ)` for a curve `X` over an algebraically closed field and `n` invertible in
`k`. -/
theorem surjective_nsmul_curveDegree_ker_of_isUnit_of_isAlgClosed (n : ℕ) (hn : IsUnit (n : k)) :
    Function.Surjective fun c : (curveDegree smoothFieldNormality normalComponentsOpen
      smoothFieldRegularity smoothClosedPointDimension smoothFieldDimension
      Picard.Degree.properCurveProductFormula X hX).ker => n • c := by
  intro c
  obtain ⟨c', hc', hcc⟩ :=
    exists_nsmul_eq_of_curveDegree_eq_zero_of_isUnit_of_isAlgClosed hX n hn c.1 c.2
  exact ⟨⟨c', hc'⟩, Subtype.ext (by rw [AddSubgroup.coe_nsmul]; exact hcc)⟩

end AlgebraicGeometry.Scheme.OverField.Curve
