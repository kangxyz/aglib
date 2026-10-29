/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.Multiplication

/-!
# Consumer checks for `Aglib.AlgebraicGeometry.Curves.Jacobian.Multiplication`

Multiplication by an invertible `n` on the Jacobian `J = Pic⁰_{X/k}` of a smooth proper curve
over an algebraically closed field: finite `k`-point fibres, finiteness, surjectivity,
divisibility of the `k`-points, and `n`-divisibility of the degree-zero classes; axiom guards.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.Modules.Invertible AlgebraicGeometry.Scheme.RelativePicard
open AlgebraicGeometry.Scheme.Group AlgebraicGeometry.Scheme.OverField.Curve
open scoped CategoryTheory.MonObj

universe u

namespace AglibTest.CurvesJacobianMultiplication

variable {k : Type u} [Field k] [IsAlgClosed k] {X : FScheme k}

/-- For any representation of the Picard sheaf, `[n]` on `J` is finite and surjective, and every
`k`-point of `J` is an `n`-th power, for `n` invertible in `k`. -/
example (hX : Curve.Properties X) (P : LocallyNoetherianOver (Spec (.of k)))
    [LocallyOfFiniteType P.obj.hom] [IsSeparated P.obj.hom] (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙ (fppfPicardSheaf X.hom).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P) (n : ℕ) (hn : IsUnit (n : k)) :
    letI := picardCommGrpObj X.hom P R
    IsFinite ((𝟙 (identityComponentOver P.obj)) ^ n).left ∧
      Surjective ((𝟙 (identityComponentOver P.obj)) ^ n).left ∧
      ∀ y : 𝟙_ (Over (Spec (.of k))) ⟶ identityComponentOver P.obj,
        {p | p ^ n = y}.Finite ∧ ∃ p, p ^ n = y :=
  ⟨isFinite_multiplication_identityComponentOver_of_isUnit_of_isAlgClosed hX P R n hn,
    surjective_multiplication_identityComponentOver_of_isUnit_of_isAlgClosed hX P R n hn,
    fun y => ⟨finite_setOf_pow_eq_identityComponentOver_of_isUnit_of_isAlgClosed hX P R n hn y,
      exists_pow_eq_identityComponentOver_of_isUnit_of_isAlgClosed hX P R n hn y⟩⟩

/-- For the Picard scheme of the adapter, `[n]` on `J` is finite and surjective. -/
example (hX : Curve.Properties X) (n : ℕ) (hn : IsUnit (n : k)) :
    ∃ (P : LocallyNoetherianOver (Spec (.of k)))
      (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙ (fppfPicardSheaf X.hom).obj ⋙
        CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
      (_ : LocallyOfFiniteType P.obj.hom) (_ : IsSeparated P.obj.hom),
      (letI := picardCommGrpObj X.hom P R;
        IsFinite ((𝟙 (identityComponentOver P.obj)) ^ n).left ∧
          Surjective ((𝟙 (identityComponentOver P.obj)) ^ n).left) := by
  obtain ⟨P, R, hP, hsep, -⟩ := exists_representableBy_fppfPicardSheaf_properties hX
  exact ⟨P, R, hP, hsep, isFinite_multiplication_identityComponentOver_of_isUnit_of_isAlgClosed hX P R n hn,
    surjective_multiplication_identityComponentOver_of_isUnit_of_isAlgClosed hX P R n hn⟩

/-- `Pic⁰(X)` is `n`-divisible: elementwise and as surjectivity of `n •` on the degree kernel. -/
example (hX : Curve.Properties X) (n : ℕ) (hn : IsUnit (n : k)) (c : PicardGroup X.left)
    (hc : curveDegree smoothFieldNormality normalComponentsOpen smoothFieldRegularity
      smoothClosedPointDimension smoothFieldDimension Picard.Degree.properCurveProductFormula
      X hX c = 0) :
    (∃ c' : PicardGroup X.left,
      curveDegree smoothFieldNormality normalComponentsOpen smoothFieldRegularity
        smoothClosedPointDimension smoothFieldDimension Picard.Degree.properCurveProductFormula
        X hX c' = 0 ∧ n • c' = c) ∧
    Function.Surjective fun c : (curveDegree smoothFieldNormality normalComponentsOpen
      smoothFieldRegularity smoothClosedPointDimension smoothFieldDimension
      Picard.Degree.properCurveProductFormula X hX).ker => n • c :=
  ⟨exists_nsmul_eq_of_curveDegree_eq_zero_of_isUnit_of_isAlgClosed hX n hn c hc,
    surjective_nsmul_curveDegree_ker_of_isUnit_of_isAlgClosed hX n hn⟩

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.finite_setOf_pow_eq_identityComponentOver_of_isUnit_of_isAlgClosed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.finite_setOf_pow_eq_identityComponentOver_of_isUnit_of_isAlgClosed

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.isFinite_multiplication_identityComponentOver_of_isUnit_of_isAlgClosed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.isFinite_multiplication_identityComponentOver_of_isUnit_of_isAlgClosed

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.surjective_multiplication_identityComponentOver_of_isUnit_of_isAlgClosed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.surjective_multiplication_identityComponentOver_of_isUnit_of_isAlgClosed

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.exists_pow_eq_identityComponentOver_of_isUnit_of_isAlgClosed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.exists_pow_eq_identityComponentOver_of_isUnit_of_isAlgClosed

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.exists_nsmul_eq_of_curveDegree_eq_zero_of_isUnit_of_isAlgClosed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.exists_nsmul_eq_of_curveDegree_eq_zero_of_isUnit_of_isAlgClosed

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.surjective_nsmul_curveDegree_ker_of_isUnit_of_isAlgClosed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.surjective_nsmul_curveDegree_ker_of_isUnit_of_isAlgClosed

end AglibTest.CurvesJacobianMultiplication
