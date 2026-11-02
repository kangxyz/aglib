/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.GroupTheory.QuotientGroup.Nsmul
public import Aglib.AlgebraicGeometry.Curves.Picard.PointDegree
public import Aglib.AlgebraicGeometry.Curves.Jacobian.Multiplication

/-!
# The Picard degree quotient of a proper curve

For a smooth proper geometrically connected curve over an algebraically closed field and an
invertible level, the original degree identifies `Pic(X)/n` with `ZMod n`. The generic quotient
construction consumes the pure point-degree supplier and the Jacobian divisibility theorem.
The latter retains its existing Kummer-finiteness dependency. Source: Stacks, Tag 03RQ;
Milne, Lectures on Étale Cohomology v2.21, Proposition 14.2, p. 90.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules.Invertible

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve

section Degree

variable {k : Type u} [Field k] {X : FScheme k} (hX : Properties X)

/-- **The kernel of the degree modulo `n` is `n Pic(X)`** for `n` invertible in the
algebraically closed field `k`: a class of degree `n m` differs from `n m [𝒪(o)]` by a class of
degree zero, which is `n`-divisible. -/
theorem curveDegreeMod_ker_of_isUnit_of_isAlgClosed [IsAlgClosed k] (n : ℕ)
    (hn : IsUnit (n : k)) :
    (curveDegreeMod hX n).ker = (nsmulAddMonoidHom (α := PicardGroup X.left) n).range :=
  QuotientAddGroup.intCast_comp_ker_eq_nsmul_range _
    (curveDegree_surjective_of_isAlgClosed hX) n
    (surjective_nsmul_curveDegree_ker_of_isUnit_of_isAlgClosed hX n hn)

/-- **`Pic(X)/n Pic(X) ≃+ ℤ/n` through the degree**, for `n` invertible in the algebraically
closed field `k` (Stacks, Étale Cohomology, proof of Lemma 69.1, Tag 03RQ). -/
def picardQuotientDegreeEquiv [IsAlgClosed k] (n : ℕ) (hn : IsUnit (n : k)) :
    PicardGroup X.left ⧸ (nsmulAddMonoidHom (α := PicardGroup X.left) n).range ≃+ ZMod n :=
  QuotientAddGroup.nsmulEquivZMod _ (curveDegree_surjective_of_isAlgClosed hX) n
    (surjective_nsmul_curveDegree_ker_of_isUnit_of_isAlgClosed hX n hn)

/-- The class of `c` goes to its degree modulo `n`. -/
@[simp] theorem picardQuotientDegreeEquiv_mk [IsAlgClosed k] (n : ℕ) (hn : IsUnit (n : k))
    (c : PicardGroup X.left) :
    picardQuotientDegreeEquiv hX n hn (QuotientAddGroup.mk c) =
      (curveDegree smoothFieldNormality normalComponentsOpen smoothFieldRegularity
        smoothClosedPointDimension smoothFieldDimension Picard.Degree.properCurveProductFormula
        X hX c : ZMod n) := rfl

end Degree

end AlgebraicGeometry.Scheme.OverField.Curve
