/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Formal.ProjectiveLine.Cover
public import Aglib.AlgebraicGeometry.Modules.Invertible.Formal.ProjectiveLine.Thickening
public import Aglib.AlgebraicGeometry.Modules.Invertible.SquareZero.TwoAffine
public import Aglib.AlgebraicGeometry.Modules.IdealPowers.IdealSheaf

/-!
# Successor lifting of line bundles on schemes finite over the projective line

Every positive ideal-power successor lifts actual line bundles, using the
original ideal-thickening transition and an actual pullback isomorphism.
An affine map to the native projective line suffices; in particular the
result applies to finite maps, including nonflat and nonreduced sources.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules.Invertible

universe u

/-- Every line bundle on a positive ideal-power thickening lifts to the next
thickening when the original scheme is affine over the projective line.
The map in the conclusion is the original `idealThickeningMap`. -/
theorem exists_lineBundle_lift_projectiveLine_powSucc
    {R : Type u} [CommRing R] {Y : Scheme.{u}}
    (p : Y ⟶ Scheme.ProjectiveLine.projectiveP1 R) [IsAffineHom p]
    (f : Y ⟶ Spec (CommRingCat.of R)) (I : Ideal R) (n : ℕ)
    (L : LineBundle (idealThickeningSpace f (I ^ (n + 1)))) :
    ∃ M : LineBundle (idealThickeningSpace f (I ^ (n + 1 + 1))),
      Nonempty ((pullback (idealThickeningMap f
        (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)) :
          I ^ (n + 1 + 1) ≤ I ^ (n + 1)))).obj M.val ≅ L.val) := by
  let q : idealThickeningSpace f (I ^ (n + 1 + 1)) ⟶
      Scheme.ProjectiveLine.projectiveP1 R :=
    idealThickeningι f (I ^ (n + 1 + 1)) ≫ p
  have : IsAffineHom q := by dsimp [q]; infer_instance
  exact exists_lineBundle_lift_twoAffine_of_square_zero
    (idealThickeningMap f (Ideal.pow_le_pow_right (Nat.le_succ (n + 1))))
    (idealThickeningMap_powSucc_ker_sq f I n)
    (projectiveLineChartι q 0) (projectiveLineChartι q 1) (projectiveLineChartι_cover q) L

end AlgebraicGeometry.Scheme.Modules.Invertible
