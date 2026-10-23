/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cover.AffineBinary
public import Aglib.AlgebraicGeometry.Modules.Invertible.Formal.Lifting

/-!
# Compatible line bundles from an actual affine binary cover

The original affine binary cover pulls back to every ideal thickening.
Intrinsic square-zero successor lifting and dependent recursion then supply
actual compatible bundles, retaining the first bundle literally.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules.Invertible

universe u

/-- The original projective-line coordinate preimages form an affine binary cover. -/
def projectiveLineAffineBinaryCover
    {R : Type u} [CommRing R] {X : Scheme.{u}}
    (p : X ⟶ Scheme.ProjectiveLine.projectiveP1 R) [IsAffineHom p] :
    Scheme.AffineBinaryCover X where
  first := projectiveLineChartOpen p 0
  second := projectiveLineChartOpen p 1
  affineFirst := isAffineOpen_projectiveLineChartOpen p 0
  affineSecond := isAffineOpen_projectiveLineChartOpen p 1
  affineIntersection := isAffineOpen_projectiveLineChartIntersection p
  covers := projectiveLineChartOpen_sup p

/-- Every actual positive successor lifts line bundles when the ambient
scheme has the specified two affine opens with affine intersection. -/
theorem exists_lineBundle_lift_affineBinary_powSucc
    {R : Type u} [CommRing R] {X : Scheme.{u}} (A : Scheme.AffineBinaryCover X)
    (f : X ⟶ Spec (CommRingCat.of R)) (I : Ideal R) (n : ℕ)
    (L : LineBundle (idealThickeningSpace f (I ^ (n + 1)))) :
    ∃ M : LineBundle (idealThickeningSpace f (I ^ (n + 1 + 1))),
      Nonempty ((pullback (idealThickeningMap f
        (Ideal.pow_le_pow_right (Nat.le_succ (n + 1))))).obj M.val ≅ L.val) := by
  let B := A.pullback (idealThickeningι f (I ^ (n + 1 + 1)))
  let : IsAffine B.first.toScheme := B.affineFirst
  let : IsAffine B.second.toScheme := B.affineSecond
  let : IsAffine (Limits.pullback B.first.ι B.second.ι) := B.affinePullback
  exact exists_lineBundle_lift_twoAffine_of_square_zero
    (idealThickeningMap f (Ideal.pow_le_pow_right (Nat.le_succ (n + 1))))
    (idealThickeningMap_powSucc_ker_sq f I n) B.first.ι B.second.ι
    (by simpa only [Scheme.Opens.opensRange_ι] using B.covers) L

/-- Actual compatible bundles produced from the original two-affine cover
and original ideal-thickening successor maps. -/
def affineBinaryCompatibleSystem
    {R : Type u} [CommRing R] {X : Scheme.{u}} (A : Scheme.AffineBinaryCover X)
    (f : X ⟶ Spec (CommRingCat.of R)) (I : Ideal R)
    (L₀ : LineBundle (idealThickeningSpace f (I ^ (0 + 1)))) :
    CompatibleLineBundleSystem f I :=
  compatibleLineBundleSystemOfSuccessorLifts f I L₀
    (fun n L => exists_lineBundle_lift_affineBinary_powSucc A f I n L)

/-- The binary-cover compatible system starts with the specified bundle literally. -/
@[simp]
theorem affineBinaryCompatibleSystem_bundle_zero
    {R : Type u} [CommRing R] {X : Scheme.{u}} (A : Scheme.AffineBinaryCover X)
    (f : X ⟶ Spec (CommRingCat.of R)) (I : Ideal R)
    (L₀ : LineBundle (idealThickeningSpace f (I ^ (0 + 1)))) :
    (affineBinaryCompatibleSystem A f I L₀).bundle 0 = L₀ := rfl

end AlgebraicGeometry.Scheme.Modules.Invertible
