/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Formal.ProjectiveLine
public import Aglib.AlgebraicGeometry.Modules.Invertible.Formal.System.Data

/-!
# Compatible formal line bundles from actual successor lifts

Dependent recursion chooses actual bundles, beginning with the specified
closed-fibre bundle. Each successor isomorphism is the specified original
pullback comparison supplied by that lifting step. No passage to Picard
isomorphism classes or additional cocycle premise is involved.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules.Invertible

universe u
variable {R : Type u} [CommRing R] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of R)) (I : Ideal R)
  (L₀ : LineBundle (idealThickeningSpace f (I ^ (0 + 1))))
  (hlift : ∀ n : ℕ, ∀ L : LineBundle (idealThickeningSpace f (I ^ (n + 1))),
    ∃ M : LineBundle (idealThickeningSpace f (I ^ (n + 1 + 1))),
      Nonempty ((pullback (idealThickeningMap f
        (Ideal.pow_le_pow_right (Nat.le_succ (n + 1))))).obj M.val ≅ L.val))

/-- The actual compatible system produced by successor lifting, starting
at the original supplied positive-level bundle. -/
def compatibleLineBundleSystemOfSuccessorLifts : CompatibleLineBundleSystem f I := by
  let B : ∀ n : ℕ, LineBundle (idealThickeningSpace f (I ^ (n + 1))) :=
    Nat.rec (motive := fun n => LineBundle (idealThickeningSpace f (I ^ (n + 1))))
      L₀ (fun n L => Classical.choose (hlift n L))
  exact {
    bundle := B
    successorIso := fun n => Classical.choice (Classical.choose_spec (hlift n (B n))) }

/-- The recursively constructed system retains the specified first bundle literally. -/
@[simp]
theorem compatibleLineBundleSystemOfSuccessorLifts_bundle_zero :
    (compatibleLineBundleSystemOfSuccessorLifts f I L₀ hlift).bundle 0 = L₀ := rfl

/-- Actual compatible line bundles on all positive ideal thickenings of a
scheme affine over the native projective line, starting at the given bundle. -/
def projectiveLineCompatibleSystem (p : X ⟶ Scheme.ProjectiveLine.projectiveP1 R)
    [IsAffineHom p] : CompatibleLineBundleSystem f I :=
  compatibleLineBundleSystemOfSuccessorLifts f I L₀
    (fun n L => exists_lineBundle_lift_projectiveLine_powSucc p f I n L)

/-- The projective-line construction retains the original first bundle literally. -/
@[simp]
theorem projectiveLineCompatibleSystem_bundle_zero
    (p : X ⟶ Scheme.ProjectiveLine.projectiveP1 R) [IsAffineHom p] :
    (projectiveLineCompatibleSystem f I L₀ p).bundle 0 = L₀ := rfl

end AlgebraicGeometry.Scheme.Modules.Invertible
