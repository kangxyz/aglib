/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Picard.KummerQuotient

/-! # Reflecting original Picard divisibility through Kummer H2

Injectivity of the original roots-of-unity H2 pullback reflects divisibility
in the original Picard group. The construction uses the actual Kummer
boundary, its original pullback square, and its proved kernel. It assumes
neither roots of affine global units nor divisibility of a Picard component.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.Modules.Invertible.PullbackTensor.Local
open AlgebraicGeometry.Scheme.EtaleCohomology.Kummer
open GroupCohomology.Kummer.CoefficientBaseChange

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Picard

universe u w w'

variable {X S : Scheme.{u}}
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{w'} (AbelianSheaf.{u, u + 1} S)]
  (f : S ⟶ X) (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤)))

/-- Injective original H2 roots pullback reflects n-divisibility of an actual
Picard class; the converse is functoriality of the original additive pullback. -/
theorem nsmul_preimage_iff_of_rootsH2_injective
    (h₂ : Function.Injective (rootsCohomologyPullback f n hn hinv 2))
    (c : PicardGroup X) :
    (∃ b : PicardGroup X, n • b = c) ↔
      ∃ b : PicardGroup S, n • b = pullbackClass f c := by
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨pullbackHom f b, ((pullbackHom f).map_nsmul n b).symm⟩
  · intro hc
    apply (picardBoundary_eq_zero_iff X n hn hinv c).mp
    apply h₂
    rw [picardBoundary_pullback, map_zero]
    exact (picardBoundary_eq_zero_iff S n hn (levelInvertible f n hinv)
      (pullbackClass f c)).mpr hc

/-- The actual quotient Picard pullback is injective whenever the original
H2 roots pullback is injective, through the already constructed Kummer injection. -/
theorem picardQuotientPullback_injective_of_rootsH2_injective
    (h₂ : Function.Injective (rootsCohomologyPullback f n hn hinv 2)) :
    Function.Injective (picardQuotientPullback f n) := by
  intro a b hab
  apply picardQuotientBoundary_injective X n hn hinv
  apply h₂
  rw [picardQuotientBoundary_pullback, picardQuotientBoundary_pullback, hab]

end AlgebraicGeometry.Scheme.EtaleCohomology.Picard
