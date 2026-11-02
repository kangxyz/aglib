/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.ExteriorCoefficient
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.ExteriorOpenArrow
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.ExteriorPullbackComposition


/-!
# The original raw pullback is invertible on its actual open locus

Invertibility is derived from the proved original restriction and composition
arrows. No generic square or determinant-pullback isomorphism is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Differentials

universe u

namespace AlgebraicGeometry.Scheme.Modules.Differentials

/-- On an open immersion the original raw pullback is the original restriction isomorphism. -/
theorem rawFormsPullback_isIso_of_isOpenImmersion {X Y : Scheme.{u}}
    {Λ : CommRingCat.{u}} (a : X ⟶ Spec Λ) (b : Y ⟶ X) [IsOpenImmersion b] (n : ℕ) :
    IsIso (rawFormsPullback a b n) :=
  IsIso.of_isIso_fac_left (rawFormsPullback_restrict a b n)

/-- If the original morphism is open on a supplied open locus, its actual raw arrow
becomes an isomorphism there, using the original composition comparison. -/
theorem rawFormsPullback_isIso_on_openLocus {X Y Z : Scheme.{u}}
    {Λ : CommRingCat.{u}} (a : X ⟶ Spec Λ) (b : Y ⟶ X) (c : Z ⟶ Y)
    [IsOpenImmersion c] [IsOpenImmersion (c ≫ b)] (n : ℕ) :
    IsIso ((pullback c).map (rawFormsPullback a b n)) := by
  let _ := rawFormsPullback_isIso_of_isOpenImmersion a (c ≫ b) n
  let _ := rawFormsPullback_isIso_of_isOpenImmersion (b ≫ a) c n
  let _ : IsIso ((pullback c).map (rawFormsPullback a b n) ≫
      rawFormsPullback (b ≫ a) c n) :=
    IsIso.of_isIso_fac_left (rawFormsPullback_comp a b c n)
  exact IsIso.of_isIso_comp_right ((pullback c).map (rawFormsPullback a b n))
    (rawFormsPullback (b ≫ a) c n)

end AlgebraicGeometry.Scheme.Modules.Differentials
