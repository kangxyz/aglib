/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Smooth.SectionComponentAffineRestriction
public import Aglib.AlgebraicGeometry.Morphisms.Affine.CompositePullback
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # The whole marked section component after a finite etale cover

A finite etale cover need not remain geometrically connected over the source
base. This construction selects the actual open component of its whole given
section. It retains that entire section, the etale map to the original family,
and affine pullbacks to every field, without asserting global affineness.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

universe u

/-- The actual section component of a finite etale cover of a smooth family
is a smooth geometrically connected family with the same whole section.
Affineness is required and proved only on its field fibres. -/
theorem exists_finiteEtale_sectionComponent_affine_fibers
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    {X G : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of R)) (n : ℕ)
    [SmoothOfRelativeDimension n p] [QuasiCompact p] [QuasiSeparated p]
    (k : G ⟶ X) [Etale k] [IsFinite k]
    (ρ : Spec (CommRingCat.of R) ⟶ G) (hρ : ρ ≫ (k ≫ p) = 𝟙 _)
    (haff : ∀ (F : Type u) [Field F]
      (z : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of R)),
      IsAffine (pullback p z : Scheme.{u})) :
    ∃ (W : G.Opens) (τ : Spec (CommRingCat.of R) ⟶ W.toScheme),
      (W : Set G) = sectionComponentLocus (k ≫ p) ρ hρ ∧
      τ ≫ W.ι = ρ ∧ τ ≫ (W.ι ≫ (k ≫ p)) = 𝟙 _ ∧
      SmoothOfRelativeDimension n (W.ι ≫ (k ≫ p)) ∧
      QuasiCompact (W.ι ≫ (k ≫ p)) ∧ QuasiSeparated (W.ι ≫ (k ≫ p)) ∧
      GeometricallyConnected (W.ι ≫ (k ≫ p)) ∧
      ∀ (F : Type u) [Field F]
        (z : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of R)),
        IsAffine (pullback (W.ι ≫ (k ≫ p)) z : Scheme.{u}) := by
  let : SmoothOfRelativeDimension n (k ≫ p) := by
    simpa only [Nat.zero_add] using
      (inferInstance : SmoothOfRelativeDimension (0 + n) (k ≫ p))
  have haffG (F : Type u) [Field F]
      (z : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of R)) :
      IsAffine (pullback (k ≫ p) z : Scheme.{u}) := by
    let : IsAffine (pullback p z : Scheme.{u}) := haff F z
    exact isAffine_pullback_comp_of_isAffineHom k p z
  exact exists_noetherian_sectionComponent_restriction_affine_fibers
    R (k ≫ p) n ρ hρ haffG

end AlgebraicGeometry.Scheme
