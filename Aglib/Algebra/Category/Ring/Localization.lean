/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.Localization.Algebra

/-!
# Canonical principal localization equations in CommRingCat

## Extraction basis

Existing proofs transferred from frozen dirty R5 revision
`79307ff88f07d34fd5c3edb859f799c55e38f290`. Source identities:

- `R5Lab/AlgebraicGeometry/Curves/RelativeDivisors/SmoothIdeal.lean`, SHA-256
  `1e1f564e4d5d68f6f673a435f935642b06c6faeca7632d110bc71565993a96e4`.

Actual objects, maps, universes and stated conditions are retained.
Native validation coverage is recorded separately in `docs/WORK_PLAN.md` and
the migration records; the source hashes above identify extraction inputs.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w t

open CategoryTheory

section
namespace CommRingCat

variable {R A B : CommRingCat.{u}}

/-- The actual ring localization maps form a commutative square. -/
theorem localizationAway_map_comm (φ : A ⟶ B) (s : A) :
    (CommRingCat.ofHom (algebraMap A (Localization.Away s))) ≫ (CommRingCat.ofHom
      (IsLocalization.Away.map (Localization.Away s) (Localization.Away (φ s)) φ.hom s)) = φ ≫
      (CommRingCat.ofHom (algebraMap B (Localization.Away (φ s)))) := by
  ext a
  exact IsLocalization.map_eq (M := Submonoid.powers s)
    (T := Submonoid.powers (φ s)) (S := Localization.Away s)
    (Q := Localization.Away (φ s)) (g := φ.hom)
    (by
      rintro x ⟨n, rfl⟩
      exact ⟨n, (map_pow φ.hom s n).symm⟩) a

/-- The actual localized kernel is the extension of the original kernel. -/
theorem ker_localizationAway_map (φ : A ⟶ B) (s : A) :
    RingHom.ker ((CommRingCat.ofHom (IsLocalization.Away.map (Localization.Away s)
      (Localization.Away (φ s)) φ.hom s))).hom =
      (RingHom.ker φ.hom).map (algebraMap A (Localization.Away s)) := by
  exact IsLocalization.ker_map (Localization.Away (φ s)) φ.hom
    (Submonoid.map_powers φ.hom s)

end CommRingCat
end
