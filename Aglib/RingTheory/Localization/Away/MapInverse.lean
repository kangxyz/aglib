/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Tactic.Ring

/-!
# Maps of the distinguished inverse in a principal localization


Source: `R5Lab.Aglib.RingTheory.Localization.Away.MapInverse`.
Packet SHA-256:
`9c07c465368fd848d2ea905915012e64d916135a4d716eca2668e7ee14cbbaca`.
Actual hypotheses, universes and forward maps are retained; source identity is
separate from compilation and mathematical-adoption evidence.
-/

@[expose] public section

noncomputable section
universe u

namespace Localization.Away

variable {S : Type u} [CommRing S]

lemma invSelf_isUnit {A : Type*} [CommRing A] (r : A) :
    IsUnit (IsLocalization.Away.invSelf r : Localization.Away r) := by
  apply isUnit_iff_exists_inv'.mpr
  exact ⟨algebraMap A _ r, IsLocalization.Away.mul_invSelf r⟩

lemma map_invSelf_of_mul {A : Type*} [CommRing A] (r : A)
    (f : Localization.Away r →+* S) (s : S)
    (h : f (algebraMap _ _ r) * s = 1) : f (IsLocalization.Away.invSelf r) = s := by
  calc
    f (IsLocalization.Away.invSelf r) = (f (algebraMap _ _ r) * s) *
        f (IsLocalization.Away.invSelf r) := by rw [h, one_mul]
    _ = s * f (algebraMap _ _ r * IsLocalization.Away.invSelf r) := by rw [map_mul]; ring
    _ = s := by rw [IsLocalization.Away.mul_invSelf, map_one, mul_one]

end Localization.Away
