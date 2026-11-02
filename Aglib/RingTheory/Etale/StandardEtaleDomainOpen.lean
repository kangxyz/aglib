/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Etale.StandardEtaleDomainLocalization
public import Mathlib.RingTheory.Unramified.LocalStructure

/-! # An actual principal standard etale factor open

The original generic prime of a domain supplies a nonzero principal
localization carrying a native standard etale presentation. Its vanishing
factor then gives the actual factor-hypersurface localization isomorphism,
with both the root formula and original scalar triangle.
-/

@[expose] public noncomputable section

open Polynomial

namespace Algebra

/-- An etale domain algebra has an original nonempty principal open which is
the actual localization of a vanishing irreducible factor. The presentation
is constructed from the original generic prime, not an additional input. -/
theorem exists_nonzero_standardEtale_factor_open
    (R B : Type*) [CommRing R] [IsDomain R] [WfDvdMonoid R[X]]
    [CommRing B] [IsDomain B] [Algebra R B] [Etale R B] :
    ∃ s : B, s ≠ 0 ∧ ∃ P : StandardEtalePresentation R (Localization.Away s),
      ∃ p q : R[X], Irreducible p ∧ P.f = p * q ∧ aeval P.x p = 0 ∧
      ∃ e : Localization.Away s ≃ₐ[R] Localization.Away (AdjoinRoot.mk p (P.g * q)),
        e P.x = algebraMap (AdjoinRoot p) _ (AdjoinRoot.root p) ∧
        e.toRingEquiv.toRingHom.comp (algebraMap R (Localization.Away s)) =
          algebraMap R (Localization.Away (AdjoinRoot.mk p (P.g * q))) := by
  obtain ⟨s, hs, hstd⟩ := IsEtaleAt.exists_isStandardEtale (R := R) (⊥ : Ideal B)
  have hs0 : s ≠ 0 := by simpa only [Ideal.mem_bot] using hs
  let : IsDomain (Localization.Away s) :=
    IsLocalization.Away.isDomain (Localization.Away s) hs0
  let : IsStandardEtale R (Localization.Away s) := hstd
  obtain ⟨P⟩ : Nonempty (StandardEtalePresentation R (Localization.Away s)) := inferInstance
  obtain ⟨p, q, hp, hf, hx, _, _, _⟩ :=
    P.P.exists_irreducible_factor_hasMap P.x P.hasMap
  let e := P.equivAwayAdjoinRootFactor p q hf hx
  exact ⟨s, hs0, P, p, q, hp, hf, hx, e,
    P.equivAwayAdjoinRootFactor_x p q hf hx, e.toAlgHom.comp_algebraMap⟩

end Algebra
