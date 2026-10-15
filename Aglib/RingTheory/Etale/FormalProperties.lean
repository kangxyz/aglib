/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: R5Lab contributors
-/
module

public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.RingHom.Smooth

/-!
# Formal etaleness of ring homomorphisms

Formal etaleness is stable under composition, base change and localization.
These ring-homomorphism interfaces reuse the existing algebra-level properties
and the canonical prime-localization map. Localization is only asserted to
preserve formal etaleness; no finite-presentation hypothesis is added.

Extraction source: the first seven generic declarations of
`R5Lab.AlgebraicGeometry.LocalRing.EtaleBaseChange` at revision
`95a3772b895fbc19a81684be4ffd519d0fdcd6b3`.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace RingHom

universe u

namespace FormallyEtale

theorem iff_formallyUnramified_and_formallySmooth {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) :
    f.FormallyEtale ↔ f.FormallyUnramified ∧ f.FormallySmooth := by
  let := f.toAlgebra
  exact Algebra.FormallyEtale.iff_formallyUnramified_and_formallySmooth

theorem stableUnderComposition : RingHom.StableUnderComposition @RingHom.FormallyEtale :=
  fun _ _ _ _ _ _ _ _ hf hg => hf.comp hg

theorem respectsIso : RingHom.RespectsIso @RingHom.FormallyEtale := by
  apply stableUnderComposition.respectsIso
  intro R S _ _ e
  rw [iff_formallyUnramified_and_formallySmooth]
  exact ⟨.of_surjective e.surjective, .of_bijective e.bijective⟩

theorem isStableUnderBaseChange :
    RingHom.IsStableUnderBaseChange @RingHom.FormallyEtale := by
  refine .mk respectsIso ?_
  introv H
  rw [RingHom.formallyEtale_algebraMap] at H ⊢
  let := H
  infer_instance

theorem holdsForLocalization : RingHom.HoldsForLocalization @RingHom.FormallyEtale := by
  intro R S _ _ _ M _
  rw [RingHom.formallyEtale_algebraMap]
  exact Algebra.FormallyEtale.of_isLocalization M

theorem localRingHom
    {R S : Type u} [CommRing R] [CommRing S]
    {p : Ideal R} [p.IsPrime] {q : Ideal S} [q.IsPrime] {f : R →+* S}
    (hpq : p = q.comap f) (hf : f.FormallyEtale) :
    (Localization.localRingHom p q f hpq).FormallyEtale :=
  holdsForLocalization.localRingHom stableUnderComposition
    isStableUnderBaseChange.localizationPreserves hpq hf

end FormallyEtale

/-- Etaleness gives formal etaleness, without asserting finite presentation of
the subsequent prime-localized ring map. -/
theorem Etale.formallyEtale
    {R S : Type u} [CommRing R] [CommRing S] {f : R →+* S} (hf : f.Etale) :
    f.FormallyEtale := by
  let := f.toAlgebra
  let : Algebra.Etale R S := hf
  exact inferInstanceAs (Algebra.FormallyEtale R S)

end RingHom
