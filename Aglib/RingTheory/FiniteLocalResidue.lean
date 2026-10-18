/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.LocalizedPrimeBranches
public import Mathlib.RingTheory.LocalRing.ResidueField.Instances

/-!
# Actual residue extensions of a finite map at original prime points

Only the residue extension is asserted finite. No finiteness of the original
localized ring over the local base is assumed or claimed.
-/

@[expose] public noncomputable section

namespace Localization

open IsLocalRing

variable {A S : Type*} [CommRing A] [CommRing S] [Algebra A S]
  [Module.Finite A S] (p : Ideal A) [p.IsPrime] (q : Ideal S) [q.IsMaximal]

/-- The original finite domain map gives the actual finite local residue extension. -/
theorem basePrimeLocal_residueFinite (hq : q.under A = p) :
    letI := basePrimeLocalAlgebra p q hq
    letI := basePrimeLocal_isLocalHom p q hq
    Module.Finite (ResidueField (Localization.AtPrime p))
      (ResidueField (Localization.AtPrime q)) := by
  let := basePrimeLocalAlgebra p q hq
  let := basePrimeLocal_isLocalHom p q hq
  let := basePrimeLocalTower p q hq
  have hs : Function.Surjective (algebraMap S (ResidueField (Localization.AtPrime q))) := by
    intro a
    obtain ⟨b, hb⟩ := (IsLocalization.AtPrime.equivQuotMaximalIdeal q
      (Localization.AtPrime q)).surjective a
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective b
    exact ⟨s, hb⟩
  let : Module.Finite S (ResidueField (Localization.AtPrime q)) :=
    Module.Finite.of_surjective
      (Algebra.ofId S (ResidueField (Localization.AtPrime q))).toLinearMap hs
  let : Module.Finite A (ResidueField (Localization.AtPrime q)) := Module.Finite.trans S _
  let : Module.Finite (Localization.AtPrime p) (ResidueField (Localization.AtPrime q)) :=
    Module.Finite.of_restrictScalars_finite A (Localization.AtPrime p) _
  exact Module.Finite.of_restrictScalars_finite (Localization.AtPrime p)
    (ResidueField (Localization.AtPrime p)) _

end Localization
