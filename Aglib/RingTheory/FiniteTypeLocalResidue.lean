/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! # Finiteness of the original residue fields of a finite-type curve model -/

@[expose] public noncomputable section

namespace Localization

open IsLocalRing

/-- Zariski's lemma applied through the actual quotient-to-local-residue map. -/
theorem finiteType_localResidue_finite (k S : Type*) [Field k] [CommRing S]
    [Algebra k S] [Algebra.FiniteType k S] (q : Ideal S) [q.IsMaximal] :
    Module.Finite k (ResidueField (Localization.AtPrime q)) := by
  have hs : Function.Surjective (algebraMap S (ResidueField (Localization.AtPrime q))) := by
    intro a
    obtain ⟨b, hb⟩ := (IsLocalization.AtPrime.equivQuotMaximalIdeal q
      (Localization.AtPrime q)).surjective a
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective b
    exact ⟨s, hb⟩
  let : Algebra.FiniteType k (ResidueField (Localization.AtPrime q)) :=
    Algebra.FiniteType.of_surjective
      (IsScalarTower.toAlgHom k S (ResidueField (Localization.AtPrime q))) hs
  exact finite_of_finite_type_of_isJacobsonRing k _

end Localization
