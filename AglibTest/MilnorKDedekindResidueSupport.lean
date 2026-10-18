/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Aglib.KTheory.MilnorK.Dedekind.ResidueSupport

/-! Regression tests for actual all-degree Dedekind residue support and its total map. -/

open IsDedekindDomain MilnorK

noncomputable section

variable (S E : Type*) [CommRing S] [IsDedekindDomain S]
  [Field E] [Algebra S E] [IsFractionRing S E]

-- No finite-support hypothesis and no replacement of the original field.
example (n : ℕ) (x : K E (n + 1)) :
    Set.Finite {q : HeightOneSpectrum S |
      DVR.residue (Localization.AtPrime q.asIdeal) E n x ≠ 0} :=
  DedekindResidue.finite_residue_support S E n x

-- The degree-three specialization is the literal all-degree DVR residue.
example (x : K E 3) :
    Set.Finite {q : HeightOneSpectrum S |
      DVR.residue (Localization.AtPrime q.asIdeal) E 2 x ≠ 0} :=
  DedekindResidue.finite_residue_support S E 2 x

-- The obstruction for each entry itself is proved finite, not assumed.
example (a : Eˣ) :
    Set.Finite {q : HeightOneSpectrum S |
      ¬ ∃ u : (Localization.AtPrime q.asIdeal)ˣ,
        MilnorK.K2.DVR.fieldUnits (Localization.AtPrime q.asIdeal) E u = a} :=
  DedekindResidue.finite_nonlocal_units S E a

-- The finitely supported map has the literal original DVR coordinates.
example (n : ℕ) (x : K E (n + 1)) (q : HeightOneSpectrum S) :
    DedekindResidue.totalResidue S E n x q =
      DVR.residue (Localization.AtPrime q.asIdeal) E n x := rfl
