/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Aglib.KTheory.MilnorK.Dedekind.ResidueDirectSum

/-! Regression tests for the actual finite-support norm-residue square. -/

open IsDedekindDomain IsLocalRing AdicCompletion MilnorK
open DedekindResidue

noncomputable section
attribute [local instance] Classical.decEq

universe u
variable (A S : Type u) [CommRing A] [IsDedekindDomain A]
  [CommRing S] [IsDedekindDomain S] [Algebra A S] [Module.Finite A S]
  [Module.IsTorsionFree A S]
  [∀ p : HeightOneSpectrum A, CharZero (ResidueField (Localization.AtPrime p.asIdeal))]

omit [Module.IsTorsionFree A S] in
-- A single original point is sent to its actual contracted point by its actual norm.
example (n : ℕ) (q : HeightOneSpectrum S)
    (x : K (ResidueField (Localization.AtPrime q.asIdeal)) n) :
    residuePushforward A S n (DFinsupp.single q x) =
      DFinsupp.single (q.under A) (pointResidueNorm A S n q x) :=
  residuePushforward_single A S n q x

-- The coordinate sum uses the original finite set of ideal branches.
example (p : HeightOneSpectrum A) (n : ℕ)
    (y : Π₀ q : HeightOneSpectrum S, K (ResidueField (Localization.AtPrime q.asIdeal)) n) :
    residuePushforward A S n y p =
      ∑ q : @IdealBranch S _ _ (Classical.decEq _) (p.asIdeal.map (algebraMap A S)),
        branchCoordinateNorm A S p n q (y (branchPoint A S p q)) :=
  residuePushforward_apply A S p n y

variable (F E : Type u) [Field F] [CharZero F] [Algebra A F] [IsFractionRing A F]
  [Field E] [Algebra S E] [IsFractionRing S E]
  [Algebra A E] [IsScalarTower A S E]
  [Algebra F E] [IsScalarTower A F E] [FiniteDimensional F E]

-- No finite-support, norm-residue compatibility, or branch-grouping law is assumed.
example (n : ℕ) :
    (totalResidue A F n).comp (finiteExtensionNorm F E (n + 1)) =
      (residuePushforward A S n).comp (totalResidue S E n) :=
  totalResidue_comp_finiteExtensionNorm A S F E n

-- In particular this is the degree-three norm/residue square.
example (x : K E 3) :
    totalResidue A F 2 (finiteExtensionNorm F E 3 x) =
      residuePushforward A S 2 (totalResidue S E 2 x) :=
  totalResidue_finiteExtensionNorm A S F E 2 x
