/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Kummer.RootBaseChange
public import Aglib.RingTheory.Kummer.Uniformizer
public import Aglib.RingTheory.Henselian.StrictHenselization.DVRFaithfullyFlat

/-! # The original uniformizer-root map to the pointed DVR etale colimit

The unchanged root algebra over the original DVR maps faithfully flatly to the
literal root algebra over its actual closed-point geometric etale colimit.
That target is a DVR at positive root order, by preservation of the original
uniformizer. No target model or etaleness assumption is supplied.
-/

@[expose] public noncomputable section

namespace Algebra.Kummer

universe u

variable (R Ω : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field Ω] [Algebra R Ω] [IsLocalHom (algebraMap R Ω)]
  (N : ℕ) (π : R)

local notation "C" => GeometricEtaleColimit R Ω

/-- The original root map into the root algebra over the actual pointed DVR
colimit is faithfully flat, at every root level. -/
theorem strictHenselianRoot_faithfullyFlat :
    letI := rootBaseChangeAlgebra C N π
    Module.FaithfullyFlat (RootAlgebra N π) (RootAlgebra N (algebraMap R C π)) := by
  let := rootBaseChangeAlgebra C N π
  let : Module.FaithfullyFlat R C := GeometricEtaleColimit.faithfullyFlat_of_dvr R Ω
  exact rootBaseChange_faithfullyFlat C N π

/-- The literal root target over the same pointed colimit is a domain. -/
theorem strictHenselianRoot_isDomain (hN : 0 < N) (hπ : Irreducible π) :
    IsDomain (RootAlgebra N (algebraMap R C π)) := by
  let := GeometricEtaleColimit.isDomain_of_dvr R Ω
  let := GeometricEtaleColimit.isDiscreteValuationRing_of_dvr R Ω
  exact uniformizerRoot_isDomain C (algebraMap R C π)
    (GeometricEtaleColimit.irreducible_algebraMap_of_dvr R Ω hπ) N hN

/-- The actual root target is a DVR; neither a generic-point colimit nor
higher-dimensional strict henselization is substituted here. -/
theorem strictHenselianRoot_isDiscreteValuationRing (hN : 0 < N) (hπ : Irreducible π) :
    letI := strictHenselianRoot_isDomain R Ω N π hN hπ
    IsDiscreteValuationRing (RootAlgebra N (algebraMap R C π)) := by
  let := GeometricEtaleColimit.isDomain_of_dvr R Ω
  let := GeometricEtaleColimit.isDiscreteValuationRing_of_dvr R Ω
  exact uniformizerRoot_isDiscreteValuationRing C (algebraMap R C π)
    (GeometricEtaleColimit.irreducible_algebraMap_of_dvr R Ω hπ) N hN

end Algebra.Kummer
