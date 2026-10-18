/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Aglib.RingTheory.LocalizedDedekindFractions

/-! # Actual localized Dedekind model instance checks -/

noncomputable section

open IsDedekindDomain Localization

variable {A S : Type*} [CommRing A] [IsDedekindDomain A]
  [CommRing S] [IsDedekindDomain S] [Algebra A S]
  [Module.IsTorsionFree A S] [Module.Finite A S] (p : HeightOneSpectrum A)

example : Module.Finite (Localization.AtPrime p.asIdeal)
    (Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl)) := inferInstance

example : IsDedekindDomain
    (Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl)) := inferInstance

example : Module.IsTorsionFree (Localization.AtPrime p.asIdeal)
    (Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl)) := inferInstance

variable (E : Type*) [Field E] [Algebra S E] [IsFractionRing S E]

example :
    letI := baseLocalizedFractionAlgebra (S := S) p.asIdeal E
    IsFractionRing (Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl)) E :=
  baseLocalizedFractionRing p.asIdeal E
