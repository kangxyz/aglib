/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.RegularLocalRing.FiniteProjectiveDimension
public import Aglib.RingTheory.RegularLocalRing.ResidueProjectiveDimension
public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.RingTheory.LocalProperties.ProjectiveDimension

/-!
# Prime localizations of regular local rings

The residue field of `Rₚ` is the localization of the finite `R`-module `R/p`.
The projective-dimension bound over a regular local ring therefore localizes
to a finite bound for that residue field. The residue-field criterion proves
regularity of `Rₚ`; a global regularity premise is not assumed.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory IsLocalRing

namespace IsRegularLocalRing

/-- Every prime localization of a regular local ring is regular local.
The proof uses the actual localized quotient giving its residue field. -/
@[stacks 0AFS]
theorem atPrime (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (p : Ideal R) [p.IsPrime] : IsRegularLocalRing (Localization.AtPrime p) := by
  let A := Localization.AtPrime p
  let M := ModuleCat.of R (R ⧸ p)
  let d := (maximalIdeal R).spanFinrank
  have : HasProjectiveDimensionLE M d :=
    (projectiveDimension_le_iff M d).mp
      (projectiveDimension_le_dimension d R spanFinrank_maximalIdeal.symm M)
  have : HasProjectiveDimensionLE (M.localizedModule p.primeCompl) d :=
    ModuleCat.localizedModule_hasProjectiveDimensionLE d p.primeCompl M
  let q : Ideal A := p.localized' A p.primeCompl (Algebra.linearMap R A)
  have hq : q = maximalIdeal A := by
    change p.localized' A p.primeCompl (Algebra.linearMap R A) = maximalIdeal A
    rw [Submodule.localized'_eq_span, ← Ideal.span,
      Algebra.coe_linearMap, ← Ideal.map]
    exact Localization.AtPrime.map_eq_maximalIdeal
  have : IsLocalizedModule p.primeCompl (M.localizedModuleMkLinearMap p.primeCompl) :=
    ModuleCat.localizedModule_isLocalizedModule M p.primeCompl
  let e₁ : M.localizedModule p.primeCompl ≃ₗ[A] (A ⧸ q) :=
    (IsLocalizedModule.linearEquiv p.primeCompl
      (M.localizedModuleMkLinearMap p.primeCompl)
      (p.toLocalizedQuotient' A p.primeCompl (Algebra.linearMap R A))).extendScalarsOfIsLocalization
        p.primeCompl A
  let e₂ : (A ⧸ q) ≃ₗ[A] ResidueField A :=
    Submodule.quotEquivOfEq q (maximalIdeal A) hq
  let e : M.localizedModule p.primeCompl ≅ ModuleCat.of A (ResidueField A) :=
    (e₁.trans e₂).toModuleIso
  have : HasProjectiveDimensionLE (ModuleCat.of A (ResidueField A)) d :=
    hasProjectiveDimensionLT_of_iso e (d + 1)
  exact of_residueField_hasProjectiveDimensionLE A d

/-- A regular local ring is regular at every prime in the native global
regularity interface. -/
theorem isRegularRing_of_regularLocal (R : Type u) [CommRing R] [IsRegularLocalRing R] :
    IsRegularRing R :=
  isRegularRing_iff.mpr fun p _ => atPrime R p

/-- Regularity at a prime is independent of the chosen localization model. -/
theorem of_isLocalizationAtPrime
    (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (p : Ideal R) [p.IsPrime] (S : Type v) [CommRing S] [Algebra R S]
    [IsLocalization.AtPrime S p] : IsRegularLocalRing S := by
  let := atPrime R p
  exact of_ringEquiv
    (IsLocalization.algEquiv p.primeCompl (Localization.AtPrime p) S).toRingEquiv

end IsRegularLocalRing
