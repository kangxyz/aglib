/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.LocalizedDedekindBranches

/-! # The original fraction field of the actual localized finite model -/

@[expose] public noncomputable section

namespace Localization

variable {A S : Type*} [CommRing A] [IsDomain A]
  [CommRing S] [IsDomain S] [Algebra A S] [Module.IsTorsionFree A S]
  (p : Ideal A) [p.IsPrime]
  (E : Type*) [Field E] [Algebra S E] [IsFractionRing S E]

/-- The original fraction field receives the actual localization lift from the
finite model localized only at denominators from the base. -/
@[instance_reducible]
def baseLocalizedFractionAlgebra :
    Algebra (Localization (Algebra.algebraMapSubmonoid S p.primeCompl)) E :=
  IsLocalization.localizationAlgebraOfSubmonoidLe _ E
    (Algebra.algebraMapSubmonoid S p.primeCompl) (nonZeroDivisors S)
    (algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul S p.primeCompl_le_nonZeroDivisors)

/-- The lift extends the specified original domain map. -/
theorem baseLocalizedFractionTower :
    letI := baseLocalizedFractionAlgebra (S := S) p E
    IsScalarTower S (Localization (Algebra.algebraMapSubmonoid S p.primeCompl)) E :=
  IsLocalization.localization_isScalarTower_of_submonoid_le _ E
    (Algebra.algebraMapSubmonoid S p.primeCompl) (nonZeroDivisors S)
    (algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul S p.primeCompl_le_nonZeroDivisors)

/-- The original field, not a newly chosen fraction field, is a fraction field
of the actual localized finite model. -/
theorem baseLocalizedFractionRing :
    letI := baseLocalizedFractionAlgebra (S := S) p E
    IsFractionRing (Localization (Algebra.algebraMapSubmonoid S p.primeCompl)) E := by
  let := baseLocalizedFractionAlgebra (S := S) p E
  let := baseLocalizedFractionTower (S := S) p E
  exact IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (Algebra.algebraMapSubmonoid S p.primeCompl) _ E

/-- Compatibility with the actual localized base follows from uniqueness of
localization lifts, for any existing compatible map from the localized base. -/
theorem baseLocalizedFractionBaseTower [Algebra A E] [IsScalarTower A S E]
    [Algebra (Localization.AtPrime p) E] [IsScalarTower A (Localization.AtPrime p) E] :
    letI := baseLocalizedFractionAlgebra (S := S) p E
    IsScalarTower (Localization.AtPrime p)
      (Localization (Algebra.algebraMapSubmonoid S p.primeCompl)) E := by
  let := baseLocalizedFractionAlgebra (S := S) p E
  let := baseLocalizedFractionTower (S := S) p E
  let : IsScalarTower A (Localization (Algebra.algebraMapSubmonoid S p.primeCompl)) E :=
    IsScalarTower.to₁₃₄ A S _ E
  apply IsScalarTower.of_algebraMap_eq'
  apply IsLocalization.ringHom_ext p.primeCompl
  ext a
  simp only [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply]

end Localization
