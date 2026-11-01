/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.IntegralClosure.FiniteEtale.LocalFactorGeneric
public import Aglib.FieldTheory.Galois.TensorFactor

/-! # Bounded Galoisness of the original base-changed local generic field

An arbitrary extension of the original coefficient field may disconnect a
Galois algebra. The specified normalization prime nevertheless selects its
original tensor generic field. The canonical surjective generic map, not a
replacement product decomposition, proves that this field is Galois and that
its automorphism order divides the original order.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace integralClosure.LocalFactor

universe r k l k'

variable (R : Type r) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [HenselianLocalRing R]
  (K : Type k) [Field K] (L : Type l) [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  (K' : Type k') [Field K'] [Algebra K K'] [Algebra R K'] [IsFractionRing R K']

local instance : Algebra.Etale K L := by
  let : Algebra.FormallyEtale K L := Algebra.FormallyEtale.of_isSeparable K L
  let : Algebra.FinitePresentation K L := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  exact ⟨inferInstance, inferInstance⟩

local notation "A" => K' ⊗[K] L

variable (q : Ideal (integralClosure R (K' ⊗[K] L))) [q.IsMaximal]

local notation "S" => Localization.AtPrime q
local notation "M" => K' ⊗[R] S

local instance : Field M := genericField R K' A q

/-- The literal generic field selected by the original normalization prime is
Galois after coefficient extension, and its order divides the original one. -/
theorem baseChange_genericField_isGalois_and_card_dvd :
    IsGalois K' M ∧ Nat.card (M ≃ₐ[K'] M) ∣ Nat.card (L ≃ₐ[K] L) := by
  let φ := genericMap R K' A q
  have hφ := genericMap_surjective R K' A q
  exact ⟨Algebra.TensorProduct.isGalois_factor φ hφ,
    Algebra.TensorProduct.factor_card_aut_dvd φ hφ⟩

/-- The actual selected-field automorphisms restrict into the original Galois
group through the unchanged generic algebra map. -/
def baseChange_genericRestriction : (M ≃ₐ[K'] M) →* (L ≃ₐ[K] L) :=
  Algebra.TensorProduct.factorRestriction (genericMap R K' A q)

/-- The original restriction is injective; no component automorphism is lost. -/
theorem baseChange_genericRestriction_injective :
    Function.Injective (baseChange_genericRestriction R K L K' q) :=
  Algebra.TensorProduct.factorRestriction_injective (genericMap R K' A q)
    (genericMap_surjective R K' A q)

/-- Original old-field elements satisfy the actual automorphism-restriction
square inside the literal selected generic field. -/
theorem baseChange_genericRestriction_commutes (σ : M ≃ₐ[K'] M) (x : L) :
    genericMap R K' A q (1 ⊗ₜ[K] (baseChange_genericRestriction R K L K' q σ x)) =
      σ (genericMap R K' A q (1 ⊗ₜ[K] x)) :=
  Algebra.TensorProduct.factorRestriction_commutes (genericMap R K' A q) σ x

/-- Every original finite Galois group bound is inherited by the same selected
field after arbitrary coefficient-field extension. -/
theorem baseChange_genericField_card_dvd {N : ℕ}
    (hN : Nat.card (L ≃ₐ[K] L) ∣ N) : Nat.card (M ≃ₐ[K'] M) ∣ N :=
  (baseChange_genericField_isGalois_and_card_dvd R K L K' q).2.trans hN

end integralClosure.LocalFactor
