/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.Kaehler.TensorProduct
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# Differential base change to actual generic parameter fields

For fields `k → K`, the coefficient map identifies `K[ι]` with the actual
polynomial base change of `K` along `k → k[ι]`. Localizing the polynomial rings
and using the original coefficient map constructs the canonical action of
`Frac(k[ι])` on `Frac(K[ι])`. The resulting differential equivalence preserves
the actual coefficient derivatives.

The fraction-field algebra is a named reducible non-instance: enabling it
locally retains the canonical map without introducing a global instance diamond
when the two coefficient fields coincide. No finite-variable or separability
assumption is required.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct
open TensorProduct KaehlerDifferential

universe u v w

namespace GenericParameterField

variable (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K] (ι : Type w)

attribute [local instance] MvPolynomial.algebraMvPolynomial
attribute [local instance] SMulCommClass.of_commMonoid

local notation "P" => MvPolynomial ι k
local notation "B" => MvPolynomial ι K
local notation "F" => FractionRing P
local notation "L" => FractionRing B

/-- The canonical generic-parameter field action induced by the original injective
polynomial coefficient map. This is intentionally not a global instance. -/
abbrev fractionAlgebra : Algebra F L := FractionRing.liftAlgebra P L

attribute [local instance] fractionAlgebra

/-- The actual coefficient-extension map between the two generic parameter fields. -/
def fractionMap : F →+* L := algebraMap F L

/-- The canonical field map restricts to the original polynomial coefficient map. -/
theorem fractionMap_algebraMap (f : P) :
    fractionMap k K ι (algebraMap P F f) =
      algebraMap B L (MvPolynomial.map (algebraMap k K) f) := by
  change algebraMap F L (algebraMap P F f) = _
  rw [← IsScalarTower.algebraMap_apply P F L, IsScalarTower.algebraMap_apply P B L,
    MvPolynomial.algebraMap_def]

/-- In particular the canonical field map preserves each actual parameter variable. -/
theorem fractionMap_X (i : ι) :
    fractionMap k K ι (algebraMap P F (MvPolynomial.X i)) =
      algebraMap B L (MvPolynomial.X i) := by
  rw [fractionMap_algebraMap, MvPolynomial.map_X]

/-- The native canonical polynomial pushout gives differential base change over `k[ι]`. -/
def polynomialDifferentialEquiv : B ⊗[K] Ω[K⁄k] ≃ₗ[B] Ω[B⁄P] :=
  tensorKaehlerEquiv k P K B

/-- Localizing the actual polynomial algebra extends its differential base change. -/
def localizedDifferentialEquiv : L ⊗[K] Ω[K⁄k] ≃ₗ[L] Ω[L⁄P] := by
  letI : Algebra.FormallyEtale B L :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors B)
  exact ((AlgebraTensorModule.cancelBaseChange K B L L Ω[K⁄k]).symm.trans
    ((polynomialDifferentialEquiv k K ι).baseChange B L _ _)).trans
      (tensorKaehlerEquivOfFormallyEtale P B L)

/-- Localized base change carries original coefficient derivatives to original derivatives. -/
theorem localizedDifferentialEquiv_tmul_D (t : L) (x : K) :
    localizedDifferentialEquiv k K ι (t ⊗ₜ[K] D k K x) =
      t • D P L (algebraMap K L x) := by
  let : Algebra.FormallyEtale B L :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors B)
  simp only [localizedDifferentialEquiv, LinearEquiv.trans_apply,
    AlgebraTensorModule.cancelBaseChange_symm_tmul, LinearEquiv.baseChange_tmul,
    polynomialDifferentialEquiv, tensorKaehlerEquiv_tmul_D, one_smul,
    tensorKaehlerEquivOfFormallyEtale_apply, mapBaseChange_tmul, map_D,
    ← IsScalarTower.algebraMap_apply K B L]

/-- Enlarging the polynomial base to its actual fraction field changes no differentials:
the kernel in the transitivity sequence is zero because the base localization is unramified. -/
def fractionBaseDifferentialEquiv : Ω[L⁄P] ≃ₗ[L] Ω[L⁄F] := by
  letI : Algebra.FormallyEtale P F :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors P)
  refine LinearEquiv.ofBijective (KaehlerDifferential.map P F L L) ⟨?_, map_surjective P F L⟩
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := (exact_mapBaseChange_map P F L x).mp hx
  rw [Subsingleton.elim y 0, map_zero]

/-- The actual differential equivalence after adjoining independent generic parameters
and passing to the canonical parameter fields. -/
def differentialEquiv : L ⊗[K] Ω[K⁄k] ≃ₗ[L] Ω[L⁄F] :=
  (localizedDifferentialEquiv k K ι).trans (fractionBaseDifferentialEquiv k K ι)

/-- The equivalence preserves the original differential generators, with their actual maps. -/
theorem differentialEquiv_tmul_D (t : L) (x : K) :
    differentialEquiv k K ι (t ⊗ₜ[K] D k K x) =
      t • D F L (algebraMap K L x) := by
  rw [differentialEquiv, LinearEquiv.trans_apply, localizedDifferentialEquiv_tmul_D,
    map_smul]
  change t • KaehlerDifferential.map P F L L (D P L (algebraMap K L x)) = _
  rw [map_D]
  rfl

end GenericParameterField
