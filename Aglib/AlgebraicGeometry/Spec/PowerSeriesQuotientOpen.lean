/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Spec.SplitQuotientOpen
public import Aglib.RingTheory.MvPowerSeries.VariableIdeal

/-! # Arbitrary opens on original power-series thickenings -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MvPowerSeries

namespace AlgebraicGeometry.Scheme

universe u
variable {σ A : Type u} [Finite σ] [CommRing A]
local notation "B" => MvPowerSeries σ A
local notation "I" => Ideal.span (Set.range (X : σ → B))
local notation "ε" => (constantCoeff : B →+* A)
local notation "i" => (C : A →+* B)

/-- The actual variable-power quotient sees precisely the intersection of the
arbitrary ambient open with the original zero section, including exponent zero. -/
theorem powerSeriesQuotient_preimage_eq (V : (Spec (.of B)).Opens) (n : ℕ) :
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ n))) ⁻¹ᵁ V =
      Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mk (I ^ n)).comp i)) ⁻¹ᵁ
        (Spec.map (CommRingCat.ofHom ε) ⁻¹ᵁ V) := by
  rw [span_X_eq_ker_constantCoeff (σ := σ) (R := A)]
  exact
    splitQuotient_preimage_eq i ε constantCoeff_comp_C V n

/-- The literal open pullbacks on the original variable-power quotient. -/
def powerSeriesQuotientOpenIso (V : (Spec (.of B)).Opens) (n : ℕ) :
    pullback V.ι (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ n)))) ≅
      pullback (Spec.map (CommRingCat.ofHom ε) ⁻¹ᵁ V).ι
        (Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mk (I ^ n)).comp i))) := by
  rw [span_X_eq_ker_constantCoeff (σ := σ) (R := A)]
  exact
    splitQuotientOpenIso i ε constantCoeff_comp_C V n

end AlgebraicGeometry.Scheme
