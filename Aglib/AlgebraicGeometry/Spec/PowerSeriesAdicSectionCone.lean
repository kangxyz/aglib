/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Spec.AdicSectionCone
public import Aglib.AlgebraicGeometry.Spec.PowerSeriesAdicSections

/-! # The actual ring-section limit on an arbitrary power-series open -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MvPowerSeries

namespace AlgebraicGeometry.Scheme

universe u
variable {σ : Type} {A : Type u} [Finite σ] [CommRing A] [IsDomain A]
  (V : (Spec (.of (MvPowerSeries σ A))).Opens) [Nonempty V]

local notation "B" => MvPowerSeries σ A
local notation "ε" => (constantCoeff : B →+* A)
local notation "i" => (C : A →+* B)
local notation "U" => splitSectionOpen ε V

/-- The literal structure-ring section cone on the actual variable-power
thickenings is limiting. Both scalar bijectivities and the compatible inverse
are derived, not supplied as final comparison hypotheses. -/
def powerSeriesAdicRingSectionConeIsLimit
    [QuasiCompact (U).ι] [QuasiSeparated (U).ι]
    (hU : Function.Bijective (hartogsScalarMap A U)) :
    IsLimit (adicRingSectionCone V.ι (Ideal.span (Set.range (X : σ → B)))) := by
  rw [span_X_eq_ker_constantCoeff (σ := σ) (R := A)]
  letI := powerSeriesKernel_isAdicComplete (σ := σ) (A := A)
  have hB := powerSeriesAffineScalar_bijective V hU
  have hb := powerSeriesAdicSectionScalar_bijective V hU
  exact adicRingSectionConeIsLimit V.ι (RingHom.ker ε) hb hB

end AlgebraicGeometry.Scheme
