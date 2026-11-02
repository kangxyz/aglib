/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.Birational.NormalizedPointDomination
public import Aglib.AlgebraicGeometry.Properties.Normal.Affine
public import Aglib.AlgebraicGeometry.Surfaces.Birational.NormalizedPointDomination.AffineBaseCharts

/-!
# Normalized-point domination over the original affine Nagata base

The native global-section equivalence and the existing identity adapted-chart
theorem supply all chart Nagata hypotheses. The existing P04 construction then
returns its unchanged actual chain and original proper birational comparison.
No regularity of the supplied model or terminal is assumed or concluded.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.NormalizedPointDomination

/-- Any supplied integral proper birational model over a normal Nagata
domain of dimension at most two is dominated by the original P04 chain,
without supplying affine-chart Nagata hypotheses separately. -/
theorem exists_domination_of_nagata_base
    (A : Type u) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    (hA : IsNagataRing.{u, 0} A) (hdA : ringKrullDim A ≤ 2)
    {Y : Scheme.{u}} [IsIntegral Y]
    (q : Y ⟶ Spec (.of A)) [IsProper q] [IsDominant q]
    (hqff : IsIso (CommRingCat.ofHom (functionFieldMap q))) :
    ∃ (T : Scheme.{u}) (beta : T ⟶ Spec (.of A)) (a : T ⟶ Y) (hT : IsIntegral T),
      letI := hT
      ∃ (hbeta : IsDominant beta) (ha : IsDominant a),
        letI := hbeta
        letI := ha
        ∃ (_ : Blowup.NormalizedPointBlowupChain beta),
          a ≫ q = beta ∧ NormalStalks T ∧ IsNoetherian T ∧ topologicalKrullDim T ≤ 2 ∧
            IsProper beta ∧ IsProper a ∧
            IsIso (CommRingCat.ofHom (functionFieldMap beta)) ∧
            IsIso (CommRingCat.ofHom (functionFieldMap a)) := by
  let : IsNoetherianRing A := hA.isNoetherianRing
  have hN : NormalStalks (Spec (.of A)) :=
    fun x => (isIntegrallyClosed_and_isDomain_stalk_Spec A x).symm
  have hd : topologicalKrullDim (Spec (.of A)) ≤ 2 := by
    change topologicalKrullDim (PrimeSpectrum A) ≤ 2
    rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    exact hdA
  have hcharts : ∀ V : (Spec (.of A)).affineOpens,
      Nonempty V.1 → IsNagataRing.{u, 0} Γ(Spec (.of A), V.1) :=
    affineCharts_isNagata_of_nagata (.of A) hA hdA
  exact exists_domination hN hcharts hd q hqff

end AlgebraicGeometry.Scheme.NormalizedPointDomination
