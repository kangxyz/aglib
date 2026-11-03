/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.Birational.NormalizedPointDomination.AdaptedCharts

/-!
# Actual affine charts of the original Nagata surface spectrum

The native global-section equivalence and identity adapted-chart theorem
supply the chart hypotheses on the same spectrum. This is the one existing
block extracted from AffineBase, without normality or locality of the ring.
-/

@[expose] public noncomputable section
set_option autoImplicit false

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.NormalizedPointDomination

/-- Every actual nonempty affine chart of a Nagata domain surface spectrum
is Nagata, through its original identity-chart map. -/
theorem affineCharts_isNagata_of_nagata
    (A : CommRingCat.{u}) [IsDomain A]
    (hA : IsNagataRing.{u, 0} A) (hdA : ringKrullDim A ≤ 2) :
    ∀ V : (Spec A).affineOpens, Nonempty V.1 → IsNagataRing.{u, 0} Γ(Spec A, V.1) := by
  have hd : topologicalKrullDim (Spec A) ≤ 2 := by
    change topologicalKrullDim (PrimeSpectrum A) ≤ 2
    rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    exact hdA
  have hbase : IsNagataRing.{u, 0} Γ(Spec A, ⊤) := by
    let e : A ≃+* Γ(Spec A, ⊤) :=
      (Scheme.ΓSpecIso A).symm.commRingCatIsoToRingEquiv
    let : Algebra A Γ(Spec A, ⊤) := e.toRingHom.toAlgebra
    let : Module.Finite A Γ(Spec A, ⊤) :=
      RingHom.Finite.of_surjective e.toRingHom e.surjective
    exact hA.of_finite
  let : Nonempty (⊤ : (Spec A).Opens) :=
    ⟨⟨genericPoint (Spec A), trivial⟩⟩
  intro V hV
  let : Nonempty V.1 := hV
  exact (adaptedChart_nagata_and_dimension (𝟙 (Spec A)) ⊤ V.1 le_top
    (isAffineOpen_top _) V.2 hbase hd (FunctionField.fieldMap_isIso (𝟙 _))).1

end AlgebraicGeometry.Scheme.NormalizedPointDomination
