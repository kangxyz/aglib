/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.Localization.LengthSurjective
public import Mathlib.RingTheory.KrullDimension.Zero
public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.Localization.Submodule

/-!
# Finite localized length at a minimal quotient prime

Extracted from `lean/R5Lab/Aglib/AlgebraicGeometry/Torus/FiniteCorrespondence/`
leaf `FibreLength.lean:25–44`
at R5 revision `f8a3314ddecffcada2ec721d26d56a937bed9690`, source SHA-256
`aa294c36910a70807375aef5e2134dd081205a9618f811625891d92fffc17581`.
The quotient is Noetherian; no Noetherian premise on the ambient ring is added.
-/

@[expose] public noncomputable section

open scoped TensorProduct
open Module (length_localization_of_surjective)

namespace Module
universe u

/-- The local quotient module has finite length at every minimal component
of a Noetherian quotient ring; the ambient ring need not be Noetherian. -/
theorem length_localized_quotient_ne_top {A : Type u} [CommRing A] (I : Ideal A)
    [IsNoetherianRing (A ⧸ I)] (q : Ideal A) [q.IsPrime]
    (hq : q ∈ I.minimalPrimes) :
    Module.length (Localization.AtPrime q) (Localization.AtPrime q ⊗[A] (A ⧸ I)) ≠ ⊤ := by
  rw [Ideal.minimalPrimes_eq_comap] at hq
  obtain ⟨Q, hQ, rfl⟩ := hq
  let : Q.IsPrime := hQ.isPrime
  let : Ring.KrullDimLE 0 (Localization.AtPrime Q) :=
    Ring.KrullDimLE.of_isLocalization Q hQ (Localization.AtPrime Q)
  let : IsArtinianRing (Localization.AtPrime Q) :=
    IsNoetherianRing.isArtinianRing_of_krullDimLE_zero
  change Module.length (Localization.AtPrime (Q.under A))
    (Localization.AtPrime (Q.under A) ⊗[A] (A ⧸ I)) ≠ ⊤
  rw [length_localization_of_surjective (A ⧸ I) Ideal.Quotient.mk_surjective Q]
  rw [(TensorProduct.AlgebraTensorModule.rid (A ⧸ I)
    (Localization.AtPrime Q) (Localization.AtPrime Q)).length_eq]
  exact Module.length_ne_top

end Module
