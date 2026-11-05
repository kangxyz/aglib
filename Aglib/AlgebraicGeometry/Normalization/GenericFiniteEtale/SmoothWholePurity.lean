/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.SmoothLocalWholePurity

/-! # Whole normalization purity over an arbitrary normal Noetherian base

At each original normalization point, the base is localized at its actual
image. Its finite local dimension invokes the proved whole-local purity
theorem. The native normalization comparison returns etaleness to that same
original point. Source locality then proves etaleness of the entire original
normalization, without a global dimension bound or a source restriction.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery

universe u

/-- The original tame Galois normalization with its lifted section is etale
on the whole smooth target over a normal Noetherian domain. Neither locality
nor a global dimension bound on the base is required. -/
theorem etale_normalization_of_smooth_baseOpen_section
    (A : Type u) [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [IsIntegrallyClosed A]
    {X U : Scheme.{u}} (p : X ⟶ Spec (.of A)) [Smooth p] [GeometricallyConnected p]
    (s : Spec (.of A) ⟶ X) (hs : s ≫ p = 𝟙 _)
    (W : (Spec (.of A)).Opens) [Nonempty W]
    (j : U ⟶ X) [IsOpenImmersion j]
    (hj : Set.range j = p ⁻¹' (W : Set (Spec (.of A))))
    (N : ℕ) (hN : 0 < N) (hunit : IsUnit (N : A)) :
    letI : GeometricallyIntegral p := geometricallyIntegral_of_smooth_of_geometricallyConnected p
    letI : IsIntegral X := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian p
    letI : Nonempty U := section_baseOpen_nonempty p s hs W j hj
    letI : IsIntegral U := isIntegral_of_isOpenImmersion j
    ∀ (Y : FiniteEtale U) [IsIntegral Y.obj.left] [IsGalois Y], Nat.card (Aut Y) ∣ N →
      ∀ (a : Spec (.of A) ⟶ (genericMap j Y.obj.hom).normalization),
        a ≫ (genericMap j Y.obj.hom).fromNormalization = s →
          Etale (genericMap j Y.obj.hom).fromNormalization := by
  let : GeometricallyIntegral p := geometricallyIntegral_of_smooth_of_geometricallyConnected p
  let : IsIntegral X := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian p
  let : Nonempty U := section_baseOpen_nonempty p s hs W j hj
  let : IsIntegral U := isIntegral_of_isOpenImmersion j
  intro Y _ _ hcard a ha
  apply Hom.etale_of_forall_etaleAt
  intro y
  let q : PrimeSpectrum A := p ((genericMap j Y.obj.hom).fromNormalization y)
  let L := Localization.AtPrime q.asIdeal
  obtain ⟨d, hd⟩ := ENat.ne_top_iff_exists.mp
    ((IsLocalRing.maximalIdeal L).height_ne_top Ideal.IsPrime.ne_top')
  have hdim : ringKrullDim L = (d : ℕ) := by
    rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, ← hd]
    rfl
  exact etaleAt_of_baseLocalization_whole_dimension A p s hs W j hj N hN hunit
    Y hcard a ha q d hdim (smoothLocalWholePurityAtDimension d)
    ((genericMap j Y.obj.hom).fromNormalization y) rfl y rfl

end AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery
