/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.Birational.NormalizedPointDomination.AffineBaseCharts

/-!
# Nagata stalks of actual finite-type birational surface models

Localize the same adapted affine chart at its original point. The base
spectrum chart is supplied by the existing original affine-chart theorem.
This is the one stalk-localization body extracted from BlowupChildren;
properness, locality, normality and rationality are not hypotheses.
-/

@[expose] public noncomputable section
set_option autoImplicit false

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

/-- Every actual stalk of a finite-type birational integral model over a
Nagata surface base is Nagata, using its original adapted affine chart. -/
theorem stalk_isNagataRing_of_birational_surface
    (A : Type u) [CommRing A] [IsDomain A]
    (hA : IsNagataRing.{u, 0} A) (hdA : ringKrullDim A ≤ 2)
    {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f] [IsDominant f]
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap f))) (x : X) :
    IsNagataRing.{u, 0} (X.presheaf.stalk x) := by
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ (⊤ : X.Opens) from trivial)
  let : Nonempty U := ⟨⟨x, hxU⟩⟩
  let : Nonempty (⊤ : (Spec (.of A)).Opens) :=
    ⟨⟨genericPoint (Spec (.of A)), trivial⟩⟩
  have hbase : IsNagataRing.{u, 0} Γ(Spec (.of A), ⊤) :=
    NormalizedPointDomination.affineCharts_isNagata_of_nagata (.of A) hA hdA
      ⟨⊤, isAffineOpen_top _⟩ inferInstance
  have hdim : topologicalKrullDim (Spec (.of A)) ≤ 2 := by
    change topologicalKrullDim (PrimeSpectrum A) ≤ 2
    rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    exact hdA
  have hchart : IsNagataRing.{u, 0} Γ(X, U) :=
    (NormalizedPointDomination.adaptedChart_nagata_and_dimension f ⊤ U le_top
      (isAffineOpen_top _) hU hbase hdim hff).1
  let p := (hU.primeIdealOf ⟨x, hxU⟩).asIdeal
  let : p.IsPrime := (hU.primeIdealOf ⟨x, hxU⟩).isPrime
  let : Algebra Γ(X, U) (X.presheaf.stalk x) :=
    X.presheaf.algebra_section_stalk ⟨x, hxU⟩
  let : IsLocalization.AtPrime (X.presheaf.stalk x) p := hU.isLocalization_stalk ⟨x, hxU⟩
  exact IsNagataRing.of_isLocalization p.primeCompl hchart

end AlgebraicGeometry.Scheme
