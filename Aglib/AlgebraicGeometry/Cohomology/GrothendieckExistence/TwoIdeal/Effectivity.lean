/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.TwoIdeal.RecoveryMap
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.TwoIdeal.CoefficientBounds
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.BoundedCoherentReconstruction

/-! # Two-ideal effectivity from bounded comparison and actual closed effectivity

The bounded K-adic coherent candidate is constructed by global reconstruction,
not supplied as an extra hypothesis. The remaining inputs are the original
bounded comparison and actual effectivity on the closed K-power thickenings.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Coherent
namespace AlgebraicGeometry.Scheme.Cohomology
universe u
variable {A : Type u} [CommRing A] [IsNoetherianRing A]
  (I : Ideal A) [IsAdicComplete I A] {X : Scheme.{u}} [IsLocallyNoetherian X]
  (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f] (K : X.IdealSheafData)
  (h : ClosedThickeningCompletionEssSurj f I K)
  (F : AdicSystem X (idealThickeningIdealSheaf f I)) {H : X.CoherentSheaf}
local notation "J" => idealThickeningIdealSheaf f I
include h

/-- Bounded comparison and actual closed-thickening effectivity reconstruct
an original I-algebraization retaining its target map and a uniform defect bound. -/
theorem exists_twoIdealAlgebraization
    (φ : F ⟶ (completionFunctor X J).obj H) (t : ℕ)
    (hφ : AdicSystem.DefectsKilled K t φ) :
    ∃ (G : X.CoherentSheaf) (a : G ⟶ H)
      (e : (completionFunctor X J).obj G ≅ F),
      e.hom ≫ φ = (completionFunctor X J).map a ∧
        killedByIdealSheaf (K ^ (t * 2)) (kernel a.hom) ∧
          killedByIdealSheaf (K ^ (t * 2)) (cokernel a.hom) := by
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  obtain ⟨G, a, β, hβ, hk, hc⟩ := exists_boundedCoherentReconstruction
    (twoIdealCoefficientMap I f K h F φ) (t * 2)
    (twoIdealCoefficientMap_defectsKilled I f K h F φ t hφ)
  refine ⟨G, a, twoIdealRecoveryIso I f K h F φ t hφ a β hβ (t * 2) hk hc, ?_, hk, hc⟩
  exact twoIdealRecoveryIso_map I f K h F φ t hφ a β hβ (t * 2) hk hc

/-- The original formal object is effective under the two mathematical inputs
used in proper ideal induction, with no bounded-candidate oracle. -/
theorem twoIdeal_mem_essImage
    (φ : F ⟶ (completionFunctor X J).obj H) (t : ℕ)
    (hφ : AdicSystem.DefectsKilled K t φ) :
    (completionFunctor X J).essImage F := by
  obtain ⟨G, _, e, _⟩ := exists_twoIdealAlgebraization I f K h F φ t hφ
  exact ⟨G, ⟨e⟩⟩

end AlgebraicGeometry.Scheme.Cohomology
