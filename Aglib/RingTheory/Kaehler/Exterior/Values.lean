/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Kaehler.Exterior.Map


/-!
# Original scalar-extended raw exterior values

The original raw map retains the coefficient scalar and the ordered wedge.
This applies to arbitrary ordinary differential vectors, not only generators
of a smooth presentation.
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u v w

namespace KaehlerDifferential

variable (Λ : Type w) (R : Type u) (S : Type v)
  [CommRing Λ] [CommRing R] [CommRing S]
  [Algebra Λ R] [Algebra R S] [Algebra Λ S] [IsScalarTower Λ R S]

/-- Original scalar multiples and ordered raw wedges under actual base change. -/
theorem mapExteriorBaseChange_tmul_mk (n : ℕ) (s : S)
    (v : Fin n → KaehlerDifferential Λ R) :
    mapExteriorBaseChange Λ R S n (s ⊗ₜ[R] exteriorPower.ιMulti R n v) =
      s • exteriorPower.ιMulti S n (fun i => map Λ Λ R S (v i)) := by
  rw [mapExteriorBaseChange_tmul, mapExterior_ιMulti]

/-- In particular the original differential generators retain their order and sign. -/
theorem mapExteriorBaseChange_tmul_d (n : ℕ) (s : S) (a : Fin n → R) :
    mapExteriorBaseChange Λ R S n
      (s ⊗ₜ[R] exteriorPower.ιMulti R n (fun i => D Λ R (a i))) =
      s • exteriorPower.ιMulti S n (fun i => D Λ S (algebraMap R S (a i))) := by
  refine (mapExteriorBaseChange_tmul_mk Λ R S n s (fun i => D Λ R (a i))).trans ?_
  congr 2
  funext i
  exact map_D Λ Λ R S (a i)

end KaehlerDifferential
