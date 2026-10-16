/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.AdicCompletion.Noetherian

/-!
# Finite modules over an adically complete Noetherian ring

Every finite module over a Noetherian ring complete for an ideal is complete for the induced
module filtration. For a finite algebra this is completeness for the extended ideal.

## Extraction basis

Transferred existing declarations from
`R5Lab/AlgebraicGeometry/LocalRing/FiniteComplete.lean` at revision
`79307ff88f07d34fd5c3edb859f799c55e38f290`, source SHA-256
`db6c0a91383357bf2289b3077c6664e9ae31eb82068ab5add2be5702ba24726f`, lines 15–41.
The stated hypotheses and chosen maps are retained; declarations use native mathematical
namespaces and canonical carriers. Source correspondence is separate from native Lean validation.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
open TensorProduct

namespace IsAdicComplete

variable (R : Type*) [CommRing R] [IsNoetherianRing R]
  (I : Ideal R) [IsAdicComplete I R]

/-- Every finite module over an adically complete Noetherian ring is complete. -/
theorem of_finite (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    IsAdicComplete I M := by
  have : IsHausdorff I M := IsHausdorff.of_le_jacobson I M
    (IsAdicComplete.le_jacobson_bot I)
  apply (AdicCompletion.of_bijective_iff (I := I) (M := M)).mp
  refine ⟨AdicCompletion.of_injective I M, ?_⟩
  intro z
  obtain ⟨t, rfl⟩ := AdicCompletion.ofTensorProduct_surjective_of_finite I M z
  induction t using TensorProduct.inductionOn with
  | tmul r m =>
    obtain ⟨a, rfl⟩ :=
      ((AdicCompletion.of_bijective_iff (I := I) (M := R)).mpr inferInstance).surjective r
    refine ⟨a • m, ?_⟩
    rw [AdicCompletion.ofTensorProduct_tmul]
    change AdicCompletion.of I M (a • m) =
      (algebraMap R (AdicCompletion I R) a) • AdicCompletion.of I M m
    simp
  | add x y hx hy =>
    obtain ⟨m, hm⟩ := hx
    obtain ⟨n, hn⟩ := hy
    exact ⟨m + n, by simp [hm, hn]⟩

/-- The extended ideal topology on a finite algebra is complete. -/
theorem map_algebraMap_of_finite (B : Type*) [CommRing B] [Algebra R B] [Module.Finite R B] :
    IsAdicComplete (I.map (algebraMap R B)) B := by
  have := of_finite R I B
  exact (IsAdicComplete.map_algebraMap_iff I B).mpr this

end IsAdicComplete
