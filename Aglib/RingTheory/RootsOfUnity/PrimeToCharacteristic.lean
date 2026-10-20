/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.RootsOfUnity.PrimitiveCoordinates
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Roots at levels prime to the characteristic

Source: `R5Lab.Aglib.RingTheory.RootsOfUnity.PrimeToCharacteristic`,
revision `f8a3314ddecffcada2ec721d26d56a937bed9690`. Exact field, action, embedding and
explicit-data hypotheses are retained. Native objects and maps are reused.
-/

@[expose] public section

noncomputable section
namespace Field.absoluteGaloisGroup.RootsOfUnity.PrimeToCharacteristic
open Field.absoluteGaloisGroup.RootsOfUnity
open Field.absoluteGaloisGroup.RootsOfUnity.PrimitiveCoordinates
universe u
variable (K : Type u) [Field K]
theorem exists_primitiveMu_of_neZero (n : ℕ) [NeZero n] [NeZero (n : K)] :
    ∃ a : Mu K n, IsPrimitiveRoot (a.toMul : (AlgebraicClosure K)ˣ) n := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure K) n
  refine ⟨Additive.ofMul hζ.toRootsOfUnity, ?_⟩
  apply IsPrimitiveRoot.coe_units_iff.mp
  change IsPrimitiveRoot ((hζ.toRootsOfUnity : (AlgebraicClosure K)ˣ) : AlgebraicClosure K) n
  simpa only [IsPrimitiveRoot.val_toRootsOfUnity_coe] using hζ

theorem mu_card_of_neZero (n : ℕ) [NeZero n] [NeZero (n : K)] : Nat.card (Mu K n) = n := by
  obtain ⟨a, ha⟩ := exists_primitiveMu_of_neZero K n
  rw [← Nat.card_congr (rootEquivZMod K n a ha).toEquiv, Nat.card_zmod]

end Field.absoluteGaloisGroup.RootsOfUnity.PrimeToCharacteristic
