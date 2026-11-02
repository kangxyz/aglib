/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Limits.Range
public import Aglib.AlgebraicGeometry.Modules.Invertible.RationalTrivialization


/-!
# Actual nonempty overlaps inside an integral scheme

Intersect the original open ranges and use the actual scheme-pullback point
provider. The same pullback is integral by its original open immersion.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme

/-- Two actual nonempty open immersions into an integral scheme have nonempty native overlap. -/
theorem nonempty_openOverlap {X U V : Scheme.{u}} [IsIntegral X] [Nonempty U] [Nonempty V]
    (j : U ⟶ X) (k : V ⟶ X) [IsOpenImmersion j] [IsOpenImmersion k] :
    Nonempty (pullback j k : Scheme) := by
  obtain ⟨u⟩ := ‹Nonempty U›
  obtain ⟨v⟩ := ‹Nonempty V›
  let : Nonempty j.opensRange := ⟨⟨j u, ⟨u, rfl⟩⟩⟩
  let : Nonempty k.opensRange := ⟨⟨k v, ⟨v, rfl⟩⟩⟩
  obtain ⟨⟨z, hz⟩⟩ := Modules.Invertible.RationalTrivialization.nonempty_inf X
    j.opensRange k.opensRange
  obtain ⟨a, ha⟩ := hz.1
  obtain ⟨b, hb⟩ := hz.2
  obtain ⟨w, _, _⟩ := Scheme.Pullback.exists_preimage_pullback a b (ha.trans hb.symm)
  exact ⟨w⟩

/-- The same actual nonempty pullback overlap is integral, without choosing another open model. -/
theorem integral_openOverlap {X U V : Scheme.{u}} [IsIntegral X] [Nonempty U] [Nonempty V]
    (j : U ⟶ X) (k : V ⟶ X) [IsOpenImmersion j] [IsOpenImmersion k] :
    IsIntegral (pullback j k) := by
  let _ := nonempty_openOverlap j k
  exact isIntegral_of_isOpenImmersion (pullback.fst j k ≫ j)

end AlgebraicGeometry.Scheme
