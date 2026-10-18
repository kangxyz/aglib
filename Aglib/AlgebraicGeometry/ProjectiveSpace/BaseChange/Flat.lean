/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.BaseChange.Cartesian
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Flatness of coefficient base change

For a flat ring map `f : R →+* S`, the coefficient base change
`ProjectiveSpace.map f ι : P_S → P_R` is flat (`flat_map`): by `isPullback_map` it is the base
change of `Spec S → Spec R` along `toSpec R ι`, and flatness is stable under base change. In
particular the projection of a field extension is flat (`flat_map_algebraMap`, an instance), so
pullback along it preserves monomorphisms and short exact sequences
(`Scheme.Modules.pullback_preservesMonomorphisms_of_flat`, `shortExact_pullback_of_flat_all`).
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.ProjectiveSpace

variable {R S : Type u} [CommRing R] [CommRing S]

/-- The coefficient base change along a flat ring map is flat. -/
theorem flat_map (f : R →+* S) (hf : f.Flat) (ι : Type u) : Flat (map f ι) := by
  have hS : Flat (Spec.map (CommRingCat.ofHom f)) := Flat.SpecMap_iff.mpr hf
  exact MorphismProperty.of_isPullback (isPullback_map f ι).flip hS

/-- The projection `P_K → P_k` of a field extension is flat. -/
instance flat_map_algebraMap (k K : Type u) [Field k] [Field K] [Algebra k K] (ι : Type u) :
    Flat (map (algebraMap k K) ι) :=
  flat_map _ (RingHom.flat_algebraMap_iff.mpr inferInstance) ι

end AlgebraicGeometry.ProjectiveSpace
