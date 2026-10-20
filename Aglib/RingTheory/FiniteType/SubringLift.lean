/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Data.Finset.Lattice.Basic

/-!
# Restricting lifts between generated subrings


Source: `R5Lab.Aglib.RingTheory.FiniteType.SubringLift`.
Packet SHA-256:
`8a0cb790e56a65b9b4cf89c95ab23595dfcd1fa7017508ea252393f32f66bc18`.
Actual hypotheses, universes and forward maps are retained; source identity is
separate from compilation and mathematical-adoption evidence.
-/

@[expose] public section

noncomputable section

namespace Subring
universe u
/-- Classical decidable equality on the ambient type used for generated-subring data. -/
local instance subringLiftDecidableEq (L : Type u) : DecidableEq L := Classical.decEq L
/-- Restrict a complete chart-ring lift to the original relation ring and
recover each separately prescribed rational function. -/
def closureUnionInclusion
    {L : Type u} [Field L] (data extra : Finset L) :
    Subring.closure (data : Set L) →+*
      Subring.closure ((data ∪ extra : Finset L) : Set L) :=
  Subring.inclusion (Subring.closure_mono (fun _ hx => Finset.mem_union_left _ hx))

/-- Restriction is checked over abstract subrings, so the proof does not
normalize the generated-subring lattice while checking the diagram. -/
theorem subring_lift_restrict
    {L C : Type u} [Field L] [CommRing C] (R S : Subring L) (hle : R ≤ S)
    (g : C →+* L) (lift : S →+* C) (h : g.comp lift = S.subtype) :
    g.comp (lift.comp (Subring.inclusion hle)) = R.subtype := by
  rw [← RingHom.comp_assoc, h]
  rfl

/-- A lift of an abstract subring represents each prescribed contained value. -/
theorem subring_lift_extra
    {L C : Type u} [Field L] [CommRing C] (S : Subring L) (data : Finset L)
    (hdata : ∀ t ∈ data, t ∈ S) (g : C →+* L) (lift : S →+* C)
    (h : g.comp lift = S.subtype) :
    ∀ t ∈ data, ∃ z : C, g z = t := by
  intro t ht
  exact ⟨lift ⟨t, hdata t ht⟩, RingHom.congr_fun h ⟨t, hdata t ht⟩⟩

end Subring
