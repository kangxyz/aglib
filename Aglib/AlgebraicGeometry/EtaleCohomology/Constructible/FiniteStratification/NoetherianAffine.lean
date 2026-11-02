/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteStratification.AffineOpen
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteStratification.GenericProperty

/-! # Actual finite strata for affine quasi-finite morphisms over a Noetherian base

The complete Noetherian generic-property partition construction is instantiated
with finiteness of the original base-changed morphism. Its generic supplier is
the actual affine algebra construction. No non-Noetherian extension is asserted.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible

universe u

/-- An affine quasi-finite finite-type morphism over a Noetherian base
admits an actual finite constructible locally closed partition on which
the literal original base-changed structural maps are finite. -/
theorem exists_finitePartition_of_isAffineHom_of_noetherian
    {U X : Scheme.{u}} [IsNoetherian X]
    (f : U ⟶ X) [IsAffineHom f] [LocallyQuasiFinite f] [LocallyOfFiniteType f] :
    ∃ p : FiniteLocallyClosedPartition X,
      ∀ i, IsFinite (pullback.snd f (p.inclusion i)) := by
  apply exists_finitePartition_of_generic_open
    (fun {_} i => IsFinite (pullback.snd f i))
  intro Y _ _ _ i _
  let fY := pullback.snd f i
  have : IsAffineHom fY := MorphismProperty.pullback_snd f i inferInstance
  obtain ⟨S, a, ha, hS, hfinite⟩ := exists_nonempty_finite_open_of_isAffineHom fY
  exact ⟨S, a, ha, hS, (isFinite_pullback_snd_comp_iff f i a).mpr hfinite⟩

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible
