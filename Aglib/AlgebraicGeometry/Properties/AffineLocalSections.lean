/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Topology.Sheaves.Stalks

/-!
# Vanishing of structure-sheaf sections by local restriction

A section of the structure sheaf of a scheme vanishes if every point has an open
neighbourhood inside its domain on which the restriction vanishes
(`AlgebraicGeometry.Scheme.eq_zero_of_local`). Since affine opens form a basis, it suffices
that the restriction vanishes on every affine open inside the domain
(`AlgebraicGeometry.Scheme.eq_zero_of_forall_affine`). No hypothesis on the scheme is used.

The current consumers are square-zero kernels on arbitrary opens
(`Aglib.AlgebraicGeometry.Modules.Invertible.SquareZero.KernelOpens`) and the Picard tangent
space (`Aglib.AlgebraicGeometry.Picard.Tangent.Generator`).
-/

@[expose] public section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme

universe u

/-- A section of the structure sheaf vanishing near every point vanishes. -/
theorem eq_zero_of_local {X : Scheme.{u}} {V : X.Opens} (s : Γ(X, V))
    (hs : ∀ x ∈ V, ∃ (W : X.Opens) (hW : W ≤ V), x ∈ W ∧
      (X.presheaf.map (homOfLE hW).op).hom s = 0) : s = 0 := by
  apply TopCat.Presheaf.section_ext X.sheaf V s 0
  intro x hx
  obtain ⟨W, hle, hxW, hz⟩ := hs x hx
  have e := TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE hle) x hxW s
  have hz' : X.presheaf.map (homOfLE hle).op s = 0 := hz
  rw [hz', map_zero] at e
  change X.presheaf.germ V x hx s = X.presheaf.germ V x hx 0
  rw [map_zero]
  exact e.symm

/-- A section of the structure sheaf vanishing on every affine open inside its domain
vanishes. -/
theorem eq_zero_of_forall_affine {X : Scheme.{u}} {V : X.Opens} (s : Γ(X, V))
    (hs : ∀ W : X.Opens, IsAffineOpen W → ∀ hW : W ≤ V,
      (X.presheaf.map (homOfLE hW).op).hom s = 0) : s = 0 := by
  apply eq_zero_of_local s
  intro x hx
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hx V.2
  exact ⟨W, hWV, hxW, hs W hW hWV⟩

end AlgebraicGeometry.Scheme
