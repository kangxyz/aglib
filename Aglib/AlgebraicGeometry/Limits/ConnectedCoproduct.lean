/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.Topology.Connected.Clopen

/-! # Connected schemes mapping to coproducts

The original scheme morphism factors through one actual coproduct inclusion;
the factorization is not merely a statement about underlying point sets.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A morphism from a connected scheme to a coproduct factors through one
of its actual open-immersion inclusions. -/
theorem exists_factor_sigma_of_connected {X : Scheme.{u}} [ConnectedSpace X]
    {ι : Type u} (Y : ι → Scheme.{u}) (f : X ⟶ ∐ Y) :
    ∃ i, ∃ g : X ⟶ Y i, g ≫ Sigma.ι Y i = f := by
  obtain ⟨i, g, _, hg⟩ :=
    ((sigmaMk Y).symm.continuous.comp f.continuous).exists_lift_sigma
  have hrange : Set.range f ⊆ Set.range (Sigma.ι Y i) := by
    rintro _ ⟨x, rfl⟩
    refine ⟨g x, ?_⟩
    have h := congrArg (sigmaMk Y) (congrFun hg x)
    simpa only [Homeomorph.apply_symm_apply, Function.comp_apply, sigmaMk_mk] using h.symm
  exact ⟨i, IsOpenImmersion.lift (Sigma.ι Y i) f hrange,
    IsOpenImmersion.lift_fac _ _ _⟩

end AlgebraicGeometry.Scheme.Hom
