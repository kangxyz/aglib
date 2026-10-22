/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.InternalHom.Gluing

/-! # Equality of original module morphisms on an open cover -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules.InternalHom
universe u v

/-- Restriction to a jointly covering open family detects equality of original
module morphisms. Neither coefficient needs to be quasicoherent. -/
theorem hom_ext_of_openCover
    {X : Scheme.{u}} {ι : Type v} (Y : ι → Scheme.{u})
    (p : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (p i)]
    (hcover : ∀ x : X, ∃ (i : ι) (y : Y i), p i y = x)
    {M N : X.Modules} (f g : M ⟶ N)
    (h : ∀ i, (restrictFunctor (p i)).map f = (restrictFunctor (p i)).map g) : f = g := by
  have hc : RestrictionHomCompatible p M N
      (fun i => (restrictFunctor (p i)).map f) := by
    intro i k
    exact (overlapRestrictIso (p i) (p k)).hom.naturality f
  obtain ⟨l, _, hl⟩ := existsUnique_restrictionHom Y p hcover M N
    (fun i => (restrictFunctor (p i)).map f) hc
  exact (hl f (fun _ => rfl)).trans (hl g (fun i => (h i).symm)).symm

end AlgebraicGeometry.Scheme.Modules.InternalHom
