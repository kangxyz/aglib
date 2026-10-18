/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.InternalHom.Gluing

/-!
# Equality of original module arrows on covering open families

The uniqueness part of the original Hom-sheaf gluing detects equality on
arbitrary jointly surjective families of open immersions. The index universe
is independent of the scheme universe. No finiteness or quasicoherence is
needed, and an empty family detects equality on an empty scheme.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules.Nonflat

/-- Equality of original module arrows can be checked on any jointly covering
family of open immersions, with no restriction on the index universe. -/
theorem hom_ext_of_restrict_jointlySurjective
    {X : Scheme.{u}} {ι : Type v} (Y : ι → Scheme.{u}) (a : ∀ i, Y i ⟶ X)
    [∀ i, IsOpenImmersion (a i)]
    (hcover : ∀ x : X, ∃ (i : ι) (y : Y i), a i y = x)
    {M N : X.Modules} (φ ψ : M ⟶ N)
    (h : ∀ i, (restrictFunctor (a i)).map φ = (restrictFunctor (a i)).map ψ) :
    φ = ψ := by
  let t := fun i => (restrictFunctor (a i)).map φ
  have ht : InternalHom.RestrictionHomCompatible a M N t := by
    intro i j
    exact (overlapRestrictIso (a i) (a j)).hom.naturality φ
  have hφ := InternalHom.glueRestrictionHom_unique Y a hcover M N t ht φ (fun _ => rfl)
  have hψ := InternalHom.glueRestrictionHom_unique Y a hcover M N t ht ψ
    (fun i => (h i).symm)
  exact hφ.trans hψ.symm

/-- Original module arrows are equal if their restrictions agree on an open
neighbourhood of each point. -/
theorem hom_ext_of_restrict_pointwise
    {X : Scheme.{u}} {M N : X.Modules} (φ ψ : M ⟶ N)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      (restrictFunctor U.ι).map φ = (restrictFunctor U.ι).map ψ) : φ = ψ := by
  classical
  choose U hx heq using h
  apply hom_ext_of_restrict_jointlySurjective (fun x => (U x).toScheme)
    (fun x => (U x).ι) ?_ φ ψ heq
  intro x
  exact ⟨x, ⟨x, hx x⟩, rfl⟩

end AlgebraicGeometry.Scheme.Modules.Nonflat
