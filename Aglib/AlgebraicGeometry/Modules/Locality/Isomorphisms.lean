/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.Support
/-! # Checking actual module-sheaf isomorphisms on open covers -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

/-- A map of actual scheme-module sheaves is an isomorphism exactly when
all its underlying abelian-group stalk maps are isomorphisms. -/
theorem moduleSheaf_isIso_iff_stalks {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N) :
    IsIso f ↔ ∀ x, IsIso ((Scheme.Modules.stalkFunctor X x).map f) := by
  constructor
  · intro h x
    exact (Scheme.Modules.stalkFunctor X x).map_isIso f
  · intro h
    have : IsIso ((SheafOfModules.toSheaf.{u} X.ringCatSheaf).map f) :=
      (TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso _).mpr h
    have : IsIso ((Scheme.Modules.toPresheaf X).map f) :=
      (TopCat.Sheaf.forget _ _).map_isIso ((SheafOfModules.toSheaf.{u} X.ringCatSheaf).map f)
    exact isIso_of_reflects_iso f (Scheme.Modules.toPresheaf X)

/-- An open restriction is an isomorphism if its stalk maps are isomorphisms
at every point in that open. -/
theorem moduleSheaf_isIso_restrict_of_stalks {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] {M N : X.Modules} (f : M ⟶ N)
    (h : ∀ x : U, IsIso ((Scheme.Modules.stalkFunctor X (j x)).map f)) :
    IsIso ((Scheme.Modules.restrictFunctor j).map f) := by
  apply (moduleSheaf_isIso_iff_stalks _).mpr
  intro x
  exact (NatIso.isIso_map_iff (Scheme.Modules.restrictStalkNatIso j x) f).mpr (h x)

/-- Isomorphism on a family of open charts covering the selected open proves
isomorphism on its actual restriction. No finiteness hypothesis is needed. -/
theorem moduleSheaf_isIso_restrict_of_openCover
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    {ι : Type v} (Y : ι → Scheme.{u}) (a : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (a i)]
    (hcover : ∀ x : U, ∃ (i : ι) (y : Y i), a i y = j x)
    {M N : X.Modules} (f : M ⟶ N)
    (hf : ∀ i, IsIso ((Scheme.Modules.restrictFunctor (a i)).map f)) :
    IsIso ((Scheme.Modules.restrictFunctor j).map f) := by
  apply moduleSheaf_isIso_restrict_of_stalks j f
  intro x
  obtain ⟨i, y, hy⟩ := hcover x
  rw [← hy]
  have := hf i
  exact (NatIso.isIso_map_iff (Scheme.Modules.restrictStalkNatIso (a i) y) f).mp
    (inferInstanceAs (IsIso ((Scheme.Modules.stalkFunctor (Y i) y).map
      ((Scheme.Modules.restrictFunctor (a i)).map f))))

end AlgebraicGeometry.Scheme.Modules
