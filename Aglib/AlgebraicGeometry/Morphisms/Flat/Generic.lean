/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Flat.Generic.Integral
public import Aglib.AlgebraicGeometry.Cohomology.Proper.StructureSheaf.Coefficient

/-!
# Generic flatness of the original scheme morphism

Relative flatness of the actual structure module is equivalent to flatness
of the scheme morphism. Generic flatness for that coefficient therefore
gives a nonempty flat target open for a quasi-compact finite-type morphism
to an integral locally Noetherian scheme. Surjectivity is used explicitly
when obtaining a nonempty flat source open.
-/

@[expose] public noncomputable section


open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Relative flatness of the original structure module implies flatness
of the original morphism, through its actual stalk maps. -/
theorem flat_of_relativeFlat_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h : relativeFlat f (SheafOfModules.unit X.ringCatSheaf)) : Flat f := by
  apply Flat.of_stalkMap
  intro x
  let := (f.stalkMap x).hom.toAlgebra
  let : Subsingleton (ULift.{u} (PLift (x ∈ (⊤ : X.Opens)))) :=
    ⟨fun a b => by
      obtain ⟨⟨_⟩⟩ := a
      obtain ⟨⟨_⟩⟩ := b
      rfl⟩
  let e := (ModuleCat.restrictScalars (f.stalkMap x).hom).mapIso
    (unitStalkIso X x ≪≫ (Finsupp.uniqueLinearEquiv _ _
      (⟨⟨trivial⟩⟩ : ULift.{u} (PLift (x ∈ (⊤ : X.Opens))))).toModuleIso)
  let := h x
  exact Module.Flat.of_linearEquiv e.symm.toLinearEquiv

/-- The original structure module is relatively flat exactly when its
scheme morphism is flat. -/
theorem relativeFlat_unit_iff_flat {X Y : Scheme.{u}} (f : X ⟶ Y) :
    relativeFlat f (SheafOfModules.unit X.ringCatSheaf) ↔ Flat f :=
  ⟨flat_of_relativeFlat_unit f, fun h => by
    let := h
    exact relativeFlat_unit_of_flat f⟩

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme

open Modules

/-- Generic flatness of a quasi-compact morphism locally of finite type to
an integral locally Noetherian target, with the original restricted map. -/
theorem exists_nonempty_open_flat_of_isIntegral {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIntegral Y] [IsLocallyNoetherian Y] [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ U : Y.Opens, (U : Set Y).Nonempty ∧ Flat (f ∣_ U) := by
  obtain ⟨U, hU, hflat⟩ := exists_nonempty_open_relativeFlat_of_isIntegral f
    (SheafOfModules.unit X.ringCatSheaf) (affineLocallyFiniteType_unit X)
  exact ⟨U, hU, flat_of_relativeFlat_unit (f ∣_ U)
    (relativeFlat_of_iso _ (restrictUnitIso (f ⁻¹ᵁ U).ι).symm hflat)⟩

/-- A surjective quasi-compact finite-type morphism to an integral locally
Noetherian scheme is flat on a nonempty source open. Surjectivity ensures
that the generic flat target open has a nonempty preimage. -/
theorem exists_nonempty_source_open_flat_of_isIntegral {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIntegral Y] [IsLocallyNoetherian Y] [LocallyOfFiniteType f] [QuasiCompact f]
    [Surjective f] : ∃ W : X.Opens, Nonempty W ∧ Flat (W.ι ≫ f) := by
  obtain ⟨U, ⟨y, hy⟩, hflat⟩ := exists_nonempty_open_flat_of_isIntegral f
  obtain ⟨x, hx⟩ := f.surjective y
  refine ⟨f ⁻¹ᵁ U, ⟨⟨x, ?_⟩⟩, ?_⟩
  · change f x ∈ U
    rwa [hx]
  · rw [← morphismRestrict_ι]
    let := hflat
    infer_instance

end AlgebraicGeometry.Scheme
