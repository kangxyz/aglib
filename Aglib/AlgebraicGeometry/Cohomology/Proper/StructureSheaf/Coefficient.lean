/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Finiteness.Coherent
public import Aglib.AlgebraicGeometry.Modules.Flat.Generators
public import Aglib.AlgebraicGeometry.Modules.Flat.Relative
public import Aglib.AlgebraicGeometry.Modules.Flat.Relative.Unit
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.FinitePresentation
public import Aglib.AlgebraicGeometry.Modules.StructureSheaf.Hom
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.RingTheory.Flat.Stability

/-!
# The structure module as a coherent relatively flat coefficient

The actual structure module `SheafOfModules.unit X.ringCatSheaf` is finitely
presented by its native free-on-one presentation, hence affine-locally of
finite type on every scheme. No Noetherianity, quasicompactness or properness
is assumed. The stalk flatness of the structure module and its relative
flatness over a flat morphism (`unit_stalk_flat`, `relativeFlat_unit_of_flat`)
live in `Modules/Flat/Relative/Unit`, which this file re-exports.

These are the coefficient inputs of the proper local criterion for the
structure sheaf. Intended owner of the finite-type statements:
`Modules/QuasiCoherent/FiniteType`.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

/-- The structure module is finitely presented by its native free-on-one presentation. -/
theorem unit_isFinitePresentation (X : Scheme.{u}) :
    (SheafOfModules.unit X.ringCatSheaf).IsFinitePresentation := by
  let M : X.Modules := SheafOfModules.free (R := X.ringCatSheaf) PUnit.{u + 1}
  let q : M.LocalGeneratorsData.{u} :=
    (SheafOfModules.free.generatingSections (R := X.ringCatSheaf)
      PUnit.{u + 1}).localGeneratorsData
  have : q.IsLocallyFreeData := inferInstanceAs
    ((SheafOfModules.free.generatingSections (R := X.ringCatSheaf)
      PUnit.{u + 1}).localGeneratorsData.IsLocallyFreeData)
  have : ∀ i, Finite (q.generators i).I := fun _ => inferInstanceAs (Finite PUnit.{u + 1})
  have hM : M.IsFinitePresentation :=
    Scheme.Cohomology.finitePresentation_of_finite_local_basis X M q
  let e : M ≅ SheafOfModules.unit X.ringCatSheaf :=
    coproductUniqueIso (fun _ : PUnit.{u + 1} => SheafOfModules.unit X.ringCatSheaf)
  exact (SheafOfModules.isFinitePresentation X.ringCatSheaf).prop_of_iso e hM

/-- The structure module is affine-locally quasicoherent of finite type on every scheme. -/
theorem affineLocallyFiniteType_unit (X : Scheme.{u}) :
    QuasiCoherent.affineLocallyFiniteType X (SheafOfModules.unit X.ringCatSheaf) := by
  have := unit_isFinitePresentation X
  exact QuasiCoherent.affineLocallyFiniteType_of_finitePresentation _


end AlgebraicGeometry.Scheme.Modules
