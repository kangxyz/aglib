/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Finiteness.Coherent
public import Aglib.AlgebraicGeometry.Cohomology.Finiteness.ProperInputs
/-!
# Structure-sheaf consequences of the explicit standard coherent-finiteness input

Every theorem retains `hstandard : ProperModuleCohomologyFinite` as an explicit
parameter. This is the user-accepted classical proper/coherent finiteness input
on the actual module cohomology objects and their structural field actions.
This file does not prove that standard input or introduce a Lean axiom for it.

The actual structure module is finitely presented by its native free-on-one
presentation. The scalar-compatible `structureModuleCohomologyEquiv` then
transfers the supplied all-module finiteness to actual structure cohomology in
all degrees, including H1, for arbitrary proper schemes over arbitrary fields.

Input owners: `Properties`, `Modules`, and `GeneralProperties`;
Lean 4.34.1, Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

Extraction source: `R5Lab.AlgebraicGeometry.Curves.Cohomology.StandardCoherentFiniteness` at
  R5Lab revision
`95a3772b895fbc19a81684be4ffd519d0fdcd6b3`; all declarations are retained.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.OverField
namespace AlgebraicGeometry.Scheme.Cohomology
universe u

/-- Structure-sheaf specialization of the explicit standard coherent-finiteness input. -/
theorem properStructureCohomologyFinite_of_standard
    (hstandard : ProperModuleCohomologyFinite.{u}) : ProperStructureCohomologyFinite.{u} := by
  intro k hk X n hX
  have hO : (SheafOfModules.unit X.left.ringCatSheaf).IsFinitePresentation := by
    let M : X.left.Modules := SheafOfModules.free (R := X.left.ringCatSheaf) PUnit.{u + 1}
    let q : M.LocalGeneratorsData.{u} :=
      (SheafOfModules.free.generatingSections (R := X.left.ringCatSheaf)
        PUnit.{u + 1}).localGeneratorsData
    have : q.IsLocallyFreeData := inferInstanceAs
      ((SheafOfModules.free.generatingSections (R := X.left.ringCatSheaf)
        PUnit.{u + 1}).localGeneratorsData.IsLocallyFreeData)
    have : ∀ i, Finite (q.generators i).I := fun _ => inferInstanceAs (Finite PUnit.{u + 1})
    have hM : M.IsFinitePresentation := finitePresentation_of_finite_local_basis X.left M q
    let e : M ≅ SheafOfModules.unit X.left.ringCatSheaf :=
      coproductUniqueIso (fun _ : PUnit.{u + 1} => SheafOfModules.unit X.left.ringCatSheaf)
    exact (SheafOfModules.isFinitePresentation X.left.ringCatSheaf).prop_of_iso e hM
  have := hstandard k X (SheafOfModules.unit X.left.ringCatSheaf) n hX hO
  exact (structureModuleCohomologyEquiv X n).finiteDimensional

theorem structureCohomology_finite_of_standard
    (hstandard : ProperModuleCohomologyFinite.{u}) {k : Type u} [Field k]
    (X : FScheme k) (hX : IsProper X.hom) (n : ℕ) :
    Module.Finite k (structureCohomology k X n) :=
  properStructureCohomologyFinite_of_standard hstandard k X n hX

theorem structureH1_finite_of_standard
    (hstandard : ProperModuleCohomologyFinite.{u}) {k : Type u} [Field k]
    (X : FScheme k) (hX : IsProper X.hom) :
    Module.Finite k (structureCohomology k X 1) :=
  structureCohomology_finite_of_standard hstandard X hX 1

end AlgebraicGeometry.Scheme.Cohomology
