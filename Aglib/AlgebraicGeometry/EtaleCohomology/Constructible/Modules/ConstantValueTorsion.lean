/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.ConstantValueAnnihilator
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.QcqsSections
public import Aglib.CategoryTheory.Sites.Torsion.AdditiveFunctor
public import Aglib.LinearAlgebra.Torsion.Finite

/-! # Internal torsion detected on a constant module value

On a nonempty qcqs scheme, the original constant value embeds into its
sections. Sequential continuity sends internal sheaf torsion to torsion of
these sections. Finite generation then supplies a positive annihilator
without a finite ring or finite underlying additive group.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

universe u r
attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

/-- Internal torsion of the original constant module sheaf implies additive
torsion of its unchanged coefficient value. -/
theorem constantModuleValue_isAddTorsion
    (R : Type r) [Ring R] (X : Scheme.{u}) [Nonempty X]
    [CompactSpace X] [QuasiSeparatedSpace X] (M : ModuleCat.{u + 1} R)
    (hM : Sheaf.IsTorsion ((moduleUnderlying R X).obj
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M))) :
    IsAddTorsion M := by
  let : CompactSpace (etaleTerminal X).left := inferInstanceAs (CompactSpace X)
  let : QuasiSeparatedSpace (etaleTerminal X).left :=
    inferInstanceAs (QuasiSeparatedSpace X)
  let H := globalSections X
  let : H.Additive := { map_add := by intro A B a b; rfl }
  let : PreservesFilteredColimitsOfSize.{u + 1, u + 1} H := {
    preserves_filtered_colimits I _ _ :=
      Continuity.qcqsSectionsPreservesFilteredColimits (I := I) (etaleTerminal X) }
  let : PreservesFilteredColimitsOfSize.{0, 0} H :=
    preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1, 0, 0} H
  have hT := hM.isAddTorsion_obj H
  let η := (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj M)).app
    (op (etaleTerminal X))
  intro m
  obtain ⟨n, hn, hz⟩ := (hT (η m)).exists_nsmul_eq_zero
  change n • η m = 0 at hz
  apply isOfFinAddOrder_iff_nsmul_eq_zero.mpr
  refine ⟨n, hn, ?_⟩
  apply constantModuleUnit_injective R X M
  change η (n • m) = η 0
  simpa only [map_nsmul, map_zero] using hz

/-- A finite-type constant module with internally torsion sheaf has a positive
annihilator over the original, possibly infinite coefficient ring. -/
theorem constantModuleValue_exists_positive_annihilator
    (R : Type r) [Ring R] (X : Scheme.{u}) [Nonempty X]
    [CompactSpace X] [QuasiSeparatedSpace X] (M : ModuleCat.{u + 1} R)
    [Module.Finite R M]
    (hM : Sheaf.IsTorsion ((moduleUnderlying R X).obj
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M))) :
    ∃ n : ℕ, 0 < n ∧ ∀ m : M, n • m = 0 :=
  Module.exists_positive_annihilator_of_isAddTorsion R M
    (constantModuleValue_isAddTorsion R X M hM)

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules
