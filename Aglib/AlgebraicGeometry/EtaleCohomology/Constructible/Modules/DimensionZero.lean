/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.ArtinSections
public import Aglib.AlgebraicGeometry.ResidueField.Constants
public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.DegreeZero
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.FieldTheory.PurelyInseparable.Basic

/-! # Finite original module H0 in proper dimension zero

For constructible ModuleCat-valued coefficients over any commutative ring,
original degree-zero cohomology is finite over that ring on a proper
zero-dimensional scheme over a separably closed field. The argument uses the
actual Artinian scheme and its actual finite product of local components.
The original Ext universe and coefficient-ring universe remain independent.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

universe u r e

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify
  ModuleCat.Sheaf.cohomologyModule

variable (R : Type r) [CommRing R]

/-- The original module H0, with its original coefficient action, is linearly
equivalent to the original small-etale module global sections. -/
def moduleH0SectionsLinearEquiv (X : Scheme.{u})
    [HasExt.{e} (AbelianSheaf.{u, u + 1} X)] (F : ModuleSheaf R X) :
    (ModuleCat.Sheaf.cohomology.{u + 1, u, r, e} X.smallEtaleTopology R 0).obj F ≃ₗ[R]
      (moduleGlobalSections R X).obj F :=
  ModuleCat.Sheaf.degreeZeroSectionsLinearEquiv X.smallEtaleTopology R F
    (etaleTerminalIsTerminal X)

/-- Finiteness of actual Artinian sections gives finiteness of unchanged
original degree-zero module cohomology, in every original Ext universe. -/
theorem moduleH0_finite_of_isConstructible_artinian
    (X : Scheme.{u}) [IsArtinianScheme X]
    [HasExt.{e} (AbelianSheaf.{u, u + 1} X)]
    (hres : ∀ x : X, IsSepClosed (X.residueField x))
    {F : ModuleSheaf R X} (hF : IsConstructible F) :
    Module.Finite R
      ((ModuleCat.Sheaf.cohomology.{u + 1, u, r, e} X.smallEtaleTopology R 0).obj F) := by
  let := moduleGlobalSections_finite_of_isConstructible_artinian R X hres hF
  exact Module.Finite.equiv (moduleH0SectionsLinearEquiv R X F).symm

/-- Proper dimension zero over a separably closed field gives finite original
constructible module sections, without any condition on the coefficient ring. -/
theorem moduleGlobalSections_finite_of_proper_dimension_le_zero
    {k : Type u} [Field k] [IsSepClosed k]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [IsProper p]
    (hdim : topologicalKrullDim X ≤ 0)
    {F : ModuleSheaf R X} (hF : IsConstructible F) :
    Module.Finite R ((moduleGlobalSections R X).obj F) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  let : IsLocallyArtinian X := .of_topologicalKrullDim_le_zero hdim
  let : IsArtinianScheme X := {}
  apply moduleGlobalSections_finite_of_isConstructible_artinian R X _ hF
  intro x
  let := residueAlgebra X p x
  let : Module.Finite k (X.residueField x) := residue_finite X p ⟨x, isClosed_discrete _⟩
  exact Algebra.IsAlgebraic.isSepClosed (F := k) (E := X.residueField x)

/-- Genuine finite generation of the original module H0 on a proper
zero-dimensional scheme over a separably closed field. No torsion, Noetherian
coefficient ring, or finite underlying additive group is assumed. -/
theorem moduleH0_finite_of_proper_dimension_le_zero
    {k : Type u} [Field k] [IsSepClosed k]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [IsProper p]
    (hdim : topologicalKrullDim X ≤ 0)
    [HasExt.{e} (AbelianSheaf.{u, u + 1} X)]
    {F : ModuleSheaf R X} (hF : IsConstructible F) :
    Module.Finite R
      ((ModuleCat.Sheaf.cohomology.{u + 1, u, r, e} X.smallEtaleTopology R 0).obj F) := by
  let := moduleGlobalSections_finite_of_proper_dimension_le_zero R p hdim hF
  exact Module.Finite.equiv (moduleH0SectionsLinearEquiv R X F).symm

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules
