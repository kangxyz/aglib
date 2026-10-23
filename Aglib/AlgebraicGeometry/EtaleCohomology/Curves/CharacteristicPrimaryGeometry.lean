/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.StructureComparison
public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.CharacteristicPrimary
public import Aglib.AlgebraicGeometry.Cohomology.Proper.Field
public import Aglib.AlgebraicGeometry.Cohomology.Vanishing.Noetherian

/-! # Characteristic-primary vanishing on arbitrary proper curves

The geometric inputs are the proved proper coherent finiteness and Noetherian
Zariski dimension vanishing, transported along the original scalar-compatible
comparison. Singular, nonreduced and disconnected proper schemes of dimension
at most one are included; the constant field need not be perfect.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry.Scheme.OverField

universe u w

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Curves

attribute [local instance] HasExt.standard hasSheafifyLarge structureCohomologyModule

variable {k : Type u} [Field k] (Y : FScheme k) [IsProper Y.hom]
  [HasExt.{w} (AbelianSheaf.{u, u + 1} Y.left)]

/-- Proper structure cohomology is finite dimensional for its actual structural action. -/
theorem etaleStructureCohomology_finite (q : ℕ) :
    FiniteDimensional k (Sheaf.H.{w} (additiveStructureSheaf Y.left) q) := by
  let : FiniteDimensional k (Scheme.structureCohomology k Y q) :=
    Cohomology.properStructureCohomologyFinite k Y q inferInstance
  exact (structureCohomologyLinearComparison Y q).finiteDimensional

/-- Dimension vanishing for the original etale structure coefficient of a proper curve. -/
theorem etaleStructureCohomology_vanishing
    (hdim : topologicalKrullDim Y.left ≤ 1) (q : ℕ) (hq : 1 < q) :
    Subsingleton (Sheaf.H.{w} (additiveStructureSheaf Y.left) q) := by
  let : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  let : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  let : IsNoetherian Y.left := ⟨⟩
  let : Subsingleton (Sheaf.H.{u + 1} (Scheme.structureAddSheaf Y.left) q) :=
    Cohomology.noetherianSheafCohomology_vanishing Y.left
      (Scheme.structureAddSheaf Y.left) 1 q hdim hq
  exact (structureCohomologyComparison Y.left q).symm.injective.subsingleton

/-- All characteristic-primary cyclic coefficients vanish above degree one
on every proper curve over a separably closed field. -/
theorem characteristicPrimary_vanishing [IsSepClosed k]
    (hdim : topologicalKrullDim Y.left ≤ 1)
    (p : ℕ) [Fact p.Prime] [CharP k p] (m r : ℕ) :
    Subsingleton (Sheaf.H.{w}
      (ConstantFinite.coefficient (ULift.{u} (ZMod (p ^ r))) Y.left) (m + 2)) := by
  let := etaleStructureCohomology_finite Y 1
  exact characteristicPrimary_vanishing_of_structure_cohomology Y p
    (etaleStructureCohomology_vanishing Y hdim) m r

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves
