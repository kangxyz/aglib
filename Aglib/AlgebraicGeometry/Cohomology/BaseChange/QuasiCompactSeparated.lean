/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.CechComparison
/-!
# The original canonical structure-cohomology base-change theorem

Finite affine covers, exact scalar extension, and the literal comparison with
the existing tensor map prove base change for quasi-compact separated schemes
over arbitrary fields, in every degree. Proper schemes give the original
ProperStructureCohomologyBaseChange proposition without another theorem-family
or cohomology-finiteness premise.

Extraction source: `R5Lab.AlgebraicGeometry.Curves.Cohomology.ProperBaseChange` at R5Lab revision
`95a3772b895fbc19a81684be4ffd519d0fdcd6b3`; all declarations are retained.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme.OverField
namespace AlgebraicGeometry.Scheme.Cohomology
universe u
variable {F : Type u} [Field F] (K : Type u) [Field K] [Algebra F K]

/-- Positive-degree base change for the existing canonical map on any quasi-compact separated
  field scheme. -/
theorem structureCohomologyBaseChangeMap_bijective_succ_of_quasiCompact_of_isSeparated
    (X : FScheme F) [QuasiCompact X.hom] [IsSeparated X.hom] (n : ℕ) :
    Function.Bijective (structureCohomologyBaseChangeMap K X (n + 1)) := by
  classical
  let : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  obtain ⟨s, hs, he⟩ := (isCompact_iff_finite_and_eq_biUnion_affineOpens
    (X := X.left) (U := ⊤)).mp (by simpa using (isCompact_univ : IsCompact (Set.univ : Set X.left)))
  let : Fintype s := hs.fintype
  have hcover : (⨆ i : s, (i.val : X.left.Opens)) = ⊤ := by
    simpa only [iSup_subtype] using he.symm
  exact structureCohomologyBaseChangeMap_bijective_succ_of_finite_affine_cover K X
    (fun i : s => (i.val : X.left.Opens)) hcover (fun i => i.val.property) n

/-- All-degree base change for the unchanged canonical tensor map, with no finite-generation
  hypothesis. -/
theorem structureCohomologyBaseChangeMap_bijective_of_quasiCompact_of_isSeparated
    (X : FScheme F) [QuasiCompact X.hom] [IsSeparated X.hom] (n : ℕ) :
    Function.Bijective (structureCohomologyBaseChangeMap K X n) := by
  cases n with
  | zero => exact structureCohomologyBaseChangeMap_bijective_zero_of_quasiCompact_of_isSeparated K X
  | succ n => exact
    structureCohomologyBaseChangeMap_bijective_succ_of_quasiCompact_of_isSeparated K X n

/-- Proper base change for the original canonical structure-cohomology map in every degree. -/
theorem structureCohomologyBaseChangeMap_bijective_of_isProper
    (X : FScheme F) [IsProper X.hom] (n : ℕ) :
    Function.Bijective (structureCohomologyBaseChangeMap K X n) :=
  structureCohomologyBaseChangeMap_bijective_of_quasiCompact_of_isSeparated K X n

/-- The literal original proper base-change family, now proved for all fields and all scheme
  dimensions. -/
theorem properStructureCohomologyBaseChange : ProperStructureCohomologyBaseChange.{u} := by
  intro F K _ _ _ X n hX
  let : IsProper X.hom := hX
  exact structureCohomologyBaseChangeMap_bijective_of_isProper K X n

end AlgebraicGeometry.Scheme.Cohomology
