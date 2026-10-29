/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Modules.Basic
public import Aglib.Topology.Sheaves.Cohomology.SectionCycles
/-!
# Global-section cycles computing actual Zariski cohomology

These transparent Scheme views reuse the topological section-cycle construction.
This is the resolution-comparison foundation for affine acyclicity. For an
injective resolution of the actual additive sheaf, global-section cycles
surject onto `Sheaf.H`, and a positive-degree cycle is zero precisely when it
is a global-section boundary. The resulting quotient is additively equivalent
to the existing Ext cohomology. No affine vanishing theorem is assumed here.

The homological input is mathlib's `InjectiveResolution.extMk`, its surjectivity,
and its boundary criterion, at mathlib revision
`d13f23b723b8a846827a245b89c10fc7d3f11612`. This file specializes that verified
comparison to actual global sections using the constant-sheaf adjunction.

Extraction source: `R5Lab.AlgebraicGeometry.Curves.Cohomology.AffineAcyclicity` at R5Lab revision
`95a3772b895fbc19a81684be4ffd519d0fdcd6b3`; all declarations are retained.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Cohomology

universe u

variable {X : Scheme.{u}}

/-- Maps from the actual constant integer sheaf are global sections. -/
abbrev integerSheafHomEquiv (A : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    (((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ))) ⟶ A) ≃+ A.obj.obj (op ⊤) :=
  TopCat.Sheaf.Cohomology.integerSheafHomEquiv (X := X.toTopCat) A

theorem integerSheafHomEquiv_comp
    {A B : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (f : (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ)) ⟶ A) (g : A ⟶ B) :
    integerSheafHomEquiv B (f ≫ g) = g.hom.app (op ⊤) (integerSheafHomEquiv A f) :=
  TopCat.Sheaf.Cohomology.integerSheafHomEquiv_comp (X := X.toTopCat) f g

theorem integerSheafHomEquiv_symm_comp
    {A B : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (g : A ⟶ B) (s : A.obj.obj (op ⊤)) :
    (integerSheafHomEquiv A).symm s ≫ g =
      (integerSheafHomEquiv B).symm (g.hom.app (op ⊤) s) :=
  TopCat.Sheaf.Cohomology.integerSheafHomEquiv_symm_comp (X := X.toTopCat) g s

variable {A : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
  (R : InjectiveResolution A)

/-- Global sections of the `n`th object of an actual additive-sheaf resolution. -/
abbrev resolutionSections (n : ℕ) :=
  TopCat.Sheaf.Cohomology.resolutionSections (X := X.toTopCat) R n

/-- The differential on global sections of the resolution. -/
abbrev resolutionSectionDifferential (n m : ℕ) :
    resolutionSections R n →+ resolutionSections R m :=
  TopCat.Sheaf.Cohomology.resolutionSectionDifferential (X := X.toTopCat) R n m

/-- Actual global-section cycles, without introducing another cohomology object. -/
abbrev resolutionSectionCycles (n : ℕ) :=
  TopCat.Sheaf.Cohomology.resolutionSectionCycles (X := X.toTopCat) R n

/-- A cycle of global sections represents a class in the existing Ext cohomology. -/
abbrev resolutionSectionClass (n : ℕ) : resolutionSectionCycles R n →+ Sheaf.H.{u + 1} A n :=
  TopCat.Sheaf.Cohomology.resolutionSectionClass (X := X.toTopCat) R n

/-- Every actual cohomology class has a global-section cycle representative. -/
theorem resolutionSectionClass_surjective (n : ℕ) :
    Function.Surjective (resolutionSectionClass R n) :=
  TopCat.Sheaf.Cohomology.resolutionSectionClass_surjective (X := X.toTopCat) R n

/-- A positive-degree cycle is zero in actual cohomology exactly when it is
the differential of a global section in the preceding degree. -/
theorem resolutionSectionClass_eq_zero_iff (n : ℕ)
    (s : resolutionSectionCycles R (n + 1)) :
    resolutionSectionClass R (n + 1) s = 0 ↔
      ∃ t : resolutionSections R n, resolutionSectionDifferential R n (n + 1) t = s.val :=
  TopCat.Sheaf.Cohomology.resolutionSectionClass_eq_zero_iff (X := X.toTopCat) R n s

/-- Boundaries as a homomorphism into global-section cycles. -/
abbrev resolutionSectionBoundary (n : ℕ) :
    resolutionSections R n →+ resolutionSectionCycles R (n + 1) :=
  TopCat.Sheaf.Cohomology.resolutionSectionBoundary (X := X.toTopCat) R n

theorem resolutionSectionClass_ker (n : ℕ) :
    (resolutionSectionClass R (n + 1)).ker = (resolutionSectionBoundary R n).range :=
  TopCat.Sheaf.Cohomology.resolutionSectionClass_ker (X := X.toTopCat) R n

/-- Actual positive-degree Zariski cohomology is the quotient of global-section
cycles by global-section boundaries in any injective resolution. -/
abbrev resolutionSectionsCohomologyEquiv (n : ℕ) :
    resolutionSectionCycles R (n + 1) ⧸ (resolutionSectionBoundary R n).range ≃+
      Sheaf.H.{u + 1} A (n + 1) :=
  TopCat.Sheaf.Cohomology.resolutionSectionsCohomologyEquiv (X := X.toTopCat) R n

/-- The exact resolution condition still needed for an affine vanishing proof. -/
theorem subsingleton_cohomology_iff_resolution_sections_exact (n : ℕ) :
    Subsingleton (Sheaf.H.{u + 1} A (n + 1)) ↔
      ∀ s : resolutionSectionCycles R (n + 1),
        ∃ t : resolutionSections R n,
          resolutionSectionDifferential R n (n + 1) t = s.val :=
  TopCat.Sheaf.Cohomology.subsingleton_cohomology_iff_resolution_sections_exact (X := X.toTopCat)
    R n

variable {R} {B : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
  {S : InjectiveResolution B} {f : A ⟶ B}

/-- A lift of a coefficient map to resolutions acts on actual global-section cycles. -/
abbrev resolutionSectionCyclesMap (φ : InjectiveResolution.Hom R S f) (n : ℕ) :
    resolutionSectionCycles R n →+ resolutionSectionCycles S n :=
  TopCat.Sheaf.Cohomology.resolutionSectionCyclesMap (X := X.toTopCat) φ n

/-- The resolution comparison intertwines actual coefficient maps, for any lift. -/
theorem resolutionSectionClass_naturality (φ : InjectiveResolution.Hom R S f)
    (n : ℕ) (s : resolutionSectionCycles R n) :
    Sheaf.H.map f n (resolutionSectionClass R n s) =
      resolutionSectionClass S n (resolutionSectionCyclesMap φ n s) :=
  TopCat.Sheaf.Cohomology.resolutionSectionClass_naturality (X := X.toTopCat) φ n s

open AlgebraicGeometry.Scheme.OverField in
/-- The comparison uses precisely the pre-existing structural scalar action:
any resolution lift of the actual scalar sheaf map computes multiplication. -/
theorem module_resolutionSectionClass_smul {F : Type u} [Field F]
    (X : FScheme F) (M : X.left.Modules)
    (R : InjectiveResolution (moduleAddSheaf X.left M)) (a : F)
    (φ : InjectiveResolution.Hom R R (moduleScalar X M a))
    (n : ℕ) (s : resolutionSectionCycles R n) :
    a • (show moduleCohomology F X M n from resolutionSectionClass R n s) =
      resolutionSectionClass R n (resolutionSectionCyclesMap φ n s) :=
  resolutionSectionClass_naturality φ n s

end AlgebraicGeometry.Scheme.Cohomology
