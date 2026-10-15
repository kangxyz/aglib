/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.ShortComplex.BaseChange.Grauert
public import Aglib.Algebra.Category.ModuleCat.FinitePresentation
public import Aglib.RingTheory.Spectrum.Prime.FiberDimension.LocallyFree

/-!
# The reduced global constant-rank criterion for original homology

For a short complex over a reduced ring, local constancy of the original
residue-field homology dimension gives projectivity of original homology
and arbitrary original homology base change. A finite source, a finitely
presented middle term, and a finite projective final term suffice. Native
cokernel finite presentation and the original two-cokernel dimension
identity supply the finite-projective criterion over the whole spectrum.
Neither locality nor Noetherianity of the base ring is assumed.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Module

namespace CategoryTheory.ShortComplex

universe u v

variable {R : Type u} [CommRing R] [IsReduced R]
    (S : ShortComplex (ModuleCat.{max u v} R))

/-- Locally constant original residue-field homology dimension makes both native
cokernels projective over the reduced base, without a locality or Noetherian premise. -/
theorem projective_opcycles_and_cokernel_of_isLocallyConstant_homology
    [Module.Finite R S.X₁] [Module.FinitePresentation R S.X₂]
    [Module.Finite R S.X₃] [Module.Projective R S.X₃]
    (h : IsLocallyConstant (fun p : PrimeSpectrum R =>
      finrank p.asIdeal.ResidueField
        (S.map (ModuleCat.extendScalars (algebraMap R p.asIdeal.ResidueField))).homology)) :
    Module.Projective R S.opcycles ∧
      Module.Projective R (cokernel S.g : ModuleCat.{max u v} R) := by
  let : Module.FinitePresentation R S.X₃ := Module.finitePresentation_of_projective R S.X₃
  let : Module.FinitePresentation R (cokernel S.f : ModuleCat.{max u v} R) :=
    ModuleCat.finitePresentation_cokernel S.f
  let : Module.FinitePresentation R S.opcycles :=
    Module.FinitePresentation.of_equiv S.opcyclesIsoCokernel.symm.toLinearEquiv
  let : Module.FinitePresentation R (cokernel S.g : ModuleCat.{max u v} R) :=
    ModuleCat.finitePresentation_cokernel S.g
  obtain ⟨ho, hc⟩ := S.isLocallyConstant_finrank_fiber_opcycles_and_cokernel h
  exact ⟨Module.projective_of_isLocallyConstant_finrank_fiber_of_isReduced R S.opcycles ho,
    Module.projective_of_isLocallyConstant_finrank_fiber_of_isReduced R
      (cokernel S.g : ModuleCat.{max u v} R) hc⟩

/-- The unchanged original homology is projective when its original fibre dimension
is locally constant over a reduced ring, under the displayed finite-presentation bounds. -/
theorem projective_homology_of_isLocallyConstant_residueField_finrank
    [Module.Finite R S.X₁] [Module.FinitePresentation R S.X₂]
    [Module.Finite R S.X₃] [Module.Projective R S.X₃]
    (h : IsLocallyConstant (fun p : PrimeSpectrum R =>
      finrank p.asIdeal.ResidueField
        (S.map (ModuleCat.extendScalars (algebraMap R p.asIdeal.ResidueField))).homology)) :
    Module.Projective R S.homology := by
  obtain ⟨ho, hc⟩ := S.projective_opcycles_and_cokernel_of_isLocallyConstant_homology h
  let : Module.Projective R S.opcycles := ho
  let : Module.Projective R (cokernel S.g : ModuleCat.{max u v} R) := hc
  let : Projective S.X₃ := ModuleCat.projective_of_categoryTheory_projective S.X₃
  let : Projective (cokernel S.g : ModuleCat.{max u v} R) :=
    ModuleCat.projective_of_categoryTheory_projective _
  have hQ : Projective S.opcycles := ModuleCat.projective_of_categoryTheory_projective _
  let : Projective S.homology :=
    S.projective_homology_iff_projective_opcycles_of_projective_cokernel.mpr hQ
  exact ModuleCat.projective_of_module_projective S.homology

universe w

/-- The same reduced global criterion makes the original homology base-change mate
invertible after every ring map, preserving independent target-ring universes. -/
theorem homologyBaseChangeMap_isIso_of_isLocallyConstant_residueField_finrank_of_isReduced
    {B : Type w} [CommRing B] (σ : R →+* B)
    (S : ShortComplex (ModuleCat.{max u v w} R))
    [Module.Finite R S.X₁] [Module.FinitePresentation R S.X₂]
    [Module.Finite R S.X₃] [Module.Projective R S.X₃]
    (h : IsLocallyConstant (fun p : PrimeSpectrum R =>
      finrank p.asIdeal.ResidueField
        (S.map (ModuleCat.extendScalars (algebraMap R p.asIdeal.ResidueField))).homology)) :
    IsIso (ModuleCat.homologyBaseChangeMap.{u, max u v, w} σ S) := by
  let : Module.Projective R (cokernel S.g : ModuleCat.{max u v w} R) :=
    (projective_opcycles_and_cokernel_of_isLocallyConstant_homology.{u, max v w} S h).2
  exact ModuleCat.homologyBaseChangeMap_isIso_of_projective_cokernel.{u, max u v, w} σ S

end CategoryTheory.ShortComplex
