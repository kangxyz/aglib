/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.ShortComplex.Semicontinuity
public import Aglib.Algebra.Homology.ShortComplex.BaseChange.LocalFreeness
public import Aglib.RingTheory.Spectrum.Prime.FiberDimension.Reduced
public import Aglib.Topology.Semicontinuity

/-!
# Constant fibre cohomology over reduced local rings

Local constancy of the original residue-field homology dimension makes
the two original cokernel fibre dimensions locally constant. Over a reduced
local ring these finite cokernels are free. Hence the original homology is
free and its original homology base-change mate is invertible after every
ring map. Only a finite middle term and a finite flat final term are needed
in this local criterion; neither Noetherianity nor a bounded complex is
assumed. Reducedness is essential for the constant-dimension implication.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Module

namespace CategoryTheory.ShortComplex

universe u v

variable {R : Type u} [CommRing R] (S : ShortComplex (ModuleCat.{max u v} R))

/-- Constant original residue-field homology dimension forces local constancy of
the two original cokernel fibre dimensions. This numerical implication holds over any
commutative ring, before any homology base-change isomorphism is known. -/
theorem isLocallyConstant_finrank_fiber_opcycles_and_cokernel
    [Module.Finite R S.X₂] [Module.FinitePresentation R S.X₃] [Module.Flat R S.X₃]
    (h : IsLocallyConstant (fun p : PrimeSpectrum R =>
      finrank p.asIdeal.ResidueField
        (S.map (ModuleCat.extendScalars (algebraMap R p.asIdeal.ResidueField))).homology)) :
    IsLocallyConstant (fun p : PrimeSpectrum R =>
      finrank p.asIdeal.ResidueField (p.asIdeal.Fiber S.opcycles)) ∧
    IsLocallyConstant (fun p : PrimeSpectrum R =>
      finrank p.asIdeal.ResidueField
        (p.asIdeal.Fiber (cokernel S.g : ModuleCat.{max u v} R))) := by
  let : Module.Finite R S.opcycles := Module.Finite.of_surjective S.pOpcycles.hom
    ((ModuleCat.epi_iff_surjective S.pOpcycles).mp inferInstance)
  let : Module.Finite R (cokernel S.g : ModuleCat.{max u v} R) :=
    Module.Finite.of_surjective (cokernel.π S.g).hom
      ((ModuleCat.epi_iff_surjective (cokernel.π S.g)).mp inferInstance)
  have ho := Module.upperSemicontinuous_finrank_fiber R S.opcycles
  have hc := Module.upperSemicontinuous_finrank_fiber R
    (cokernel S.g : ModuleCat.{max u v} R)
  have he : (fun p : PrimeSpectrum R =>
      finrank p.asIdeal.ResidueField (p.asIdeal.Fiber S.opcycles) +
        finrank p.asIdeal.ResidueField
          (p.asIdeal.Fiber (cokernel S.g : ModuleCat.{max u v} R))) =
      fun p => finrank p.asIdeal.ResidueField
          (S.map (ModuleCat.extendScalars (algebraMap R p.asIdeal.ResidueField))).homology +
        finrank p.asIdeal.ResidueField (p.asIdeal.Fiber S.X₃) :=
    funext (fun p => (S.finrank_homology_residueField_baseChange p).symm)
  have hsum : IsLocallyConstant (fun p : PrimeSpectrum R =>
      finrank p.asIdeal.ResidueField (p.asIdeal.Fiber S.opcycles) +
        finrank p.asIdeal.ResidueField
          (p.asIdeal.Fiber (cokernel S.g : ModuleCat.{max u v} R))) := by
    rw [he]
    exact h.comp₂ (Module.isLocallyConstant_finrank_fiber R S.X₃) (· + ·)
  exact ⟨ho.isLocallyConstant_of_add hc hsum,
    hc.isLocallyConstant_of_add ho (by simpa only [add_comm] using hsum)⟩

/-- Over a reduced local ring, local constancy of the original residue-field homology
dimension makes both original finite cokernels free. No finite presentation of the
middle or first term is required. -/
theorem free_opcycles_and_cokernel_of_isLocallyConstant_homology
    [IsReduced R] [IsLocalRing R] [Module.Finite R S.X₂]
    [Module.Finite R S.X₃] [Module.Flat R S.X₃]
    (h : IsLocallyConstant (fun p : PrimeSpectrum R =>
      finrank p.asIdeal.ResidueField
        (S.map (ModuleCat.extendScalars (algebraMap R p.asIdeal.ResidueField))).homology)) :
    Module.Free R S.opcycles ∧ Module.Free R (cokernel S.g : ModuleCat.{max u v} R) := by
  let : Module.Free R S.X₃ := Module.free_of_flat_of_isLocalRing
  let : Module.FinitePresentation R S.X₃ := Module.finitePresentation_of_projective R S.X₃
  let : Module.Finite R S.opcycles := Module.Finite.of_surjective S.pOpcycles.hom
    ((ModuleCat.epi_iff_surjective S.pOpcycles).mp inferInstance)
  let : Module.Finite R (cokernel S.g : ModuleCat.{max u v} R) :=
    Module.Finite.of_surjective (cokernel.π S.g).hom
      ((ModuleCat.epi_iff_surjective (cokernel.π S.g)).mp inferInstance)
  obtain ⟨ho, hc⟩ := S.isLocallyConstant_finrank_fiber_opcycles_and_cokernel h
  exact ⟨Module.free_of_isLocallyConstant_finrank_fiber_of_isReduced R S.opcycles ho,
    Module.free_of_isLocallyConstant_finrank_fiber_of_isReduced R
      (cokernel S.g : ModuleCat.{max u v} R) hc⟩

/-- The original homology of a finite-middle, finite-flat-final short complex over a
reduced local ring is free when its original residue-field homology dimension is locally
constant. The first term need not be finite. -/
theorem free_homology_of_isLocallyConstant_residueField_finrank
    [IsReduced R] [IsLocalRing R] [Module.Finite R S.X₂]
    [Module.Finite R S.X₃] [Module.Flat R S.X₃]
    (h : IsLocallyConstant (fun p : PrimeSpectrum R =>
      finrank p.asIdeal.ResidueField
        (S.map (ModuleCat.extendScalars (algebraMap R p.asIdeal.ResidueField))).homology)) :
    Module.Free R S.homology := by
  obtain ⟨ho, hc⟩ := S.free_opcycles_and_cokernel_of_isLocallyConstant_homology h
  let : Module.Free R S.opcycles := ho
  let : Module.Free R (cokernel S.g : ModuleCat.{max u v} R) := hc
  let : Module.Free R S.X₃ := Module.free_of_flat_of_isLocalRing
  let : IsIso (ModuleCat.homologyBaseChangeMap
      (algebraMap R (IsLocalRing.ResidueField R)) S) :=
    ModuleCat.homologyBaseChangeMap_isIso_of_projective_cokernel _ S
  exact S.free_homology_iff_free_opcycles_of_epi_residue.mpr ho

universe w

/-- Under the reduced local constant-dimension criterion, the original homology
base-change mate is invertible after every ring map, including larger target universes. -/
theorem homologyBaseChangeMap_isIso_of_isLocallyConstant_residueField_finrank
    [IsReduced R] [IsLocalRing R] {B : Type w} [CommRing B] (σ : R →+* B)
    (S : ShortComplex (ModuleCat.{max u v w} R))
    [Module.Finite R S.X₂] [Module.Finite R S.X₃] [Module.Flat R S.X₃]
    (h : IsLocallyConstant (fun p : PrimeSpectrum R =>
      finrank p.asIdeal.ResidueField
        (S.map (ModuleCat.extendScalars (algebraMap R p.asIdeal.ResidueField))).homology)) :
    IsIso (ModuleCat.homologyBaseChangeMap.{u, max u v, w} σ S) := by
  let : Module.Free R S.X₃ := Module.free_of_flat_of_isLocalRing
  let : Module.Free R (cokernel S.g : ModuleCat.{max u v w} R) :=
    (free_opcycles_and_cokernel_of_isLocallyConstant_homology.{u, max v w} S h).2
  exact ModuleCat.homologyBaseChangeMap_isIso_of_projective_cokernel.{u, max u v, w} σ S

end CategoryTheory.ShortComplex
