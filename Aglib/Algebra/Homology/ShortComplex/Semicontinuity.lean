/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.ShortComplex.Finrank
public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Additive
public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Algebra
public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Finiteness
public import Aglib.RingTheory.Spectrum.Prime.FiberDimension
public import Aglib.RingTheory.Spectrum.Prime.FiberDimension.Flat
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Upper semicontinuity of original residue-field homology

The dimension of the homology of the original residue-field short complex
is upper semicontinuous when its middle term is finite and its third term
is finitely presented and flat. Scalar extension commutes with the actual
two cokernels. Their finite-module fibre dimensions are upper semicontinuous,
and the third-term fibre dimension is locally constant.

The ring need not be Noetherian. The residue-field homology is not replaced
by the residue fibre of the original homology. The module category uses
the common upper universe required by the native scalar adjunction.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Module Topology

namespace CategoryTheory.ShortComplex

universe u v

variable {R : Type u} [CommRing R] (S : ShortComplex (ModuleCat.{max u v} R))

private def residueFieldOpcyclesIso (p : PrimeSpectrum R) :
    (S.map (ModuleCat.extendScalars (algebraMap R p.asIdeal.ResidueField))).opcycles ≅
      ModuleCat.of p.asIdeal.ResidueField (p.asIdeal.Fiber S.opcycles) := by
  let F : ModuleCat.{max u v} R ⥤ ModuleCat.{max u v} p.asIdeal.ResidueField :=
    ModuleCat.extendScalars (algebraMap R p.asIdeal.ResidueField)
  letI : F.IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{v, u, u}
      (algebraMap R p.asIdeal.ResidueField)).isLeftAdjoint
  exact (S.map F).opcyclesIsoCokernel ≪≫ (PreservesCokernel.iso F S.f).symm ≪≫
    F.mapIso S.opcyclesIsoCokernel.symm ≪≫
    ModuleCat.extendScalarsAlgebraObjIso R p.asIdeal.ResidueField S.opcycles

/-- Native residue-field homology and the third fibre balance the two original cokernel
fibres, without requiring any flatness of the base change or the original terms. -/
theorem finrank_homology_residueField_baseChange
    [Module.Finite R S.X₂] [Module.Finite R S.X₃] (p : PrimeSpectrum R) :
    finrank p.asIdeal.ResidueField
        (S.map (ModuleCat.extendScalars (algebraMap R p.asIdeal.ResidueField))).homology +
      finrank p.asIdeal.ResidueField (p.asIdeal.Fiber S.X₃) =
    finrank p.asIdeal.ResidueField (p.asIdeal.Fiber S.opcycles) +
      finrank p.asIdeal.ResidueField
        (p.asIdeal.Fiber (cokernel S.g : ModuleCat.{max u v} R)) := by
  let K := p.asIdeal.ResidueField
  let F : ModuleCat.{max u v} R ⥤ ModuleCat.{max u v} K :=
    ModuleCat.extendScalars (algebraMap R K)
  let : F.IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{v, u, u} (algebraMap R K)).isLeftAdjoint
  let : Module.Finite K (S.map F).X₂ := by
    change Module.Finite K (F.obj S.X₂)
    exact ModuleCat.finite_extendScalars _ _
  let : Module.Finite K (S.map F).X₃ := by
    change Module.Finite K (F.obj S.X₃)
    exact ModuleCat.finite_extendScalars _ _
  have hh := (S.map F).finrank_homology_add_finrank_eq_opcycles_add_cokernel
  change finrank K (S.map F).homology + finrank K (F.obj S.X₃) =
    finrank K (S.map F).opcycles +
      finrank K (cokernel (F.map S.g) : ModuleCat.{max u v} K) at hh
  have hx : finrank K (F.obj S.X₃) = finrank K (p.asIdeal.Fiber S.X₃) :=
    (ModuleCat.extendScalarsAlgebraObjIso R K S.X₃).toLinearEquiv.finrank_eq
  have hp : finrank K (S.map F).opcycles = finrank K (p.asIdeal.Fiber S.opcycles) :=
    (residueFieldOpcyclesIso S p).toLinearEquiv.finrank_eq
  have hc : finrank K (cokernel (F.map S.g) : ModuleCat.{max u v} K) =
      finrank K (p.asIdeal.Fiber (cokernel S.g : ModuleCat.{max u v} R)) :=
    ((PreservesCokernel.iso F S.g).symm ≪≫
      ModuleCat.extendScalarsAlgebraObjIso R K (cokernel S.g)).toLinearEquiv.finrank_eq
  change finrank K (S.map F).homology + finrank K (p.asIdeal.Fiber S.X₃) = _
  simpa only [hx, hp, hc] using hh

/-- The homology dimension of the actual residue-field complex is upper semicontinuous.
Finite middle term and finitely presented flat third term suffice. -/
theorem upperSemicontinuous_finrank_homology_residueField
    [Module.Finite R S.X₂] [Module.FinitePresentation R S.X₃] [Module.Flat R S.X₃] :
    UpperSemicontinuous (fun p : PrimeSpectrum R =>
      finrank p.asIdeal.ResidueField
        (S.map (ModuleCat.extendScalars (algebraMap R p.asIdeal.ResidueField))).homology) := by
  let : Module.Finite R S.opcycles := Module.Finite.of_surjective S.pOpcycles.hom
    ((ModuleCat.epi_iff_surjective S.pOpcycles).mp inferInstance)
  let : Module.Finite R (cokernel S.g : ModuleCat.{max u v} R) :=
    Module.Finite.of_surjective (cokernel.π S.g).hom
      ((ModuleCat.epi_iff_surjective (cokernel.π S.g)).mp inferInstance)
  intro p n hn
  change finrank p.asIdeal.ResidueField
    (S.map (ModuleCat.extendScalars (algebraMap R p.asIdeal.ResidueField))).homology < n at hn
  obtain ⟨a, hpa, ha⟩ := Module.exists_basicOpen_finrank_fiber_le R S.opcycles p
  obtain ⟨b, hpb, hb⟩ := Module.exists_basicOpen_finrank_fiber_le R
    (cokernel S.g : ModuleCat.{max u v} R) p
  have hloc := Module.isLocallyConstant_finrank_fiber R S.X₃
  filter_upwards [(PrimeSpectrum.basicOpen a).isOpen.mem_nhds hpa,
    (PrimeSpectrum.basicOpen b).isOpen.mem_nhds hpb, hloc.eventually_eq p] with q hqa hqb hq
  have h₁ := ha q hqa
  have h₂ := hb q hqb
  have h₃ := finrank_homology_residueField_baseChange S p
  have h₄ := finrank_homology_residueField_baseChange S q
  omega

end CategoryTheory.ShortComplex
