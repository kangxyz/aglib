/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.ShortComplex.BaseChange.Local

/-!
# Local freeness of homology and the adjacent outgoing cokernel

Once the original residue-field homology map is surjective, its outgoing
cokernel is free and the original homology is a retract of the original
opcycles. Over the local ring, homology is free exactly when those
opcycles are free. The actual homology is finite by that retraction, so
no Noetherian hypothesis or finiteness of the first term is needed.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ShortComplex

universe u v

variable {R : Type u} [CommRing R] [IsLocalRing R]
    (S : ShortComplex (ModuleCat.{max u v} R))

/-- Under surjectivity of the original residue-field mate, original homology is free
exactly when the original opcycles are free. Only the middle and final terms are finite. -/
theorem free_homology_iff_free_opcycles_of_epi_residue
    [Module.Finite R S.X₂] [Module.Finite R S.X₃] [Module.Flat R S.X₃]
    [Epi (ModuleCat.homologyBaseChangeMap
      (algebraMap R (IsLocalRing.ResidueField R)) S)] :
    Module.Free R S.homology ↔ Module.Free R S.opcycles := by
  let : Module.Free R S.X₃ := Module.free_of_flat_of_isLocalRing
  let : Module.Free R (cokernel S.g : ModuleCat.{max u v} R) :=
    S.free_cokernel_of_epi_residue_homologyBaseChangeMap
  let : Module.Finite R S.opcycles := Module.Finite.of_surjective S.pOpcycles.hom
    ((ModuleCat.epi_iff_surjective S.pOpcycles).mp inferInstance)
  obtain ⟨s, hs⟩ := Abelian.exists_generalizedInverse_of_projective_cokernel S.g
  have hs' := S.rightHomologyData.generalizedInverse_g' s hs
  change S.fromOpcycles ≫ (s ≫ S.pOpcycles) ≫ S.fromOpcycles = S.fromOpcycles at hs'
  let e : S.homology ≅ kernel S.fromOpcycles :=
    S.homologyIsKernel.conePointUniqueUpToIso (limit.isLimit _)
  let r : Retract S.homology S.opcycles := (Retract.ofIso e).trans
    (kernelRetractOfGeneralizedInverse S.fromOpcycles (s ≫ S.pOpcycles) hs')
  let : Module.Finite R S.homology := Module.Finite.of_surjective r.r.hom
    ((ModuleCat.epi_iff_surjective r.r).mp inferInstance)
  have hp := S.projective_homology_iff_projective_opcycles_of_projective_cokernel
  constructor
  · intro h
    let : Module.Free R S.homology := h
    let : Module.Projective R S.homology := Module.Projective.of_free
    have hH : Projective S.homology :=
      ModuleCat.projective_of_categoryTheory_projective S.homology
    let : Projective S.opcycles := hp.mp hH
    let : Module.Projective R S.opcycles :=
      ModuleCat.projective_of_module_projective S.opcycles
    exact Module.free_of_flat_of_isLocalRing
  · intro h
    let : Module.Free R S.opcycles := h
    let : Module.Projective R S.opcycles := Module.Projective.of_free
    have hQ : Projective S.opcycles :=
      ModuleCat.projective_of_categoryTheory_projective S.opcycles
    let : Projective S.homology := hp.mpr hQ
    let : Module.Projective R S.homology :=
      ModuleCat.projective_of_module_projective S.homology
    exact Module.free_of_flat_of_isLocalRing

end CategoryTheory.ShortComplex
