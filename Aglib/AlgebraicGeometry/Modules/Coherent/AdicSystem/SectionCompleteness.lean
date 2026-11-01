/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Coherent.AdicSystem.SectionComparison
public import Aglib.AlgebraicGeometry.Modules.Coherent.AdicSystem.SectionKernels
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.QuasiAffineCoresolution

/-! # Section completeness of vector bundles on quasi-affine schemes

The original structure-module cone being limiting implies the same for every
finite locally free coefficient. The proof constructs its universally exact
finite-free co-resolution, then applies the original kernel-cone transfer.
The structure-module hypothesis is explicit: this is not an independent
construction of scalar completeness on a punctured formal neighbourhood.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules.Coherent

universe u

/-- A limiting original scalar cone controls all original vector-bundle section cones. -/
theorem idealSheafSectionCone_finiteLocallyFree_isLimit
    (X : Scheme.{u}) [X.IsQuasiAffine] (K : X.IdealSheafData)
    (hunit : IsLimit (idealSheafSectionCone X K (SheafOfModules.unit X.ringCatSheaf)))
    (M : X.Modules) [IsFiniteLocallyFree X M] :
    Nonempty (IsLimit (idealSheafSectionCone X K M)) := by
  have h := exists_universallyExact_finiteFree_coresolution X M
  obtain ⟨I, J, hI, hJ, i, d, w, hex, hmono, hbase⟩ := h
  let := hI
  let := hJ
  let := hmono
  obtain ⟨h₂⟩ := idealSheafSectionCone_finiteFree_isLimit X K I hunit
  obtain ⟨h₃⟩ := idealSheafSectionCone_finiteFree_isLimit X K J hunit
  exact ⟨idealSheafSectionCone_isLimit_of_universallyExact X K
    (ShortComplex.mk i d w) hex hbase h₂ h₃⟩

end AlgebraicGeometry.Scheme.Modules.Coherent
