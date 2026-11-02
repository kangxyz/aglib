/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.StrictHenselization.DiscreteValuationRing
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-! # Faithful flatness of the actual pointed DVR etale colimit

At a specified closed point, the original geometric etale colimit retains a
base uniformizer. Its original base map is therefore injective; torsion-free
modules over the original DVR are flat, and locality makes this flatness
faithful. No colimit Noetherianity or generic higher-dimensional
strict-henselization regularity is assumed. A generic field-valued point does
not satisfy the local-point guard and is not covered by the DVR statements.
-/

@[expose] public noncomputable section

namespace GeometricEtaleColimit

universe u

variable (R Ω : Type u) [CommRing R] [Field Ω] [Algebra R Ω]
  [IsLocalHom (algebraMap R Ω)]

/-- Locality of the chosen point makes the original base map into the same
geometric neighborhood colimit local. No DVR hypothesis is needed. -/
theorem algebraMap_isLocalHom_of_local_point :
    IsLocalHom (algebraMap R (GeometricEtaleColimit R Ω)) := by
  constructor
  intro r hr
  apply isUnit_of_map_unit (algebraMap R Ω) r
  have h : IsUnit (residue R Ω (algebraMap R (GeometricEtaleColimit R Ω) r)) :=
    hr.map (residue R Ω).toRingHom
  rwa [AlgHom.commutes] at h

variable [IsDomain R] [IsDiscreteValuationRing R]

/-- The actual base map is injective because an original uniformizer remains
an irreducible element of the same DVR colimit. -/
theorem algebraMap_injective_of_dvr :
    Function.Injective (algebraMap R (GeometricEtaleColimit R Ω)) := by
  let := isDomain_of_dvr R Ω
  let := isDiscreteValuationRing_of_dvr R Ω
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  exact IsDiscreteValuationRing.injective_of_map_irreducible _ hπ
    (irreducible_algebraMap_of_dvr R Ω hπ)

/-- Torsion freeness over the original DVR proves flatness of its actual
pointed etale colimit, without any finiteness hypothesis on that colimit. -/
theorem flat_of_dvr : Module.Flat R (GeometricEtaleColimit R Ω) := by
  let := isDomain_of_dvr R Ω
  let : Module.IsTorsionFree R (GeometricEtaleColimit R Ω) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (algebraMap_injective_of_dvr R Ω)
  infer_instance

/-- The actual closed-point DVR strict-henselization map is faithfully flat.
Separably closedness of the point field is unnecessary for this conclusion. -/
theorem faithfullyFlat_of_dvr : Module.FaithfullyFlat R (GeometricEtaleColimit R Ω) := by
  let : Module.Flat R (GeometricEtaleColimit R Ω) := flat_of_dvr R Ω
  let : IsLocalHom (algebraMap R (GeometricEtaleColimit R Ω)) :=
    algebraMap_isLocalHom_of_local_point R Ω
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

end GeometricEtaleColimit
