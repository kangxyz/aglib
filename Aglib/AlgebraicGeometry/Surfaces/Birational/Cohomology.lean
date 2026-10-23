/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Proper.FiniteLength
public import Aglib.AlgebraicGeometry.Surfaces.Birational.IsomorphismLocus

/-!
# Finite-length cohomology of proper birational local surfaces

An actual proper birational morphism from an integral scheme to a normal
Noetherian local integral scheme of dimension at most two is an isomorphism
over the punctured spectrum. The original cohomology of every coherent module
sheaf therefore has finite length in every positive degree. In particular,
this supplies finite length of the original first cohomology for duality.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

universe u

namespace AlgebraicGeometry.Scheme

/-- A proper birational morphism to a normal Noetherian local integral
scheme of dimension at most two is an actual isomorphism over its punctured
spectrum. The original function-field map is retained. -/
theorem Hom.isIso_restrict_localPuncturedSpectrum_of_isProper_birational
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [IsDomain R]
    {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f] [IsDominant f]
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap f)))
    (hR : NormalStalks (Spec (CommRingCat.of R)))
    (hdim : topologicalKrullDim (Spec (CommRingCat.of R)) ≤ 2) :
    IsIso (f ∣_ localPuncturedSpectrum R) := by
  let U := localPuncturedSpectrum R
  let L := f.targetIsomorphismLocus
  have hUL : U ≤ L := by
    intro p hp
    have hpne : p ≠ IsLocalRing.closedPoint R := (mem_localPuncturedSpectrum R p).mp hp
    have hpnclosed : ¬IsClosed ({p} : Set (Spec (CommRingCat.of R))) := by
      intro hc
      apply hpne
      exact PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal
        ((PrimeSpectrum.isClosed_singleton_iff_isMaximal p).mp hc))
    obtain ⟨V, hpV, hV⟩ :=
      exists_isIso_restrict_of_isProper_birational_at_nonclosed_point f hff hR hdim p hpnclosed
    exact f.le_targetIsomorphismLocus V hV hpV
  let W : L.toScheme.Opens := L.ι ⁻¹ᵁ U
  have himage : L.ι ''ᵁ W = U := by
    change L.ι ''ᵁ (L.ι ⁻¹ᵁ U) = U
    rw [Hom.image_preimage_eq_opensRange_inf, Opens.opensRange_ι, inf_eq_right.mpr hUL]
  let : IsIso (f ∣_ L) := f.isIso_restrict_targetIsomorphismLocus
  have hdouble : IsIso ((f ∣_ L) ∣_ W) := inferInstance
  have hsingle : IsIso (f ∣_ L.ι ''ᵁ W) :=
    ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
      (morphismRestrictRestrict f L W)).mp hdouble
  exact ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (morphismRestrictEq f himage)).mp hsingle

namespace Cohomology

/-- Every original positive cohomology group of a coherent coefficient on a
proper birational local surface has finite length with its unchanged
structural ring action. The normal target has dimension at most two. -/
theorem moduleCohomology_isFiniteLength_of_proper_birational_surface
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [IsDomain R]
    {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f] [IsDominant f]
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap f)))
    (hR : NormalStalks (Spec (CommRingCat.of R)))
    (hdim : topologicalKrullDim (Spec (CommRingCat.of R)) ≤ 2)
    (M : X.Modules) (hM : affineLocallyFiniteType X M) (q : ℕ) (hq : 0 < q) :
    let α := f.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
    letI := moduleCohomologyModuleOfHom X α M q
    IsFiniteLength R (Sheaf.H.{u + 1} (moduleAddSheaf X M) q) :=
  moduleCohomology_isFiniteLength_of_proper_of_isIso_puncturedSpectrum R f
    (Hom.isIso_restrict_localPuncturedSpectrum_of_isProper_birational R f hff hR hdim)
    M hM q hq

/-- Finite length of the original first cohomology, for the local surface
duality consumer. -/
theorem moduleCohomology_one_isFiniteLength_of_proper_birational_surface
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [IsDomain R]
    {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f] [IsDominant f]
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap f)))
    (hR : NormalStalks (Spec (CommRingCat.of R)))
    (hdim : topologicalKrullDim (Spec (CommRingCat.of R)) ≤ 2)
    (M : X.Modules) (hM : affineLocallyFiniteType X M) :
    let α := f.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
    letI := moduleCohomologyModuleOfHom X α M 1
    IsFiniteLength R (Sheaf.H.{u + 1} (moduleAddSheaf X M) 1) :=
  moduleCohomology_isFiniteLength_of_proper_birational_surface R f hff hR hdim M hM 1
    (by decide)

end Cohomology

end AlgebraicGeometry.Scheme
