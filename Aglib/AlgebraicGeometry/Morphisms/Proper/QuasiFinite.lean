/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Proper.BirationalFunctions
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-!
# The proper birational isomorphism locus at a finite fibre

A proper dominant morphism of integral schemes onto a normal target is an
isomorphism on a target neighborhood of every finite actual point fibre, when
its actual function-field map is an isomorphism. The same conclusion holds if
the morphism is quasi-finite at every point of that fibre.

The proof uses the native proper quasi-finite finiteness theorem through its
finite-fibre neighborhood corollary. The previously proved birational
structure-sheaf theorem identifies the actual section maps, and the affine
isomorphism criterion identifies the original restricted morphism. No local
Noetherianity or normality of the source is assumed.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme

universe u

private theorem isIso_restrict_of_isAffineHom_of_isIso_c
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f.c]
    (U : Y.Opens) [IsAffineHom (f ∣_ U)] : IsIso (f ∣_ U) := by
  apply (IsZariskiLocalAtTarget.iff_of_iSup_eq_top
    (P := MorphismProperty.isomorphisms Scheme)
    (fun V : U.toScheme.affineOpens => V.1) (iSup_affineOpens_eq_top _)).mpr
  intro V
  apply (isIso_morphismRestrict_iff_isIso_app (f ∣_ U) V.2).mpr
  rw [morphismRestrict_app]
  have : IsIso (f.app (U.ι ''ᵁ V.1)) :=
    NatIso.isIso_app_of_isIso f.c (op (U.ι ''ᵁ V.1))
  exact IsIso.comp_isIso' this (X.presheaf.map_isIso _)

/-- A proper dominant birational morphism of integral schemes onto a normal
target is an isomorphism over a neighborhood of every finite actual point fibre. -/
theorem exists_isIso_restrict_of_isProper_birational_of_finite_preimage_singleton
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsProper f] [IsDominant f]
    (hY : NormalStalks Y)
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap f)))
    (y : Y) (hy : (f ⁻¹' {y}).Finite) :
    ∃ U : Y.Opens, y ∈ U ∧ IsIso (f ∣_ U) := by
  obtain ⟨U, hyU, hU⟩ :=
    exists_isFinite_morphismRestrict_of_finite_preimage_singleton f y hy
  let : IsFinite (f ∣_ U) := hU
  let : IsIso f.c := isIso_c_of_isProper_birational f hY hff
  exact ⟨U, hyU, isIso_restrict_of_isAffineHom_of_isIso_c f U⟩

/-- It suffices that a proper birational morphism be quasi-finite at every
point over the given target point: its compact discrete fibre is finite. -/
theorem exists_isIso_restrict_of_isProper_birational_of_quasiFiniteAt_fibre
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsProper f] [IsDominant f]
    (hY : NormalStalks Y)
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap f)))
    (y : Y) (hy : ∀ x : X, f x = y → f.QuasiFiniteAt x) :
    ∃ U : Y.Opens, y ∈ U ∧ IsIso (f ∣_ U) := by
  apply exists_isIso_restrict_of_isProper_birational_of_finite_preimage_singleton f hY hff y
  apply (f.isCompact_preimage_singleton y).finite
  rw [isDiscrete_iff_discreteTopology, discreteTopology_iff_isOpen_singleton]
  rintro ⟨x, rfl⟩
  rw [← (f.fiberHomeo _).symm.isOpen_image, Set.image_singleton]
  exact (hy x rfl).isClopen_singleton_asFiber.isOpen

end AlgebraicGeometry.Scheme
