/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.RingTheory.Flat.TorsionFree

/-!
# The actual structural scalar map into a scheme stalk

The map is the original global constant map followed by the actual stalk germ.
It agrees with the local base germ followed by the actual morphism stalk map.
Flatness of the scheme morphism makes this ring map flat and sends each base
nonzerodivisor to a stalk nonzerodivisor. No domain, field, Noetherian or
relative-dimension hypothesis is required.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.Hom

/-- The structural constants followed by the actual germ at the point. -/
def stalkScalar {R : Type u} [CommRing R] {X : Scheme.{u}}
    (π : X ⟶ Spec (.of R)) (x : X) : R →+* X.presheaf.stalk x :=
  (X.presheaf.germ ⊤ x trivial).hom.comp
    (π.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)

/-- The same actual scalar map factors through the morphism stalk map. -/
theorem stalkScalar_eq_local {R : Type u} [CommRing R] {X : Scheme.{u}}
    (π : X ⟶ Spec (.of R)) (x : X) :
    stalkScalar π x = (π.stalkMap x).hom.comp
      (((Spec (.of R)).presheaf.germ ⊤ (π x) trivial).hom.comp
        (Scheme.ΓSpecIso (.of R)).inv.hom) := by
  ext r
  exact (π.germ_stalkMap_apply ⊤ x trivial ((Scheme.ΓSpecIso (.of R)).inv r)).symm

/-- A flat structural morphism has a flat actual scalar map to every stalk. -/
theorem stalkScalar_flat {R : Type u} [CommRing R] {X : Scheme.{u}}
    (π : X ⟶ Spec (.of R)) [Flat π] (x : X) : (stalkScalar π x).Flat := by
  have hbase : ((Spec (.of R)).presheaf.germ ⊤ (π x) trivial).hom.Flat := by
    let := (Spec (.of R)).presheaf.algebra_section_stalk (U := ⊤) ⟨π x, trivial⟩
    let hU := isAffineOpen_top (Spec (.of R))
    have := hU.isLocalization_stalk ⟨π x, trivial⟩
    exact RingHom.flat_algebraMap_iff.mpr
      (IsLocalization.flat ((Spec (.of R)).presheaf.stalk (π x))
        (hU.primeIdealOf ⟨π x, trivial⟩).asIdeal.primeCompl)
  have hΓ : (Scheme.ΓSpecIso (.of R)).inv.hom.Flat :=
    RingHom.Flat.of_bijective (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv.bijective
  rw [stalkScalar_eq_local]
  exact (hΓ.comp hbase).comp (Flat.stalkMap π x)

/-- Flatness preserves each actual base nonzerodivisor in every stalk. -/
theorem stalkScalar_mem_nonZeroDivisors {R : Type u} [CommRing R] {X : Scheme.{u}}
    (π : X ⟶ Spec (.of R)) [Flat π] (x : X) {a : R}
    (ha : a ∈ nonZeroDivisors R) :
    stalkScalar π x a ∈ nonZeroDivisors (X.presheaf.stalk x) := by
  let := (stalkScalar π x).toAlgebra
  have : Module.Flat R (X.presheaf.stalk x) := stalkScalar_flat π x
  have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors
    (M := X.presheaf.stalk x) ha
  apply mem_nonZeroDivisors_iff_left.mpr
  intro b hb
  apply hreg
  simpa only [Algebra.smul_def, RingHom.algebraMap_toAlgebra, mul_zero] using hb

end AlgebraicGeometry.Scheme.Hom

/- The scalar map is shared by frozen R5 ResidueField/StalkScalars.lean
(SHA-256 d223aefd0106f3fde88e2a7c78adbf362079b2747d0169fd2aeaf727056df134)
and Stalk/FlatDVRComponentKernel.lean. The flatness/nonzerodivisor proofs were
supplied by the surface author in ScalarFlat.lean; checked there by
scalar-check-04.json, then renamed to this native lower owner. Native package
compilation is tracked separately. -/
