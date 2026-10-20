/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Stalk.FlatDVR.ComponentKernel
public import Aglib.RingTheory.Ideal.HeightOne
public import Aglib.AlgebraicGeometry.Stalk.CodimensionOne
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.Properties
public import Aglib.AlgebraicGeometry.Properties.Normal.Basic

/-!
# Codimension one and DVR stalks at actual generic points of vertical integral components.

Source: `R5Lab.Aglib.AlgebraicGeometry.Stalk.FlatDVRComponent`.
R5 packet revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256: `68baa37d53862870a617ee5631c25576c9fcf7b8a6a0732a693d21d48b749d17`.
Actual objects, maps, universes and hypotheses are retained.
Native declaration ownership replaces the source application namespaces.
-/

@[expose] public section

open _root_.AlgebraicGeometry.Scheme (NormalStalks)

/-!
# Codimension one and DVR stalks at actual generic points of vertical integral components.

The declarations retain their original qualified interfaces and mathematical
inputs; the source-coverage comments below retain their original boundaries.
-/

open CategoryTheory Limits AlgebraicGeometry Polynomial
open scoped Polynomial
universe u

section FibreComponentGenericDVR


/-!
# The actual generic point of a vertical integral component

The supplied flat-DVR component-kernel family gives the minimal
prime over the actual uniformizer ideal. Closed-immersion stalk surjectivity
onto the component's generic field identifies that kernel with the maximal
ideal; the principal ideal theorem then gives height one. The existing normal
codimension-one stalk theorem gives its DVR structure. No new theorem family,
component inventory, numerical count, or supplied codimension-one condition.
-/
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.Scheme.FlatDVR
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {X C : Scheme.{u}} [IsLocallyNoetherian X] [hXintegral : IsIntegral X] [IsIntegral C]
  (π : X ⟶ Spec (.of R)) [Flat π]
  (i : C ⟶ pullback π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))
  [IsClosedImmersion i]
  (hi : Set.range i ∈ irreducibleComponents
    (pullback π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) : Scheme.{u}))

include hi hXintegral

omit hXintegral in
-- Retain integrality of the total space in the flat-DVR component interface; this dimension
-- calculation is supplied by the stated local fibre-component kernel input.
/-- The dimension-one stalk is the actual image of the component's generic point. -/
@[nolint unusedArguments]
theorem componentGeneric_stalk_dimension_one [IsIntegral X]
    (H : FlatDVRFibreComponentKernel.{u}) :
    ringKrullDim (X.presheaf.stalk
      ((i ≫ pullback.fst π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))
        (genericPoint C))) = 1 := by
  let j := i ≫ pullback.fst π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) :=
    IsClosedImmersion.spec_of_surjective _ IsLocalRing.residue_surjective
  have : IsClosedImmersion j := by dsimp [j]; infer_instance
  let : Field (C.presheaf.stalk (genericPoint C)) := inferInstance
  have hk : RingHom.ker (j.stalkMap (genericPoint C)).hom =
      IsLocalRing.maximalIdeal (X.presheaf.stalk (j (genericPoint C))) :=
    IsLocalRing.ker_eq_maximalIdeal _ (j.stalkMap_surjective _)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨hnzd, hmin⟩ := H R X C π i ϖ inferInstance inferInstance hi hϖ (genericPoint C)
  have hh := Ideal.minimalPrime_height_one hnzd hmin
  change (RingHom.ker (j.stalkMap (genericPoint C)).hom).height = 1 at hh
  rw [hk] at hh
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
  exact_mod_cast hh

/-- Canonical codimension-one point, constructed rather than supplied. -/
def componentGenericCodimensionOne (H : FlatDVRFibreComponentKernel.{u}) :
    Scheme.CodimensionOnePoint X :=
  ⟨(i ≫ pullback.fst π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))
      (genericPoint C), componentGeneric_stalk_dimension_one π i hi H⟩

/-- Normality gives the actual DVR stalk at that derived point. -/
theorem componentGeneric_stalk_dvr (H : FlatDVRFibreComponentKernel.{u})
    (hN : NormalStalks X) :
    IsDiscreteValuationRing (X.presheaf.stalk
      ((i ≫ pullback.fst π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))
        (genericPoint C))) := by
  let : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x) := fun x => (hN x).2
  exact (componentGenericCodimensionOne π i hi H).localRing_isDiscreteValuationRing

end AlgebraicGeometry.Scheme.FlatDVR

end
end FibreComponentGenericDVR
