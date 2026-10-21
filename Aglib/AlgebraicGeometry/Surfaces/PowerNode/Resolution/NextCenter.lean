/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.PlaneNode.Residue
public import Aglib.AlgebraicGeometry.Blowup.AffineCenter
public import Aglib.AlgebraicGeometry.Surfaces.PowerNode.Resolution.Data

/-!
Native extraction from the R5 local-model source
`PointedResolution.Resolution.NextCenter`.
R5 revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256:
`5ba0d341870fe9497aa90f8b37b5ead0511253595047a597f192d4eff91f5ef1`.
Only source NodeMiddleResidue19–95: actual residue origin, exact centre, structural/blowdown
  triangles and separate exponent-zero/one facts. Weierstrass second-blowup maps remain separately
  selected.
Conditional blowup families remain explicit inputs.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Polynomial
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.PowerNode
universe u

section NodeMiddleResidue


/-! The actual rational middle origin and its exact recursive centre ideal.
The exponent-zero and exponent-one recursive base cases remain separate. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Blowup IsLocalRing
open PlaneNode _root_.PowerNode.Rees
namespace AlgebraicGeometry.Scheme.PowerNode.NextCenter
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]


/-- The residue-field origin of the positive-exponent node, sending both node coordinates to zero.
-/
def origin (π : R) (hπ : Irreducible π) (m : ℕ) (hm : 0 < m) :
    Spec (.of (ResidueField R)) ⟶ Spec (.of (node π m)) :=
  Spec.map (CommRingCat.ofHom
    (PlaneNode.residueMap (π^m) (IsDiscreteValuationRing.power_residue_zero π hπ m hm)).toRingHom)

instance origin_closedImmersion (π : R) (hπ : Irreducible π) (m : ℕ) (hm : 0 < m) :
    IsClosedImmersion (origin π hπ m hm) :=
  IsClosedImmersion.spec_of_surjective _ (PlaneNode.residueMap_surjective (π^m)
    (IsDiscreteValuationRing.power_residue_zero π hπ m hm))

lemma origin_center (π : R) (hπ : Irreducible π) (m : ℕ) (hm : 0 < m) :
    (origin π hπ m hm).ker = affineCenter (node π m) (centerIdeal π m) := by
  rw [origin, ← affineCenter_kernel _
    (PlaneNode.residueMap_surjective (π^m) (IsDiscreteValuationRing.power_residue_zero π hπ m hm))]
  congr 1
  rw [← PlaneNode.residueCenter_eq_ker,
    PlaneNode.residueCenter_eq_uniformizer_span (π^m) π hπ, centerIdeal]
  congr 1
  ext z
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

@[reassoc] lemma origin_structure (π : R) (hπ : Irreducible π) (m : ℕ) (hm : 0 < m) :
    origin π hπ m hm ≫ Spec.map (CommRingCat.ofHom (algebraMap R (node π m))) =
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) := by
  rw [origin, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact (PlaneNode.residueMap (π^m) (IsDiscreteValuationRing.power_residue_zero π hπ m
    hm)).commutes r

@[reassoc] lemma origin_middleBase (π : R) (hπ : Irreducible π) (m : ℕ) (hm : 0 < m) :
    origin π hπ m hm ≫ Spec.map (CommRingCat.ofHom (middleBase π m).toRingHom) =
      origin π hπ (m + 2) (by omega) := by
  have H : (PlaneNode.residueMap (π^m) (IsDiscreteValuationRing.power_residue_zero π hπ m hm)).comp
      (middleBase π m) = PlaneNode.residueMap (π^(m + 2))
        (IsDiscreteValuationRing.power_residue_zero π hπ (m + 2) (by omega)) := by
    apply PlaneNode.hom_ext <;> simp [middleBase, PlaneNode.residueMap]
  rw [origin, origin, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact congrArg AlgHom.toRingHom H

@[reassoc] lemma origin_middleChart_blowdown (π : R) (hπ : Irreducible π)
    (m : ℕ) (hm : 0 < m) (D : OneStepBlowup.Data π m) :
    origin π hπ m hm ≫ BlowupAtlas.middleChartMap D.atlas hπ ≫ D.blowup.map =
      origin π hπ (m + 2) (by omega) := by
  rw [BlowupAtlas.middleChartMap_triangle, origin_middleBase]

/-- At original exponent 2 the middle chart is UV=1 and has no origin. -/
lemma zero_no_origin (π : R) (f : node π 0 →ₐ[R] ResidueField R)
    (hu : f (PlaneNode.U (π ^ 0)) = 0) (hv : f (PlaneNode.V (π ^ 0)) = 0) : False := by
  have h := congrArg f (PlaneNode.relation (π ^ 0))
  simp only [map_mul, hu, hv, zero_mul, pow_zero, map_one] at h
  exact zero_ne_one h

/-- The recursive exponent-one resolution is exactly the identity. -/
lemma one_map (π : R) (hπ : Irreducible π) : (Resolution.one π hπ).map = 𝟙 _ := rfl

lemma middle_zero_regular (π : R) :
    AlgebraicGeometry.Scheme.RegularStalks (Spec (.of (node π 0))) :=
  (Resolution.zero π).regular

/-- At original exponent 3 the middle UV=pi chart is already regular. -/
lemma middle_one_regular (π : R) (hπ : Irreducible π) :
    AlgebraicGeometry.Scheme.RegularStalks (Spec (.of (node π 1))) :=
  (Resolution.one π hπ).regular

end AlgebraicGeometry.Scheme.PowerNode.NextCenter

end
end NodeMiddleResidue
