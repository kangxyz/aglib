/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.UnitLocus
public import Aglib.AlgebraicGeometry.Surfaces.PowerNode.Blowup.NodeAtlas
public import Aglib.AlgebraicGeometry.Surfaces.PowerNode.Resolution.Regularity
public import Aglib.AlgebraicGeometry.Morphisms.IsIso.OpenRestriction

/-!
Native extraction from the R5 local-model source
`PointedResolution.Resolution.Data`.
R5 revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256:
`fd9b05361e6adc7711c0561833215776cbd56bb23d82f33f70bc7d62f7a491bb`.
Original objects, maps, quantifiers and mathematical hypotheses are retained.
Conditional blowup families remain explicit inputs.
-/

@[expose] public section

/-!
# The unit locus of an actual affine blowup and the recursive node-resolution datum with its two
  fixed outer opens.

The declarations retain their original qualified interfaces and mathematical
inputs; the source-coverage comments below retain their original boundaries.
-/

open CategoryTheory Limits AlgebraicGeometry Polynomial
open scoped Polynomial
open AlgebraicGeometry.Scheme.PowerNode
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Hom.Range AlgebraicGeometry.Scheme.Pullback.Fibre
universe u

section NodeResolutionData


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry
open PlaneNode _root_.PowerNode.Rees
open AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.Scheme.PowerNode.Resolution
variable {R : Type u} [CommRing R]
/-- The affine power-node scheme with equation `UV = π^n`. -/
abbrev X (π : R) (n : ℕ) : Scheme.{u} := Spec (.of (node π n))
/-- The principal open of the power node where the coordinate `U` is invertible. -/
def uOpen (π : R) (n : ℕ) : (X π n).Opens := PrimeSpectrum.basicOpen (PlaneNode.U (π^n))
/-- The principal open of the power node where the coordinate `V` is invertible. -/
def vOpen (π : R) (n : ℕ) : (X π n).Opens := PrimeSpectrum.basicOpen (PlaneNode.V (π^n))
/-- The principal open of the power node where the base element `π` is invertible. -/
def genericOpen (π : R) (n : ℕ) : (X π n).Opens :=
  PrimeSpectrum.basicOpen (algebraMap R (node π n) π)

/-- A constructed regular modification, with actual inverse-image isomorphisms.
This is output data: the recursion below supplies every field, rather than
postulating a universal resolution family. -/
structure Data (π : R) (n : ℕ) where
  /-- The regular source scheme of the constructed modification. -/
  Y : Scheme.{u}
  /-- The proper modification map from the regular source to the exponent-`n` node. -/
  map : Y ⟶ X π n
  proper : IsProper map
  regular : RegularStalks Y
  isoU : IsIso (map ∣_ uOpen π n)
  isoV : IsIso (map ∣_ vOpen π n)

attribute [instance] Data.proper Data.isoU Data.isoV

variable {π : R} {n : ℕ} (D : Data π n)

/-- Identify the inverse image of the `U`-invertible open with that open via the modification map.
-/
def uIso : (D.map ⁻¹ᵁ uOpen π n).toScheme ≅ (uOpen π n).toScheme :=
  asIso (D.map ∣_ uOpen π n)
/-- Identify the inverse image of the `V`-invertible open with that open via the modification map.
-/
def vIso : (D.map ⁻¹ᵁ vOpen π n).toScheme ≅ (vOpen π n).toScheme :=
  asIso (D.map ∣_ vOpen π n)
@[reassoc] lemma uIso_triangle :
    (uIso D).hom ≫ (uOpen π n).ι = (D.map ⁻¹ᵁ uOpen π n).ι ≫ D.map :=
  morphismRestrict_ι D.map (uOpen π n)
@[reassoc] lemma vIso_triangle :
    (vIso D).hom ≫ (vOpen π n).ι = (D.map ⁻¹ᵁ vOpen π n).ι ≫ D.map :=
  morphismRestrict_ι D.map (vOpen π n)

lemma genericOpen_le_uOpen (π : R) (n : ℕ) : genericOpen π n ≤ uOpen π n := by
  intro x hx
  change algebraMap R (node π n) π ∉ x.asIdeal at hx
  change PlaneNode.U (π^n) ∉ x.asIdeal
  intro hu
  apply hx
  apply x.isPrime.mem_of_pow_mem n
  rw [← map_pow, ← PlaneNode.relation]
  exact x.asIdeal.mul_mem_right _ hu

instance generic_isIso : IsIso (D.map ∣_ genericOpen π n) :=
  Scheme.Hom.isIso_restrict_of_le D.map (genericOpen_le_uOpen π n)

/-- Identify the inverse image of the `π`-invertible open with that open via the modification map.
-/
def genericIso : (D.map ⁻¹ᵁ genericOpen π n).toScheme ≅ (genericOpen π n).toScheme :=
  asIso (D.map ∣_ genericOpen π n)
@[reassoc] lemma genericIso_triangle :
    (genericIso D).hom ≫ (genericOpen π n).ι = (D.map ⁻¹ᵁ genericOpen π n).ι ≫ D.map :=
  morphismRestrict_ι D.map (genericOpen π n)

variable [IsDomain R] [IsDiscreteValuationRing R]

/-- The identity regular modification of the exponent-zero node. -/
def zero (π : R) : Data π 0 where
  Y := X π 0
  map := 𝟙 _
  proper := inferInstance
  regular := by
    have := PlaneNode.Regularity.unitNode_regular (π^0) (by simp)
    exact regularStalks_spec (node π 0)
  isoU := by rw [morphismRestrict_id]; infer_instance
  isoV := by rw [morphismRestrict_id]; infer_instance

/-- The identity regular modification of the exponent-one node for an irreducible `π`. -/
def one (π : R) (hπ : Irreducible π) : Data π 1 where
  Y := X π 1
  map := 𝟙 _
  proper := inferInstance
  regular := by
    have := PlaneNode.Regularity.uniformizerNode_regular (π^1) (by simpa only [pow_one] using hπ)
    exact regularStalks_spec (node π 1)
  isoU := by rw [morphismRestrict_id]; infer_instance
  isoV := by rw [morphismRestrict_id]; infer_instance

end AlgebraicGeometry.Scheme.PowerNode.Resolution

end
end NodeResolutionData
