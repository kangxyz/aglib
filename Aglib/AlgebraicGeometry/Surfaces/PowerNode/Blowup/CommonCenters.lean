/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.AffineCenter
public import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.CriticalNeighborhood.CommonChart
public import Aglib.AlgebraicGeometry.Blowup.BaseChange
public import Aglib.RingTheory.Blowup.PowerNode.Saturated
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
Native extraction from the R5 local-model source
`PointedResolution.Blowup.CommonCenters`.
R5 revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256:
`6711e148074182b043bbe90a70ff223bd964fa9a4c623b75d51d7851246aec00`.
Original objects, maps, quantifiers and mathematical hypotheses are retained.
Conditional blowup families remain explicit inputs.
-/

@[expose] public section

open AlgebraicGeometry.Scheme

/-!
# The actual residue-point centre ideal sheaves on the common étale chart and their exact pullback
  identities.

The declarations retain their original qualified interfaces and mathematical
inputs; the source-coverage comments below retain their original boundaries.
-/

open CategoryTheory Limits AlgebraicGeometry Polynomial
open scoped Polynomial
open AlgebraicGeometry.Scheme WeierstrassCurve
universe u

section CommonChartCenterSheaves


/-!
# Actual first residue-point centres on the common etale chart

Exact ideal pullbacks become exact ideal-sheaf pullbacks by the actual affine
quotient pushout. The original centre is identified with the actual residue
point's scheme kernel, and the power-node centre with the existing (U,V,pi).
No assertion is made about a later centre.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Blowup IsLocalRing
open WeierstrassCurve.Affine.TangentNode _root_.PowerNode.Rees
namespace AlgebraicGeometry.Scheme.PowerNode.CommonChartBlowup


section Local

variable {R : Type u} [CommRing R] [IsLocalRing R]
  {W : WeierstrassCurve R} {x y : ResidueField R}
open WeierstrassCurve.CriticalNeighborhood
variable (M : WeierstrassCurve.CriticalNeighborhood W x y)

/-- The ideal sheaf of the original affine Weierstrass centre determined by `M`. -/
def originalCenterSheaf : (Scheme.WeierstrassNode.AffineScheme W).IdealSheafData :=
  affineCenter ((W.toAffine.CoordinateRing)) M.originalCenter

/-- The ideal sheaf of the residue centre on the affine node with parameter `c`. -/
def nodeCenterSheaf (c : R) : (Spec (.of (PlaneNode.Ring c))).IdealSheafData :=
  affineCenter (PlaneNode.Ring c) (PlaneNode.residueCenter c)

/-- The common centre is the literal inverse image of the original affine centre. -/
def commonCenterSheaf : M.commonScheme.IdealSheafData :=
  (originalCenterSheaf M).comap M.toOriginalScheme

lemma originalResidue_surjective (he : (W.map (IsLocalRing.residue R)).toAffine.Equation x y) :
    Function.Surjective (WeierstrassCurve.CriticalNeighborhood.originalResidue he).toRingHom := by
  intro z
  obtain ⟨r, hr⟩ := IsLocalRing.residue_surjective (R := R) z
  refine ⟨algebraMap R ((W.toAffine.CoordinateRing)) r, ?_⟩
  change WeierstrassCurve.CriticalNeighborhood.originalResidue he (algebraMap R
    ((W.toAffine.CoordinateRing)) r) = z
  simpa only [AlgHom.commutes, ResidueField.algebraMap_eq] using hr

/-- The original blowup ideal is the actual residue-point ideal sheaf. -/
lemma originalCenterSheaf_eq_point_kernel
    (he : (W.map (IsLocalRing.residue R)).toAffine.Equation x y) :
    originalCenterSheaf M =
      (Spec.map (CommRingCat.ofHom (WeierstrassCurve.CriticalNeighborhood.originalResidue
        he).toRingHom)).ker := by
  rw [originalCenterSheaf, M.originalCenter_eq_point_kernel he]
  exact affineCenter_kernel _ (originalResidue_surjective he)

/-- The node centre too is the kernel of its actual residue-point immersion. -/
lemma nodeCenterSheaf_eq_point_kernel (c : R) (hc : IsLocalRing.residue R c = 0) :
    nodeCenterSheaf c =
      (Spec.map (CommRingCat.ofHom (PlaneNode.residueMap c
        hc).toRingHom)).ker := by
  rw [nodeCenterSheaf, PlaneNode.residueCenter_eq_ker c hc]
  exact affineCenter_kernel _ (PlaneNode.residueMap_surjective c hc)

variable (c : R) (a : M.Carrierˣ)
  (ha : M.translated.a₆ = (a : M.Carrier) * algebraMap R M.Carrier c)

/-- Equality of actual ideal sheaves, including all nilpotent centre structure. -/
lemma common_center_eq :
    (nodeCenterSheaf c).comap (M.toPowerNodeScheme c a ha) = commonCenterSheaf M := by
  rw [commonCenterSheaf, originalCenterSheaf, nodeCenterSheaf,
    WeierstrassCurve.CriticalNeighborhood.toOriginalScheme,
      WeierstrassCurve.CriticalNeighborhood.toPowerNodeScheme,
    AlgebraicGeometry.Scheme.Blowup.BaseChange.affineCenter_comap,
      AlgebraicGeometry.Scheme.Blowup.BaseChange.affineCenter_comap,
    M.initial_center_pullback_eq c a ha]

end Local

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {W : WeierstrassCurve R} {x y : ResidueField R}
  (M : WeierstrassCurve.CriticalNeighborhood W x y)

lemma powerNodeCenter_eq_centerIdeal (π : R) (hπ : Irreducible π) (n : ℕ) :
    PlaneNode.residueCenter (π ^ n) = centerIdeal π n := by
  rw [PlaneNode.residueCenter_eq_uniformizer_span (π ^ n) π hπ,
    centerIdeal]
  congr 1
  ext z
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

lemma recursiveNodeCenter_eq_point_kernel (π : R) (hπ : Irreducible π) (n : ℕ)
    (hc : IsLocalRing.residue R (π ^ n) = 0) :
    affineCenter (node π n) (centerIdeal π n) =
      (Spec.map (CommRingCat.ofHom (PlaneNode.residueMap (π ^ n)
        hc).toRingHom)).ker := by
  rw [← powerNodeCenter_eq_centerIdeal π hπ n]
  exact nodeCenterSheaf_eq_point_kernel (π ^ n) hc

/-- The same common centre is the actual centre used by the original R-node recursion. -/
lemma common_node_center_eq (π : R) (hπ : Irreducible π) (n : ℕ)
    (a : M.Carrierˣ)
    (ha : M.translated.a₆ = (a : M.Carrier) * algebraMap R M.Carrier (π ^ n)) :
    (affineCenter (node π n) (centerIdeal π n)).comap
      (M.toPowerNodeScheme (π ^ n) a ha) = commonCenterSheaf M := by
  rw [← powerNodeCenter_eq_centerIdeal π hπ n]
  exact common_center_eq M (π ^ n) a ha

/-- The original affine Weierstrass chart is actually Noetherian. -/
instance original_isLocallyNoetherian :
    IsLocallyNoetherian (Scheme.WeierstrassNode.AffineScheme W) := by
  infer_instance

/-- Noetherianity of the common chart follows from its actual etale map to
the original Noetherian affine scheme. No local-ring structure is assigned. -/
instance common_isLocallyNoetherian : IsLocallyNoetherian M.commonScheme :=
  LocallyOfFiniteType.isLocallyNoetherian M.toOriginalScheme

end AlgebraicGeometry.Scheme.PowerNode.CommonChartBlowup

end
end CommonChartCenterSheaves
