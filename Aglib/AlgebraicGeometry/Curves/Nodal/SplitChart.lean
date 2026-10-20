/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EllipticCurve.Affine.TangentNode
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# A common étale chart for a Weierstrass node

The actual tangent chart maps étale to the affine Weierstrass equation and
the literal plane node. The selected residue point and both scalar-map
triangles are proved for the same maps, in every residue characteristic.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry Polynomial
open scoped Polynomial
universe u

open IsLocalRing WeierstrassCurve.Affine.TangentNode

namespace AlgebraicGeometry.Scheme.WeierstrassNode

variable {R : Type u} [CommRing R]
variable (W : WeierstrassCurve R) (h3 : W.a₃ = 0) (h4 : W.a₄ = 0)

/-- The common affine scheme, constructed from the actual equation. -/
abbrev CommonChart := Spec (.of (TangentChart W))
/-- The spectrum of the original affine Weierstrass coordinate ring. -/
abbrev AffineScheme := Spec (.of (W.toAffine.CoordinateRing))
/-- The spectrum of the plane-node ring with parameter `W.a₆`. -/
abbrev NodeScheme := Spec (.of (PlaneNode.Ring W.a₆))
/-- The common tangent chart mapped to the original affine Weierstrass scheme. -/
def toAffine : CommonChart W ⟶ AffineScheme W :=
  Spec.map (CommRingCat.ofHom (algebraMap (W.toAffine.CoordinateRing) (TangentChart W)))
/-- The plane-node algebra map to the common tangent chart, using `W.a₃ = W.a₄ = 0`. -/
def nodeChartMap : PlaneNode.Ring W.a₆ →ₐ[R] TangentChart W :=
  (IsScalarTower.toAlgHom R (TangentRing W) (TangentChart W)).comp (nodeToTangent W h3 h4)
/-- The common tangent chart mapped to the plane-node scheme using the supplied coefficient
vanishings. -/
def toNode : CommonChart W ⟶ NodeScheme W :=
  Spec.map (CommRingCat.ofHom (nodeChartMap W h3 h4).toRingHom)

/-- The common tangent chart is etale over the original affine Weierstrass scheme. -/
instance toAffine_etale : Etale (toAffine W) :=
  (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
    (RingHom.etale_algebraMap.mpr inferInstance)

lemma nodeChartMap_factor : (nodeChartMap W h3 h4).toRingHom =
    (chartEquiv W h3 h4).symm.toRingHom.comp (algebraMap (PlaneNode.Ring W.a₆) (NodeChart W)) := by
  apply RingHom.ext
  intro z
  apply (chartEquiv W h3 h4).injective
  exact (chartEquiv_node_triangle W h3 h4 z).trans (by simp)

/-- The second map is étale by the proved nonmonic presentation and the actual chart isomorphism. -/
instance toNode_etale : Etale (toNode W h3 h4) := by
  have : Etale (Spec.map (CommRingCat.ofHom
      (algebraMap (PlaneNode.Ring W.a₆) (NodeChart W)))) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
      (RingHom.etale_algebraMap.mpr inferInstance)
  let e := Scheme.Spec.mapIso (chartEquiv W h3 h4).toRingEquiv.toCommRingCatIso.op
  have he : IsIso (Spec.map (CommRingCat.ofHom (chartEquiv W h3 h4).symm.toRingHom)) := by
    change IsIso e.inv
    infer_instance
  dsimp only [toNode]
  rw [nodeChartMap_factor]
  change Etale (Spec.map ((CommRingCat.ofHom (algebraMap (PlaneNode.Ring W.a₆) (NodeChart W))) ≫
    CommRingCat.ofHom (chartEquiv W h3 h4).symm.toRingHom))
  rw [Spec.map_comp]
  infer_instance

lemma affine_structure_triangle :
    toAffine W ≫ Spec.map (CommRingCat.ofHom (algebraMap R (W.toAffine.CoordinateRing))) =
      Spec.map (CommRingCat.ofHom (algebraMap R (TangentChart W))) := by
  rw [toAffine, ← Spec.map_comp]
  congr 1
lemma node_structure_triangle :
    toNode W h3 h4 ≫ Spec.map (CommRingCat.ofHom (algebraMap R (PlaneNode.Ring W.a₆))) =
      Spec.map (CommRingCat.ofHom (algebraMap R (TangentChart W))) := by
  rw [toNode, ← Spec.map_comp]
  congr 1
  ext r
  exact (nodeChartMap W h3 h4).commutes r

section Residue

variable [IsLocalRing R] (h6 : algebraMap R (ResidueField R) W.a₆ = 0) (r : ResidueField R)
variable (hr : r ^ 2 + algebraMap R (ResidueField R) W.a₁ * r - algebraMap R (ResidueField R) W.a₂
  = 0)
variable (hs : 2 * r + algebraMap R (ResidueField R) W.a₁ ≠ 0)

/-- The residue-field point of the common chart specified by the supplied simple tangent root
`r`. -/
def residuePoint : Spec (.of (ResidueField R)) ⟶ CommonChart W :=
  Spec.map (CommRingCat.ofHom (chartResidue (K := ResidueField R) W h6 r hr hs).toRingHom)
lemma residuePoint_affine_triangle :
    residuePoint W h6 r hr hs ≫ toAffine W =
      Spec.map (CommRingCat.ofHom (affineOrigin (K := ResidueField R) W h6).toRingHom) := by
  rw [residuePoint, toAffine, ← Spec.map_comp]
  congr 1
  exact congrArg (fun f : W.toAffine.CoordinateRing →ₐ[R] ResidueField R => CommRingCat.ofHom
    f.toRingHom)
    (chartResidue_affine_triangle W h6 r hr hs)
lemma residuePoint_node_triangle :
    residuePoint W h6 r hr hs ≫ toNode W h3 h4 =
      Spec.map (CommRingCat.ofHom (nodeOrigin (K := ResidueField R) W h6).toRingHom) := by
  rw [residuePoint, toNode, ← Spec.map_comp]
  congr 1
  exact congrArg (fun f : PlaneNode.Ring W.a₆ →ₐ[R] ResidueField R => CommRingCat.ofHom f.toRingHom)
    (chartResidue_node_triangle W h6 r hr hs h3 h4)

/-- A common étale neighbourhood of the actual two residue nodes, with both
maps over Spec R and with the selected k-rational tangent point. All rings,
maps and commuting triangles are constructed above; none are supplied. -/
theorem exists_common_etale_chart (h3 : W.a₃ = 0) (h4 : W.a₄ = 0)
    (h6 : algebraMap R (ResidueField R) W.a₆ = 0) (r : ResidueField R)
    (hr : r ^ 2 + algebraMap R (ResidueField R) W.a₁ * r -
      algebraMap R (ResidueField R) W.a₂ = 0) (hb : IsUnit W.b₂) :
    ∃ (U : Scheme.{u}) (f : U ⟶ AffineScheme W) (g : U ⟶ NodeScheme W)
      (z : Spec (.of (ResidueField R)) ⟶ U),
      Etale f ∧ Etale g ∧
      f ≫ Spec.map (CommRingCat.ofHom (algebraMap R (W.toAffine.CoordinateRing))) =
        g ≫ Spec.map (CommRingCat.ofHom (algebraMap R (PlaneNode.Ring W.a₆))) ∧
      z ≫ f = Spec.map (CommRingCat.ofHom (affineOrigin (K := ResidueField R) W h6).toRingHom) ∧
      z ≫ g = Spec.map (CommRingCat.ofHom (nodeOrigin (K := ResidueField R) W h6).toRingHom) := by
  have hd := tangent_simple_of_b₂_unit W r hr hb
  exact ⟨CommonChart W, toAffine W, toNode W h3 h4, residuePoint W h6 r hr hd,
    inferInstance, inferInstance,
    (affine_structure_triangle W).trans (node_structure_triangle W h3 h4).symm,
    residuePoint_affine_triangle W h6 r hr hd,
    residuePoint_node_triangle W h3 h4 h6 r hr hd⟩
end Residue

/-- A genuine DVR node with nonzero nonunit thickness parameter is isomorphic
 to the literal uniformizer-power node. Its exponent is the actual adic value. -/
theorem node_uniformizer_power [IsDomain R] [IsDiscreteValuationRing R]
    (c π : R) (hc : c ≠ 0) (hcu : ¬ IsUnit c) (hπ : Irreducible π) :
    ∃ n : ℕ, 0 < n ∧ IsDiscreteValuationRing.addVal R c = n ∧
      Nonempty (PlaneNode.Ring c ≃ₐ[R] PlaneNode.Ring (π ^ n)) := by
  obtain ⟨n, a, ha⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc hπ
  have hn : n ≠ 0 := by
    intro hz
    rw [hz, pow_zero, mul_one] at ha
    exact hcu (ha.symm ▸ a.isUnit)
  refine ⟨n, Nat.pos_of_ne_zero hn, IsDiscreteValuationRing.addVal_def c a hπ n ha, ?_⟩
  subst c
  exact ⟨PlaneNode.unitScale (π ^ n) a⟩
end AlgebraicGeometry.Scheme.WeierstrassNode

/- Migration source: R5Lab/AlgebraicGeometry/Curves/Nodal/SplitChart.lean.
Frozen R5 packet f8a3314ddecffcada2ec721d26d56a937bed9690.
SHA-256 cbe0ba17c6043949ad0cda88aa7cfb298eb19a8d8f70adc0f00f4eefd62e8927. -/
