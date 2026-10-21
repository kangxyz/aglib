/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.ResidueNode
public import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.AffineComplement

/-!
Native extraction from the R5 local-model source
`PointedResolution.Weierstrass.DVRNode`.
R5 revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256:
`fe38de93b452fcb595b6def1a29f64a03b8ab2e6827928324d02c4b31c6b7fb1`.
Only the actual infinity-section/complement slice253–304. Its source hypothesis is CommRing plus
  IsLocalRing; the existing projective scheme and residue point maps are retained.
Conditional blowup families remain explicit inputs.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry IsLocalRing
universe u

section WeierstrassComplementSection


/-! The literal infinity section avoids the actual residue-node closed subscheme
and factors through its actual open complement, with both triangles proved. -/
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry IsLocalRing
namespace WeierstrassCurve.Projective
variable {R : Type u} [CommRing R] [IsLocalRing R]

omit [IsLocalRing R] in
lemma infinitySection_z_mem (W : WeierstrassCurve R) (x : Spec (.of R)) :
    coordinate W 2 ∈ (infinitySection W x).asHomogeneousIdeal := by
  change coordinate W 2 ∈ (chart W 1
    (Spec.map (CommRingCat.ofHom (infinityChartEval W)) x)).asHomogeneousIdeal
  rw [coordinate_mem_chart_iff]
  change infinityChartEval W (normalizedCoordinate W 1 2) ∈ x.asIdeal
  simp

lemma infinitySection_range_subset_nodeComplement (W : WeierstrassCurve R)
    (r s : ResidueField R) (he : (W.map (IsLocalRing.residue R)).toAffine.Equation r s) :
    Set.range (infinitySection W) ⊆ (residueNodeComplement W r s he : Set (scheme W)) := by
  rintro _ ⟨x, rfl⟩
  rw [SetLike.mem_coe, mem_residueNodeComplement]
  intro h
  have ha : residueNode W r s he ∈ (affineChart W).opensRange :=
    ⟨affineResidueNode W r s he, (residueNode_eq_affine W r s he).symm⟩
  rw [affineChart_range] at ha
  exact ha (h ▸ infinitySection_z_mem W x)

/-- The original section factored through the same actual complement. -/
def infinityComplementSection (W : WeierstrassCurve R) (r s : ResidueField R)
    (he : (W.map (IsLocalRing.residue R)).toAffine.Equation r s) :
    Spec (.of R) ⟶ (residueNodeComplement W r s he).toScheme :=
  IsOpenImmersion.lift (residueNodeComplement W r s he).ι (infinitySection W) (by
    simpa only [Scheme.Opens.range_ι] using infinitySection_range_subset_nodeComplement W r s he)

@[reassoc] lemma infinityComplementSection_ι (W : WeierstrassCurve R)
    (r s : ResidueField R) (he : (W.map (IsLocalRing.residue R)).toAffine.Equation r s) :
    infinityComplementSection W r s he ≫ (residueNodeComplement W r s he).ι = infinitySection W :=
  IsOpenImmersion.lift_fac _ _ _

@[reassoc] lemma infinityComplementSection_structure (W : WeierstrassCurve R)
    (r s : ResidueField R) (he : (W.map (IsLocalRing.residue R)).toAffine.Equation r s) :
    infinityComplementSection W r s he ≫ (residueNodeComplement W r s he).ι ≫ structureMap W = 𝟙 _
      := by
  rw [← Category.assoc, infinityComplementSection_ι, infinitySection_structure]

end WeierstrassCurve.Projective

end
end WeierstrassComplementSection
