/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.VariableChange
public import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.AffineComplement

/-!
# The actual affine scheme isomorphism of a variable change

Source: ordinary R5 Weierstrass.VariableChange, lines 269–290.
The Spec arrow has the original contravariant orientation over the same field.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open WeierstrassCurve.Projective
namespace WeierstrassCurve.VariableChange
universe u
variable {F : Type u} [Field F]

/-- The actual isomorphism of standard affine Weierstrass spectra. -/
def affineSpecIso (W : WeierstrassCurve F) (v : WeierstrassCurve.VariableChange F) :
    (affineOver (v • W)).left ≅ (affineOver W).left :=
  Scheme.Spec.mapIso (affineEquiv W v).toRingEquiv.toCommRingCatIso.op

lemma affineSpecIso_over (W : WeierstrassCurve F) (v : WeierstrassCurve.VariableChange F) :
    (affineSpecIso W v).hom ≫ (affineOver W).hom = (affineOver (v • W)).hom := by
  change Spec.map (CommRingCat.ofHom (affineEquiv W v).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap F (W.toAffine.CoordinateRing))) =
      Spec.map (CommRingCat.ofHom (algebraMap F ((v • W).toAffine.CoordinateRing)))
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext a
  exact (affineEquiv W v).commutes a


/-- The actual affine spectrum isomorphism over the unchanged ground field. -/
def affineOverIso (W : WeierstrassCurve F) (v : WeierstrassCurve.VariableChange F) :
    affineOver (v • W) ≅ affineOver W :=
  Over.isoMk (affineSpecIso W v) (affineSpecIso_over W v)


/-- The forward Spec arrow is exactly the contravariant native affine-ring equivalence. -/
@[simp] theorem affineSpecIso_hom (W : WeierstrassCurve F) (v : VariableChange F) :
    (affineSpecIso W v).hom =
      Spec.map (CommRingCat.ofHom (affineEquiv W v).toRingHom) := rfl

end WeierstrassCurve.VariableChange
