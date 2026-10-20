/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.PlaneNode.CoordinateTransport
public import Mathlib.AlgebraicGeometry.Limits

/-!
# The actual coefficient base change of a literal node scheme

The original tensor equivalence identifies the literal scheme pullback,
including both actual projection maps. Pure node-ring transport is owned by
`Aglib.RingTheory.PlaneNode.CoordinateTransport` below schemes.
Source: scheme part of
`R5Lab.AlgebraicGeometry.Curves.LocalModels.PointedResolution.Nodal.CoordinateTransport`.
R5 packet revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256:
`1653a07650513593b903cc7b5db4793870399c969bebf70aa4ca0c159c759984`.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct
universe u
namespace AlgebraicGeometry.Scheme.PowerNode
variable {R : Type u} [CommRing R] (S : Type u) [CommRing S] [Algebra R S]

/-- The affine-scheme isomorphism identifying the node with transported coefficient with the
base change of the original node. -/
def baseChangeIso (c : R) : Spec (.of (PlaneNode.Ring (algebraMap R S c))) ≅
    pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (Spec.map (CommRingCat.ofHom (algebraMap R (PlaneNode.Ring c)))) :=
  Scheme.Spec.mapIso (PlaneNode.tensorEquiv S c).toRingEquiv.toCommRingCatIso.op ≪≫
    (pullbackSpecIso R S (PlaneNode.Ring c)).symm

@[reassoc] theorem baseChangeIso_hom_fst (c : R) :
    (baseChangeIso S c).hom ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (algebraMap S (PlaneNode.Ring (algebraMap R S c)))) := by
  simp only [baseChangeIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    pullbackSpecIso_inv_fst]
  change Spec.map (CommRingCat.ofHom (PlaneNode.tensorEquiv S c).toRingHom) ≫
    Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) = _
  rw [← Spec.map_comp]
  congr 1
  ext s
  exact (PlaneNode.tensorEquiv S c).commutes s

@[reassoc] theorem baseChangeIso_hom_snd (c : R) :
    (baseChangeIso S c).hom ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (PlaneNode.coefficientMap S c).toRingHom) := by
  simp only [baseChangeIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    pullbackSpecIso_inv_snd]
  change Spec.map (CommRingCat.ofHom (PlaneNode.tensorEquiv S c).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
      PlaneNode.Ring c →ₐ[R] S ⊗[R] PlaneNode.Ring c).toRingHom) = _
  rw [← Spec.map_comp]
  rfl


end AlgebraicGeometry.Scheme.PowerNode
