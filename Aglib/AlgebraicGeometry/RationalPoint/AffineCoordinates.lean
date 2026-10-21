/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.FundamentalGroup.Field.Basic
public import Aglib.AlgebraicGeometry.SchemeOverField

/-!
# Affine coordinates of actual algebraic-closure points

Affine Omega-points of Spec C over F are actual F-algebra homomorphisms, with exact Galois
precomposition/postcomposition compatibility. This is generic despite P16 namespace.

Source: `R5Lab.Aglib.AlgebraicGeometry.RationalPoints.AffineCoordinates`, frozen R5
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`9fca275e6ce55920aeb1241dd32d59b0ccd9904e47e0a6cc7159963baaa2f4a8`. Selected lines: [[19, 66]].
The actual objects, canonical maps, universes and stated premises are retained.
-/

@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.OverField (FScheme)
open _root_.AlgebraicGeometry.Scheme.FiniteEtale
namespace AlgebraicGeometry.Scheme.RationalPoint
universe u
section KernelCoordinates
variable (F C : Type u) [Field F] [CommRing C] [Algebra F C]

/-- The literal affine scheme over the field for a fibre coordinate algebra. -/
def algebraSpec : FScheme F := Over.mk (Spec.algebraMap F C)

/-- Actual affine scheme points correspond to field-valued algebra maps. -/
def affinePointEquiv :
    (Over.mk (FieldGalois.geometricPoint F) ⟶ algebraSpec F C) ≃
      (C →ₐ[F] AlgebraicClosure F) where
  toFun p := Spec.homEquivAlgHom ⟨p.left, Over.w p⟩
  invFun f := Over.homMk (Spec.map (CommRingCat.ofHom f.toRingHom)) (by
    change Spec.map (CommRingCat.ofHom f.toRingHom) ≫ Spec.algebraMap F C =
      Spec.algebraMap F (AlgebraicClosure F)
    rw [← Spec.map_comp]
    congr 1
    ext r
    exact f.commutes r)
  left_inv p := by
    apply Over.OverMorphism.ext
    exact congrArg Subtype.val (Spec.homEquivAlgHom.symm_apply_apply ⟨p.left, Over.w p⟩)
  right_inv f := Spec.homEquivAlgHom.apply_symm_apply f

/-- The inverse coordinate construction uses literal Spec of the field map. -/
theorem affinePointEquiv_symm_galois (g : Field.absoluteGaloisGroup F)
    (f : C →ₐ[F] AlgebraicClosure F) :
    (affinePointEquiv F C).symm (g.toAlgHom.comp f) =
      FieldGalois.pointEnd F g ≫ (affinePointEquiv F C).symm f := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (g.toAlgHom.comp f).toRingHom) =
    Spec.map (CommRingCat.ofHom g.toRingHom) ≫ Spec.map (CommRingCat.ofHom f.toRingHom)
  rw [← Spec.map_comp]
  rfl

/-- Spec precomposition becomes postcomposition on the same field coordinates. -/
theorem affinePointEquiv_galois (g : Field.absoluteGaloisGroup F)
    (p : Over.mk (FieldGalois.geometricPoint F) ⟶ algebraSpec F C) :
    affinePointEquiv F C (FieldGalois.pointEnd F g ≫ p) =
      g.toAlgHom.comp (affinePointEquiv F C p) := by
  apply (affinePointEquiv F C).symm.injective
  rw [Equiv.symm_apply_apply, affinePointEquiv_symm_galois, Equiv.symm_apply_apply]

variable {F C}
/-- Postcompose actual geometric points by the given isomorphism over the field. -/
def pointIsoEquiv {X Y : FScheme F} (i : X ≅ Y) :
    (Over.mk (FieldGalois.geometricPoint F) ⟶ X) ≃
      (Over.mk (FieldGalois.geometricPoint F) ⟶ Y) where
  toFun x := x ≫ i.hom
  invFun x := x ≫ i.inv
  left_inv x := by simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  right_inv x := by simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

end KernelCoordinates
end AlgebraicGeometry.Scheme.RationalPoint
