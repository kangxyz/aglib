/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Affine coordinates for literal tensor base change

Relocated declarations with native names from R5 revision
`e6d63abca2403f50b6b413101ad7f6a7f2e0e2c7`; explicit
source and hypothesis boundaries are retained.
-/

@[expose] public section




universe u

section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.AffineBaseChange
variable (R : Type u) [CommRing R] (X : Over (Spec (.of R))) [IsAffine X.left]

/-- The canonical scalar action on the actual affine coordinate algebra. -/
abbrev coordinateAlgebra : Algebra R Γ(X.left, ⊤) :=
  (((Scheme.ΓSpecIso (.of R)).inv ≫ X.hom.appTop).hom).toAlgebra
attribute [local instance] coordinateAlgebra

/-- The affine comparison retains the literal morphism to Spec R. -/
@[reassoc] theorem isoSpec_inv_over :
    X.left.isoSpec.inv ≫ X.hom = Spec.map (CommRingCat.ofHom (algebraMap R Γ(X.left, ⊤))) := by
  change X.left.isoSpec.inv ≫ X.hom = Spec.map ((Scheme.ΓSpecIso (.of R)).inv ≫ X.hom.appTop)
  rw [← Scheme.isoSpec_inv_naturality, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]

/-- Flatness is proved for the actual global-section algebra and this scalar
map, rather than assumed for a replacement affine presentation. -/
theorem coordinate_flat [Flat X.hom] : Module.Flat R Γ(X.left, ⊤) := by
  have h : Flat (X.left.isoSpec.inv ≫ X.hom) := inferInstance
  rw [isoSpec_inv_over] at h
  exact RingHom.flat_algebraMap_iff.mp (Flat.SpecMap_iff.mp h)

variable (S : Type u) [CommRing S] [Algebra R S]

/-- The literal tensor-product spectrum is the actual affine base change. -/
def tensorSpecIso : Spec (.of (Γ(X.left, ⊤) ⊗[R] S)) ≅
    pullback (Spec.map (CommRingCat.ofHom (algebraMap R S))) X.hom :=
  (pullbackSpecIso R Γ(X.left, ⊤) S).symm ≪≫
    pullbackSymmetry _ _ ≪≫
      asIso (pullback.map _ _ _ _ (𝟙 _) X.left.isoSpec.inv (𝟙 _)
        (by simp) (by simpa only [Category.comp_id] using (isoSpec_inv_over R X).symm))

/-- The first projection is the actual right tensor-factor inclusion. -/
@[reassoc] theorem tensorSpecIso_hom_fst :
    (tensorSpecIso R X S).hom ≫
      pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R S))) X.hom =
        Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight : S →ₐ[R] Γ(X.left, ⊤) ⊗[R] S).toRingHom) := by
  simp only [tensorSpecIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    asIso_hom, pullback.map, pullback.lift_fst, Category.comp_id,
    pullbackSymmetry_hom_comp_fst, pullbackSpecIso_inv_snd]
  rfl

/-- The second projection retains the original affine source through its
canonical comparison, with the actual left tensor-factor inclusion. -/
@[reassoc] theorem tensorSpecIso_hom_snd :
    (tensorSpecIso R X S).hom ≫
      pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R S))) X.hom =
        Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeLeft : Γ(X.left, ⊤) →ₐ[R] Γ(X.left, ⊤) ⊗[R] S).toRingHom) ≫
            X.left.isoSpec.inv := by
  simp only [tensorSpecIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    asIso_hom, pullback.map, pullback.lift_snd,
    pullbackSymmetry_hom_comp_snd_assoc, pullbackSpecIso_inv_fst_assoc]
  rfl

end AlgebraicGeometry.Scheme.AffineBaseChange

end -- original noncomputable section
end

section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.AffineBaseChange
variable (R : Type u) [CommRing R] (X : Over (Spec (.of R))) [IsAffine X.left]
attribute [local instance] coordinateAlgebra
variable {S T : Type u} [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]

/-- The actual base change of a morphism of affine R-schemes. -/
def tensorPullbackMap (φ : S →ₐ[R] T) :
    pullback (Spec.map (CommRingCat.ofHom (algebraMap R T))) X.hom ⟶
      pullback (Spec.map (CommRingCat.ofHom (algebraMap R S))) X.hom :=
  pullback.lift
    (pullback.fst _ _ ≫ Spec.map (CommRingCat.ofHom φ.toRingHom))
    (pullback.snd _ _) (by
      rw [Category.assoc, ← Spec.map_comp]
      convert pullback.condition using 2
      congr 1
      apply CommRingCat.hom_ext
      exact φ.comp_algebraMap)

/-- The coordinate tensor comparison is natural for the literal map of the
right factor. Both tensor factors, including the original affine source,
are retained by this scheme equality. -/
@[reassoc] theorem tensorSpecIso_naturality (φ : S →ₐ[R] T) :
    Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.map (AlgHom.id R Γ(X.left, ⊤)) φ).toRingHom) ≫
        (tensorSpecIso R X S).hom =
      (tensorSpecIso R X T).hom ≫ tensorPullbackMap R X φ := by
  apply pullback.hom_ext
  · simp only [Category.assoc, tensorSpecIso_hom_fst, tensorPullbackMap,
      pullback.lift_fst, tensorSpecIso_hom_fst_assoc]
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
  · simp only [Category.assoc, tensorSpecIso_hom_snd, tensorPullbackMap,
      pullback.lift_snd]
    rw [← Category.assoc, ← Spec.map_comp]
    congr 1
    congr 1
    apply CommRingCat.hom_ext
    ext x
    simp

/-- The same naturality with the tensor comparisons inverted. -/
@[reassoc] theorem tensorSpecIso_inv_naturality (φ : S →ₐ[R] T) :
    (tensorSpecIso R X T).inv ≫
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.map (AlgHom.id R Γ(X.left, ⊤)) φ).toRingHom) =
      tensorPullbackMap R X φ ≫ (tensorSpecIso R X S).inv := by
  apply (cancel_mono (tensorSpecIso R X S).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [tensorSpecIso_naturality, Iso.inv_hom_id_assoc]

end AlgebraicGeometry.Scheme.AffineBaseChange

end -- original noncomputable section
end

/- Migration source: R5Lab/Aglib/AlgebraicGeometry/AffineScheme/BaseChangeCoordinates.lean
Frozen packet R5 f8a3314ddecffcada2ec721d26d56a937bed9690.
SHA-256 4adf46219798b73f06d6ab1cf1b916e56e25f34aecadae308fc032d5e96d118f.
Native names and imports replace the source wrappers; stated conditions and maps are retained. -/
