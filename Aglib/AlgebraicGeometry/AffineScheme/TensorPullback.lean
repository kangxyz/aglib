/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Affine pullback from an actual tensor algebra equivalence

Source: R5 baseline `e6d63abca2403f50b6b413101ad7f6a7f2e0e2c7`.
Existing declarations, chosen maps and explicit evidence boundaries are preserved.
-/

@[expose] public section




noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct
universe u

namespace AlgebraicGeometry.Spec

variable {R S A B : Type u} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  [Algebra R S] [Algebra R A] [Algebra S B]

/-- A native algebra tensor equivalence gives the corresponding literal affine pullback. -/
lemma isPullback_of_tensorEquiv (e : S ⊗[R] A ≃ₐ[S] B) (g : A →+* B)
    (h : e.toRingEquiv.toRingHom.comp
      (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A).toRingHom = g) :
    IsPullback (Spec.map (CommRingCat.ofHom g))
      (Spec.map (CommRingCat.ofHom (algebraMap S B)))
      (Spec.map (CommRingCat.ofHom (algebraMap R A)))
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  let i : Spec (.of B) ≅ pullback
      (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (Spec.map (CommRingCat.ofHom (algebraMap R A))) :=
    Scheme.Spec.mapIso e.toRingEquiv.toCommRingCatIso.op ≪≫ (pullbackSpecIso R S A).symm
  apply IsPullback.flip
  apply (IsPullback.of_hasPullback _ _).of_iso' i (.refl _) (.refl _) (.refl _)
  · simp only [i, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      pullbackSpecIso_inv_fst', Iso.refl_hom, Category.comp_id]
    change Spec.map (CommRingCat.ofHom e.toRingEquiv.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap S (S ⊗[R] A))) =
      Spec.map (CommRingCat.ofHom (algebraMap S B))
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro s
    exact e.commutes s
  · simp only [i, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      pullbackSpecIso_inv_snd, Iso.refl_hom, Category.comp_id]
    change Spec.map (CommRingCat.ofHom e.toRingEquiv.toRingHom) ≫
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A).toRingHom) =
      Spec.map (CommRingCat.ofHom g)
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact h
  · simp
  · simp

end AlgebraicGeometry.Spec

/- Migration source: R5Lab/Aglib/AlgebraicGeometry/AffineScheme/TensorPullback.lean
Frozen packet R5 f8a3314ddecffcada2ec721d26d56a937bed9690.
SHA-256 2c1d78d160e3670c6f2f2aefc3fe93a1033b26307651de61d9a7c90ef48b9a0b.
Native names and imports replace the source wrappers; stated conditions and maps are retained. -/
