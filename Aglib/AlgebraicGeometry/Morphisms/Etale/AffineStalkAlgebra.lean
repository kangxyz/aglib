/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AffineScheme.TensorPullback
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Stalk

/-!
# Original affine section algebras at a target stalk

The algebra on the actual ambient stalk is induced by the original germ.
The resulting tensor square is transported to the actual open chart and its
own stalk using the canonical open-immersion stalk isomorphism.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme

universe u
variable {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
  (B : Type u) [CommRing B] [Algebra Γ(X, U) B] (x : X) (hxU : x ∈ U)

/-- Etaleness of the section algebra after tensoring by the original germ
is etaleness of the actual target-stalk base change. -/
theorem etale_stalkBaseChange_of_etale_tensor
    (h : letI := (X.presheaf.germ U x hxU).hom.toAlgebra
      Algebra.Etale (X.presheaf.stalk x) ((X.presheaf.stalk x) ⊗[Γ(X, U)] B)) :
    Etale (pullback.snd
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) B)) ≫ hU.isoSpec.inv)
      (U.toScheme.fromSpecStalk ⟨x, hxU⟩)) := by
  let := (X.presheaf.germ U x hxU).hom.toAlgebra
  let p := Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) B)) ≫ hU.isoSpec.inv
  let R := X.presheaf.stalk x
  have hAlg : Algebra.Etale R (R ⊗[Γ(X, U)] B) := h
  have H := Spec.isPullback_of_tensorEquiv
    (AlgEquiv.refl : R ⊗[Γ(X, U)] B ≃ₐ[R] R ⊗[Γ(X, U)] B)
    (Algebra.TensorProduct.includeRight : B →ₐ[Γ(X, U)] R ⊗[Γ(X, U)] B).toRingHom
    (by rfl)
  have H' : IsPullback
      (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : B →ₐ[Γ(X, U)] R ⊗[Γ(X, U)] B).toRingHom))
      (Spec.map (CommRingCat.ofHom (algebraMap R (R ⊗[Γ(X, U)] B))))
      p (U.fromSpecStalkOfMem x hxU) := by
    apply H.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) hU.isoSpec.symm
    · simp
    · simp
    · simp [p]
    · simp only [Iso.symm_hom, Iso.refl_hom, Category.id_comp]
      apply (cancel_mono hU.isoSpec.hom).mp
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      change Spec.map (X.presheaf.germ U x hxU) =
        U.fromSpecStalkOfMem x hxU ≫ U.toSpecΓ
      exact (Opens.fromSpecStalkOfMem_toSpecΓ U x hxU).symm
  have hTensor : Etale (Spec.map (CommRingCat.ofHom
      (algebraMap R (R ⊗[Γ(X, U)] B)))) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
      (RingHom.etale_algebraMap.mpr hAlg)
  have hp : Etale (pullback.snd p (U.fromSpecStalkOfMem x hxU)) := by
    apply (MorphismProperty.cancel_left_of_respectsIso @Etale H'.isoPullback.hom _).mp
    simpa only [IsPullback.isoPullback_hom_snd] using hTensor
  let e := Scheme.Spec.mapIso (asIso (U.ι.stalkMap ⟨x, hxU⟩)).symm.op
  have H'' : IsPullback (pullback.fst p (U.fromSpecStalkOfMem x hxU))
      (pullback.snd p (U.fromSpecStalkOfMem x hxU) ≫ e.hom)
      p (U.toScheme.fromSpecStalk ⟨x, hxU⟩) := by
    apply (IsPullback.of_hasPullback p (U.fromSpecStalkOfMem x hxU)).of_iso
      (Iso.refl _) (Iso.refl _) e (Iso.refl _)
    · simp
    · simp
    · simp
    · simp [e, Opens.fromSpecStalkOfMem]
  apply (MorphismProperty.cancel_left_of_respectsIso @Etale H''.isoPullback.hom _).mp
  rw [H''.isoPullback_hom_snd]
  infer_instance

end AlgebraicGeometry.Scheme
