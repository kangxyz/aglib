/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Smooth.SplitSectionCompletion
public import Mathlib.AlgebraicGeometry.Pullbacks

/-! # The original section of a completed tensor-product cover

The native completion projection and prescribed section form a commuting
square on spectra. One native `pullbackSpecIso` transports its pullback lift
to the original tensor-product spectrum, retaining both projection equations.
No smoothness or finiteness assumption is needed for this construction.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme

universe u

private theorem specMap_comp_of_comp_eq
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) (h : R →+* T) (he : g.comp f = h) :
    Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom f) =
      Spec.map (CommRingCat.ofHom h) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, he]

/-- The original two tensor inclusions give the native affine pullback square. -/
theorem isPullback_tensorSpec (B P C : Type u) [CommRing B] [CommRing P] [CommRing C]
    [Algebra B P] [Algebra B C] :
    IsPullback
      (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : C →ₐ[B] P ⊗[B] C).toRingHom))
      (Spec.algebraMap P (P ⊗[B] C)) (Spec.algebraMap B C) (Spec.algebraMap B P) :=
  (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct B P C)).flip

/-- The native completion projection retains the complete original augmentation map. -/
theorem splitCompletionProjection_comp_algebraMap
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] (ε : B →ₐ[A] A) :
    (AdicCompletion.kerProj (Algebra.Smooth.splitSection_surjective ε)).toRingHom.comp
      (algebraMap B (AdicCompletion (RingHom.ker ε.toRingHom) B)) = ε.toRingHom := by
  ext b
  exact AdicCompletion.kerProj_of (Algebra.Smooth.splitSection_surjective ε) b

/-- A prescribed section lifts to the same original completed tensor-product cover,
with both original projections retained. -/
theorem smoothCompletion_exists_section
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] (ε : B →ₐ[A] A) (δ : C →+* A)
    (hδ : δ.comp (algebraMap B C) = ε.toRingHom) :
    ∃ a : Spec (.of A) ⟶
        Spec (.of (AdicCompletion (RingHom.ker ε.toRingHom) B ⊗[B] C)),
      a ≫ Spec.algebraMap (AdicCompletion (RingHom.ker ε.toRingHom) B)
          (AdicCompletion (RingHom.ker ε.toRingHom) B ⊗[B] C) =
        Spec.map (CommRingCat.ofHom
          (AdicCompletion.kerProj (Algebra.Smooth.splitSection_surjective ε)).toRingHom) ∧
      a ≫ Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight : C →ₐ[B]
            AdicCompletion (RingHom.ker ε.toRingHom) B ⊗[B] C).toRingHom) =
        Spec.map (CommRingCat.ofHom δ) := by
  let ζ : Spec (.of A) ⟶ Spec (.of (AdicCompletion (RingHom.ker ε.toRingHom) B)) :=
    Spec.map (CommRingCat.ofHom
      (AdicCompletion.kerProj (Algebra.Smooth.splitSection_surjective ε)).toRingHom)
  have hs : ζ ≫ Spec.algebraMap B (AdicCompletion (RingHom.ker ε.toRingHom) B) =
      Spec.map (CommRingCat.ofHom δ) ≫ Spec.algebraMap B C :=
    (specMap_comp_of_comp_eq _ _ _ (splitCompletionProjection_comp_algebraMap ε)).trans
      (specMap_comp_of_comp_eq _ _ _ hδ).symm
  let l := pullback.lift ζ (Spec.map (CommRingCat.ofHom δ)) hs
  let e := pullbackSpecIso B (AdicCompletion (RingHom.ker ε.toRingHom) B) C
  refine ⟨l ≫ e.hom, ?_, ?_⟩
  · rw [Category.assoc, pullbackSpecIso_hom_fst', pullback.lift_fst]
    rfl
  · have he : e.hom ≫ Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : C →ₐ[B]
          AdicCompletion (RingHom.ker ε.toRingHom) B ⊗[B] C).toRingHom) =
        pullback.snd (Spec.algebraMap B (AdicCompletion (RingHom.ker ε.toRingHom) B))
          (Spec.algebraMap B C) :=
      pullbackSpecIso_hom_snd B (AdicCompletion (RingHom.ker ε.toRingHom) B) C
    rw [Category.assoc, he]
    exact pullback.lift_snd ζ (Spec.map (CommRingCat.ofHom δ)) hs

end AlgebraicGeometry.Scheme
