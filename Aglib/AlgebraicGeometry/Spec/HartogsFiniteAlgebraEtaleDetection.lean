/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Spec.HartogsFiniteEtaleAlgebra
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.BaseChange
public import Aglib.AlgebraicGeometry.Stalk.LocalBaseIdeal
public import Aglib.AlgebraicGeometry.Stalk.SpecLocalRing
public import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent

/-! # Etaleness detected through the original closed-base-point stalk

A recovery square over an open is pulled back along the original ambient
stalk. Flatness and the closed-base-point equation make that exact scalar map
faithfully flat. Native etale descent then detects the original coefficient
algebra. No normality or locality of the coefficient algebra is assumed.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme

universe u

/-- The actual ambient stalk over the closed point of a local affine base
is faithfully flat over that base whenever the original morphism is flat. -/
theorem stalkScalar_faithfullyFlat_of_closedPoint
    {A : Type u} [CommRing A] [IsLocalRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) [Flat f] (x : X)
    (hx : f x = IsLocalRing.closedPoint A) : (f.stalkScalar x).FaithfullyFlat := by
  let := (f.stalkScalar x).toAlgebra
  let : Module.Flat A (X.presheaf.stalk x) := f.stalkScalar_flat x
  let : IsLocalHom (algebraMap A (X.presheaf.stalk x)) :=
    f.stalkScalar_isLocalHom_of_closedPoint x hx
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

/-- An original recovery square over an open detects etaleness on the base
of that square using a point above the closed point. The actual ambient stalk,
not a replacement localization, is used for descent. -/
theorem etale_of_open_recovery_of_closedPoint
    {A : Type u} [CommRing A] [IsLocalRing A] {X T W : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) [Flat f] (U : X.Opens)
    (p : W ⟶ U.toScheme) [Etale p] (r : W ⟶ T) (t : T ⟶ Spec (.of A))
    (H : IsPullback p r (U.ι ≫ f) t) (x : X) (hxU : x ∈ U)
    (hx : f x = IsLocalRing.closedPoint A) : Etale t := by
  let k := U.fromSpecStalkOfMem x hxU
  have hk : k ≫ (U.ι ≫ f) =
      Spec.map (CommRingCat.ofHom (f.stalkScalar x)) := by
    rw [← Category.assoc, Opens.fromSpecStalkOfMem_ι]
    exact fromSpecStalk_comp_eq_spec_map_stalkScalar f x
  have hs := (flat_and_surjective_SpecMap_iff
    (CommRingCat.ofHom (f.stalkScalar x))).mpr
      (stalkScalar_faithfullyFlat_of_closedPoint f x hx)
  have hflat : Flat (k ≫ (U.ι ≫ f)) := hk.symm ▸ hs.1
  have hsurj : Surjective (k ≫ (U.ι ≫ f)) := hk.symm ▸ hs.2
  let := hflat
  let := hsurj
  have HP := (IsPullback.of_hasPullback p k).flip.paste_vert H
  exact MorphismProperty.of_isPullback_of_descendsAlong
    (P := @Etale) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) HP
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ inferInstance

/-- The original tensor algebra equivalence supplies its exact affine
pullback square. Its second map is the original right tensor inclusion
followed by the given equivalence. -/
theorem isPullback_of_tensorAlgEquiv
    (A B C₀ C : Type u) [CommRing A] [CommRing B] [CommRing C₀] [CommRing C]
    [Algebra A B] [Algebra A C₀] [Algebra B C]
    (e : B ⊗[A] C₀ ≃ₐ[B] C) :
    IsPullback (Spec.algebraMap B C)
      (Spec.map (CommRingCat.ofHom (e.toRingHom.comp
        (Algebra.TensorProduct.includeRight : C₀ →ₐ[A] B ⊗[A] C₀).toRingHom)))
      (Spec.algebraMap A B) (Spec.algebraMap A C₀) := by
  have H := isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct A B C₀)
  let ei := Scheme.Spec.mapIso e.toRingEquiv.symm.toCommRingCatIso.op
  apply H.of_iso ei (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · change Spec.map (CommRingCat.ofHom (algebraMap B (B ⊗[A] C₀))) ≫ 𝟙 _ =
      Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap B C))
    rw [Category.comp_id, ← Spec.map_comp]
    congr 1
    ext b
    exact (e.symm.commutes b).symm
  · change Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : C₀ →ₐ[A] B ⊗[A] C₀).toRingHom) ≫ 𝟙 _ =
      Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (e.toRingHom.comp
          (Algebra.TensorProduct.includeRight : C₀ →ₐ[A] B ⊗[A] C₀).toRingHom))
    rw [Category.comp_id, ← Spec.map_comp]
    congr 1
    ext a
    exact (e.symm_apply_apply _).symm
  · simp
  · simp

/-- The coefficient algebra is etale if its actual scalar extension is the
original Hartogs cover algebra and that cover meets a closed-base-point fibre.
The algebra equivalence is an explicit middle input, not an etaleness input. -/
theorem etale_coefficient_of_hartogs_tensor_comparison
    (A B C₀ : Type u) [CommRing A] [CommRing B] [CommRing C₀]
    [IsLocalRing A] [IsNoetherianRing B] [Algebra A B] [Algebra A C₀]
    [Module.Flat A B] (V : (Spec (.of B)).Opens)
    (hV : Function.Bijective (affineScalarMap V.ι))
    (D : FiniteEtale V.toScheme)
    (e : letI := (affineScalarMap (D.obj.hom ≫ V.ι)).toAlgebra
      B ⊗[A] C₀ ≃ₐ[B] Γ(D.obj.left, ⊤))
    (q : Spec (.of B)) (hq : q ∈ V)
    (hqA : (Spec.algebraMap A B) q = IsLocalRing.closedPoint A) :
    Algebra.Etale A C₀ := by
  let := (affineScalarMap (D.obj.hom ≫ V.ι)).toAlgebra
  let : Flat (Spec.algebraMap A B) :=
    (HasRingHomProperty.Spec_iff (P := @Flat)).mpr
      (RingHom.flat_algebraMap_iff.mpr inferInstance)
  have H := isPullback_hartogs_finiteAlgebra B V hV D.obj.hom
  have K := isPullback_of_tensorAlgEquiv A B C₀ Γ(D.obj.left, ⊤) e
  have HE : Etale (Spec.algebraMap A C₀) :=
    etale_of_open_recovery_of_closedPoint (Spec.algebraMap A B) V D.obj.hom
      (D.obj.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (e.toRingHom.comp
        (Algebra.TensorProduct.includeRight : C₀ →ₐ[A] B ⊗[A] C₀).toRingHom)))
      (Spec.algebraMap A C₀) (H.paste_vert K) q hq hqA
  exact (RingHom.etale_algebraMap).mp
    ((HasRingHomProperty.Spec_iff (P := @Etale)).mp HE)

end AlgebraicGeometry.Scheme
