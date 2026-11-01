/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Stalk.Scalar
public import Aglib.AlgebraicGeometry.Stalk.FlatBaseChange
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# The canonical tensor map to a fibre-product stalk

The source is the native tensor product of the two actual factor stalks,
with their original structural scalars. The map is the tensor of the
actual projection stalk maps. Its scheme map factors the original
localization through the product of the two original stalk spectra.
No affine chart or alternative local-ring model is part of the public data.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The original structural stalk scalar is the actual map of stalk spectra
followed by the original structural morphism. -/
theorem specMap_stalkScalar {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) (x : X) :
    Spec.map (CommRingCat.ofHom (stalkScalar f x)) = X.fromSpecStalk x ≫ f := by
  change Spec.map ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop ≫
    X.presheaf.germ ⊤ x trivial) = _
  rw [Spec.map_comp, Spec.map_comp, ← Scheme.fromSpecStalk_toSpecΓ]
  simp only [Category.assoc]
  rw [← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

/-- Original structural stalk scalars commute with the actual morphism stalk map. -/
theorem stalkScalar_comp {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (p : X ⟶ Y) (f : Y ⟶ Spec (.of R)) (x : X) :
    stalkScalar (p ≫ f) x = (p.stalkMap x).hom.comp (stalkScalar f (p x)) := by
  have h : CommRingCat.ofHom (stalkScalar (p ≫ f) x) =
      CommRingCat.ofHom (stalkScalar f (p x)) ≫ p.stalkMap x := by
    apply Spec.map_injective
    rw [specMap_stalkScalar, Spec.map_comp, specMap_stalkScalar]
    simpa only [Category.assoc] using (congrArg (fun q => q ≫ f)
      (Scheme.SpecMap_stalkMap_fromSpecStalk p (x := x))).symm
  exact congrArg CommRingCat.Hom.hom h

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme.Pullback

variable {R : Type u} [CommRing R] {X Y : Scheme.{u}}
  (f : X ⟶ Spec (.of R)) (g : Y ⟶ Spec (.of R)) (z : (pullback f g : Scheme))

/-- The native tensor product of the original stalks, with the original
structural maps from the affine base ring. -/
abbrev stalkTensor : Type u :=
  letI := (f.stalkScalar (pullback.fst f g z)).toAlgebra
  letI := (g.stalkScalar (pullback.snd f g z)).toAlgebra
  X.presheaf.stalk (pullback.fst f g z) ⊗[R] Y.presheaf.stalk (pullback.snd f g z)

/-- The canonical tensor of the two actual projection stalk maps. -/
def stalkTensorMap : stalkTensor f g z →+* (pullback f g).presheaf.stalk z := by
  letI := (f.stalkScalar (pullback.fst f g z)).toAlgebra
  letI := (g.stalkScalar (pullback.snd f g z)).toAlgebra
  letI := ((pullback.fst f g ≫ f).stalkScalar z).toAlgebra
  let a : X.presheaf.stalk (pullback.fst f g z) →ₐ[R]
      (pullback f g).presheaf.stalk z :=
    { __ := (pullback.fst f g).stalkMap z |>.hom
      commutes' r := (congrArg (fun h : R →+* _ => h r)
        (Scheme.Hom.stalkScalar_comp (pullback.fst f g) f z)).symm }
  let b : Y.presheaf.stalk (pullback.snd f g z) →ₐ[R]
      (pullback f g).presheaf.stalk z :=
    { __ := (pullback.snd f g).stalkMap z |>.hom
      commutes' r := by
        change (pullback.snd f g).stalkMap z (g.stalkScalar (pullback.snd f g z) r) =
          (pullback.fst f g ≫ f).stalkScalar z r
        rw [pullback.condition, Scheme.Hom.stalkScalar_comp]
        rfl }
  exact (Algebra.TensorProduct.lift a b (fun _ _ => Commute.all _ _)).toRingHom

/-- The map retains the actual product of the two projection-stalk images. -/
theorem stalkTensorMap_tmul
    (a : X.presheaf.stalk (pullback.fst f g z))
    (b : Y.presheaf.stalk (pullback.snd f g z)) :
    letI := (f.stalkScalar (pullback.fst f g z)).toAlgebra
    letI := (g.stalkScalar (pullback.snd f g z)).toAlgebra
    stalkTensorMap f g z (a ⊗ₜ[R] b) =
      (pullback.fst f g).stalkMap z a * (pullback.snd f g).stalkMap z b := rfl

/-- The localization prime is intrinsic to the canonical map: the inverse
image of the actual maximal ideal of the product stalk. -/
def stalkTensorPrime : PrimeSpectrum (stalkTensor f g z) :=
  (IsLocalRing.closedPoint ((pullback f g).presheaf.stalk z)).comap (stalkTensorMap f g z)

private def stalkTensorSpecToProduct : Spec (.of (stalkTensor f g z)) ⟶ pullback f g := by
  letI := (f.stalkScalar (pullback.fst f g z)).toAlgebra
  letI := (g.stalkScalar (pullback.snd f g z)).toAlgebra
  exact (pullbackSpecIso R (X.presheaf.stalk (pullback.fst f g z))
      (Y.presheaf.stalk (pullback.snd f g z))).inv ≫
    pullback.map _ _ f g (X.fromSpecStalk (pullback.fst f g z))
      (Y.fromSpecStalk (pullback.snd f g z)) (𝟙 _)
      (by rw [Category.comp_id]; exact Scheme.Hom.specMap_stalkScalar f _)
      (by rw [Category.comp_id]; exact Scheme.Hom.specMap_stalkScalar g _)

private theorem stalkTensorSpecToProduct_fst :
    letI := (f.stalkScalar (pullback.fst f g z)).toAlgebra
    letI := (g.stalkScalar (pullback.snd f g z)).toAlgebra
    stalkTensorSpecToProduct f g z ≫ pullback.fst f g =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := R) (A := X.presheaf.stalk (pullback.fst f g z))
        (B := Y.presheaf.stalk (pullback.snd f g z)))) ≫
          X.fromSpecStalk (pullback.fst f g z) := by
  dsimp only [stalkTensorSpecToProduct]
  rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pullbackSpecIso_inv_fst]

private theorem stalkTensorSpecToProduct_snd :
    letI := (f.stalkScalar (pullback.fst f g z)).toAlgebra
    letI := (g.stalkScalar (pullback.snd f g z)).toAlgebra
    stalkTensorSpecToProduct f g z ≫ pullback.snd f g =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R) (A := X.presheaf.stalk (pullback.fst f g z))
        (B := Y.presheaf.stalk (pullback.snd f g z))).toRingHom) ≫
          Y.fromSpecStalk (pullback.snd f g z) := by
  dsimp only [stalkTensorSpecToProduct]
  rw [Category.assoc, pullback.lift_snd, ← Category.assoc, pullbackSpecIso_inv_snd]
  rfl

private theorem stalkTensorSpecToProduct_preimmersion :
    IsPreimmersion (stalkTensorSpecToProduct f g z) := by
  let := (f.stalkScalar (pullback.fst f g z)).toAlgebra
  let := (g.stalkScalar (pullback.snd f g z)).toAlgebra
  have hm := MorphismProperty.pullbackMap (P := @IsPreimmersion)
    (f := Spec.map (CommRingCat.ofHom (algebraMap R
      (X.presheaf.stalk (pullback.fst f g z)))))
    (g := Spec.map (CommRingCat.ofHom (algebraMap R
      (Y.presheaf.stalk (pullback.snd f g z)))))
    (f' := f) (g' := g) (i₁ := X.fromSpecStalk (pullback.fst f g z))
    (i₂ := Y.fromSpecStalk (pullback.snd f g z)) inferInstance inferInstance
    (Scheme.Hom.specMap_stalkScalar f _) (Scheme.Hom.specMap_stalkScalar g _)
  dsimp only [stalkTensorSpecToProduct]
  exact IsPreimmersion.comp _ _

/-- The canonical tensor map factors the original localization of the
product through the product of the two actual stalk spectra. -/
private theorem specMap_stalkTensorMap_comp :
    Spec.map (CommRingCat.ofHom (stalkTensorMap f g z)) ≫
        stalkTensorSpecToProduct f g z = (pullback f g).fromSpecStalk z := by
  let := (f.stalkScalar (pullback.fst f g z)).toAlgebra
  let := (g.stalkScalar (pullback.snd f g z)).toAlgebra
  apply pullback.hom_ext
  · rw [Category.assoc, stalkTensorSpecToProduct_fst, ← Category.assoc, ← Spec.map_comp]
    have h : CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := R) (A := X.presheaf.stalk (pullback.fst f g z))
        (B := Y.presheaf.stalk (pullback.snd f g z))) ≫
          CommRingCat.ofHom (stalkTensorMap f g z) = (pullback.fst f g).stalkMap z := by
      ext a
      change stalkTensorMap f g z (a ⊗ₜ[R] 1) = _
      rw [stalkTensorMap_tmul, map_one, mul_one]
    rw [h]
    exact Scheme.SpecMap_stalkMap_fromSpecStalk (pullback.fst f g)
  · rw [Category.assoc, stalkTensorSpecToProduct_snd, ← Category.assoc, ← Spec.map_comp]
    have h : CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R) (A := X.presheaf.stalk (pullback.fst f g z))
        (B := Y.presheaf.stalk (pullback.snd f g z))).toRingHom ≫
          CommRingCat.ofHom (stalkTensorMap f g z) = (pullback.snd f g).stalkMap z := by
      ext b
      change stalkTensorMap f g z (1 ⊗ₜ[R] b) = _
      rw [stalkTensorMap_tmul, map_one, one_mul]
    rw [h]
    exact Scheme.SpecMap_stalkMap_fromSpecStalk (pullback.snd f g)

/-- The actual tensor-stalk map is flat over every commutative affine base. -/
theorem stalkTensorMap_flat : (stalkTensorMap f g z).Flat := by
  have hm := stalkTensorSpecToProduct_preimmersion f g z
  have : Flat (Spec.map (CommRingCat.ofHom (stalkTensorMap f g z))) :=
    MorphismProperty.of_postcomp (W := @Flat)
      (W' := MorphismProperty.monomorphisms Scheme)
      (Spec.map (CommRingCat.ofHom (stalkTensorMap f g z)))
      (stalkTensorSpecToProduct f g z) inferInstance
      (by rw [specMap_stalkTensorMap_comp]; exact Scheme.fromSpecStalk_flat _ _)
  exact Flat.SpecMap_iff.mp this

private theorem specMap_stalkTensorMap_preimmersion :
    IsPreimmersion (Spec.map (CommRingCat.ofHom (stalkTensorMap f g z))) := by
  have := stalkTensorSpecToProduct_preimmersion f g z
  have : IsPreimmersion (Spec.map (CommRingCat.ofHom (stalkTensorMap f g z)) ≫
      stalkTensorSpecToProduct f g z) := by
    rw [specMap_stalkTensorMap_comp]
    infer_instance
  exact IsPreimmersion.of_comp
    (Spec.map (CommRingCat.ofHom (stalkTensorMap f g z))) (stalkTensorSpecToProduct f g z)

private theorem isLocalization_of_iso_of_comp
    {A S B : CommRingCat.{u}} [Algebra A S] (P : Submonoid A) [IsLocalization P S]
    (φ : A ⟶ B) (e : S ≅ B)
    (h : CommRingCat.ofHom (algebraMap A S) ≫ e.hom = φ) :
    letI := φ.hom.toAlgebra
    IsLocalization P B := by
  let := φ.hom.toAlgebra
  let e' : S ≃ₐ[A] B :=
    { __ := e.commRingCatIsoToRingEquiv
      commutes' a := ConcreteCategory.congr_hom h a }
  exact (IsLocalization.isLocalization_iff_of_algEquiv P e').mp inferInstance

private theorem isLocalization_of_flat_preimmersion
    {A B : Type u} [CommRing A] [CommRing B] [IsLocalRing B] (φ : A →+* B)
    [Flat (Spec.map (CommRingCat.ofHom φ))]
    [IsPreimmersion (Spec.map (CommRingCat.ofHom φ))] :
    let := φ.toAlgebra
    IsLocalization.AtPrime B ((IsLocalRing.closedPoint B).comap φ).asIdeal := by
  let := φ.toAlgebra
  let p : PrimeSpectrum A := (IsLocalRing.closedPoint B).comap φ
  let t : (Spec (.of A)).presheaf.stalk p ⟶ CommRingCat.of B :=
    Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom φ))
  have : IsIso ((Spec.map (CommRingCat.ofHom φ)).stalkMap (IsLocalRing.closedPoint B)) :=
    Scheme.Hom.isIso_stalkMap_of_flat_of_surjectiveOnStalks _ _
  have : IsIso t := by
    dsimp only [t, Scheme.stalkClosedPointTo]
    infer_instance
  let e₀ : CommRingCat.of (Localization.AtPrime p.asIdeal) ≅ CommRingCat.of B :=
    (Spec.stalkIso (.of A) p).symm ≪≫ asIso t
  have ht : CommRingCat.ofHom (algebraMap A (Localization.AtPrime p.asIdeal)) ≫
      e₀.hom = CommRingCat.ofHom φ := by
    change CommRingCat.ofHom (algebraMap A (Localization.AtPrime p.asIdeal)) ≫
      (Spec.stalkIso (.of A) p).inv ≫ t = _
    erw [Spec.algebraMap_stalkIso_inv_assoc (R := CommRingCat.of A) (x := p)]
    change (Scheme.ΓSpecIso (.of A)).inv ≫ (Spec (.of A)).presheaf.germ ⊤ p trivial ≫
      Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom φ)) = _
    erw [Scheme.germ_stalkClosedPointTo_Spec (CommRingCat.ofHom φ)]
    exact Iso.inv_hom_id_assoc _ _
  exact isLocalization_of_iso_of_comp p.asIdeal.primeCompl (CommRingCat.ofHom φ) e₀ ht

/-- The actual stalk of a fibre product is the localization of the native
tensor of the original factor stalks at the intrinsic inverse-image prime.
This holds over every commutative affine base. -/
theorem isLocalization_stalkTensorMap :
    letI := (stalkTensorMap f g z).toAlgebra
    IsLocalization.AtPrime ((pullback f g).presheaf.stalk z)
      (stalkTensorPrime f g z).asIdeal := by
  have : Flat (Spec.map (CommRingCat.ofHom (stalkTensorMap f g z))) :=
    Flat.SpecMap_iff.mpr (stalkTensorMap_flat f g z)
  have := specMap_stalkTensorMap_preimmersion f g z
  exact isLocalization_of_flat_preimmersion (stalkTensorMap f g z)

end AlgebraicGeometry.Scheme.Pullback
