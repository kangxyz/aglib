/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.GaloisFibers
public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.EtaleBaseChange
public import Aglib.AlgebraicGeometry.Morphisms.Etale.PointwiseOpenBaseChange
public import Aglib.AlgebraicGeometry.Properties.Normal.Affine

/-! # Fibrewise etaleness on one original affine chart

Only the original open pullback and the native normalization comparison are
used. No global group action or additional field realization is constructed.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery

universe u

variable {X U : Scheme.{u}} [IsIntegral X] [IsIntegral U]
  (j : U ⟶ X) [IsOpenImmersion j]
  (Y : Scheme.FiniteEtale U) [IsIntegral Y.obj.left] [IsGalois Y]

/-- Etaleness propagates between original fibre points over an original
normal affine open immersion. The actual open pullback supplies every model. -/
theorem genericNormalization_etaleAt_of_image_eq_of_affineOpen
    (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    (b : Spec (.of R) ⟶ X) [IsOpenImmersion b]
    (x y : (genericMap j Y.obj.hom).normalization)
    (hx : (genericMap j Y.obj.hom).fromNormalization x ∈ Set.range b)
    (hxy : (genericMap j Y.obj.hom).fromNormalization x =
      (genericMap j Y.obj.hom).fromNormalization y)
    (het : (genericMap j Y.obj.hom).fromNormalization.etaleAt x) :
    (genericMap j Y.obj.hom).fromNormalization.etaleAt y := by
  let : IsDominant j := Scheme.isDominant_of_isOpenImmersion j
  let : IsDominant b := Scheme.isDominant_of_isOpenImmersion b
  let : IsDominant Y.obj.hom := GenericGalois.dominant Y
  obtain ⟨v, hv, hv'⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := j) (g := b) (genericPoint U) (genericPoint (Spec (.of R))) (by
      rw [Scheme.map_genericPoint_of_isDominant U j,
        Scheme.map_genericPoint_of_isDominant (Spec (.of R)) b])
  let : Nonempty ↑(pullback j b : Scheme) := ⟨v⟩
  let : IsIntegral (pullback j b) := isIntegral_of_isOpenImmersion (pullback.fst j b)
  let g := pullback.fst j b
  let jB := pullback.snd j b
  let : IsDominant g := Scheme.isDominant_of_isOpenImmersion g
  let YB := (Scheme.FiniteEtale.baseChange g).obj Y
  obtain ⟨w, hw, hw'⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := Y.obj.hom) (g := g) (genericPoint Y.obj.left) (genericPoint (pullback j b : Scheme)) (by
      rw [Scheme.map_genericPoint_of_isDominant Y.obj.left Y.obj.hom,
        Scheme.map_genericPoint_of_isDominant (pullback j b : Scheme) g])
  let : Nonempty YB.obj.left := ⟨w⟩
  let : IsIntegral YB.obj.left := isIntegral_of_isOpenImmersion (pullback.fst Y.obj.hom g)
  let : IsGalois YB := baseChange_isGalois_of_connected g Y
  let f := (genericMap j Y.obj.hom).fromNormalization
  let fB := (genericMap jB YB.obj.hom).fromNormalization
  let e := etaleBaseChangeIso j jB b g (IsPullback.of_hasPullback j b) Y
  have he : e.hom ≫ pullback.snd f b = fB := etaleBaseChangeIso_hom_snd ..
  let i := e.hom ≫ pullback.fst f b
  have H : i ≫ f = fB ≫ b := by
    dsimp only [i]
    rw [Category.assoc, pullback.condition, ← Category.assoc, he]
  have hs : e.inv ≫ fB = pullback.snd f b := by
    rw [← cancel_epi e.hom]
    simp only [Iso.hom_inv_id_assoc, he]
  obtain ⟨r, hr⟩ := hx
  obtain ⟨a, ha, ha'⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := f) (g := b) x r hr.symm
  obtain ⟨a', ha₂, ha₂'⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := f) (g := b) y r (hxy.symm.trans hr.symm)
  have hi : e.inv ≫ i = pullback.fst f b := by
    dsimp only [i]
    simp only [Iso.inv_hom_id_assoc]
  have hix : i (e.inv a) = x :=
    (congrArg (fun k : pullback f b ⟶ _ => k a) hi).trans ha
  have hiy : i (e.inv a') = y :=
    (congrArg (fun k : pullback f b ⟶ _ => k a') hi).trans ha₂
  have hxB : fB.etaleAt (e.inv a) :=
    (Hom.etaleAt_iff_of_open_square i fB f b H (e.inv a)).mpr (by simpa only [hix] using het)
  have hsame : fB (e.inv a) = fB (e.inv a') := by
    change (e.inv ≫ fB) a = (e.inv ≫ fB) a'
    rw [hs, ha', ha₂']
  have hyB := genericNormalization_etaleAt_of_image_eq R jB YB
    (e.inv a) (e.inv a') hsame hxB
  have hy := (Hom.etaleAt_iff_of_open_square i fB f b H (e.inv a')).mp hyB
  simpa only [hiy] using hy

/-- The chosen actual affine open of the original target is enough; every
point above the same base point stays in this one chart. -/
theorem genericNormalization_etaleAt_of_image_eq_in_affineOpen
    [∀ z : X, IsIntegrallyClosed (X.presheaf.stalk z)]
    (V : X.Opens) (hV : IsAffineOpen V)
    (x y : (genericMap j Y.obj.hom).normalization)
    (hx : (genericMap j Y.obj.hom).fromNormalization x ∈ V)
    (hxy : (genericMap j Y.obj.hom).fromNormalization x =
      (genericMap j Y.obj.hom).fromNormalization y)
    (het : (genericMap j Y.obj.hom).fromNormalization.etaleAt x) :
    (genericMap j Y.obj.hom).fromNormalization.etaleAt y := by
  let : Nonempty V := ⟨⟨_, hx⟩⟩
  let : IsIntegrallyClosed Γ(X, V) :=
    Scheme.isIntegrallyClosed_sections_of_isAffineOpen X V hV
  exact genericNormalization_etaleAt_of_image_eq_of_affineOpen j Y Γ(X, V) hV.fromSpec
    x y (by rwa [hV.range_fromSpec]) hxy het

end AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery
