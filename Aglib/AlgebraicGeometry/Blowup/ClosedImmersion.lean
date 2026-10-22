/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.ClosedImmersion.Affine

/-!
# Closed-subscheme blowup embeddings

The comparison is the native universal-property `BaseChange.map`. Affine
localization uses only flat open base change, never a nonflat pullback identity.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Blowup.BaseChange

/-- The affine-ring theorem for arbitrary actual ideal sheaves on the two spectra. -/
theorem map_isClosedImmersion_spec {A R : Type u} [CommRing A] [CommRing R]
    (f : A →+* R) (hf : Function.Surjective f)
    {I : (Spec (.of A)).IdealSheafData} {J : (Spec (.of R)).IdealSheafData}
    (hI : I.comap (Spec.map (CommRingCat.ofHom f)) = J)
    (B : BlowupDatum I) (C : BlowupDatum J) :
    IsClosedImmersion (map (Spec.map (CommRingCat.ofHom f)) hI B C) := by
  let K := spectrumIdeal I
  have hK : affineCenter A K = I := affineCenter_spectrumIdeal I
  clear_value K
  subst I
  have hJ : affineCenter R (K.map f) = J := (affineCenter_comap f K).symm.trans hI
  cases hJ
  exact map_isClosedImmersion_affineCenter f hf K B C

/-- Closedness over an affine target, transported through the actual spectrum isomorphisms. -/
theorem map_isClosedImmersion_of_isAffine {X Z : Scheme.{u}} [IsAffine X]
    (i : Z ⟶ X) [IsClosedImmersion i]
    {I : X.IdealSheafData} {J : Z.IdealSheafData} (hI : I.comap i = J)
    (B : BlowupDatum I) (C : BlowupDatum J) :
    IsClosedImmersion (map i hI B C) := by
  let : IsAffine Z := isAffine_of_isAffineHom i
  let B₀ := flatPullbackDatum B X.isoSpec.inv
  let C₀ := flatPullbackDatum C Z.isoSpec.inv
  have h₀ : (I.comap X.isoSpec.inv).comap (Spec.map i.appTop) =
      J.comap Z.isoSpec.inv := by
    rw [← Scheme.IdealSheafData.comap_comp, Scheme.isoSpec_inv_naturality,
      Scheme.IdealSheafData.comap_comp, hI]
  let k₀ := map (Spec.map i.appTop) h₀ B₀ C₀
  let b : B₀.Y ⟶ B.Y := pullback.fst B.map X.isoSpec.inv
  let c : C₀.Y ⟶ C.Y := pullback.fst C.map Z.isoSpec.inv
  let : IsIso b := show IsIso (pullback.fst B.map X.isoSpec.inv) from inferInstance
  let : IsIso c := show IsIso (pullback.fst C.map Z.isoSpec.inv) from inferInstance
  let : IsClosedImmersion k₀ := map_isClosedImmersion_spec i.appTop.hom
    (IsClosedImmersion.isAffine_surjective_of_isAffine i).2 h₀ B₀ C₀
  have hc : c ≫ C.map = C₀.map ≫ Z.isoSpec.inv := pullback.condition
  have hb : b ≫ B.map = B₀.map ≫ X.isoSpec.inv := pullback.condition
  have hk : k₀ ≫ B₀.map = C₀.map ≫ Spec.map i.appTop := map_triangle _ _ _ _
  have he : c ≫ map i hI B C = k₀ ≫ b := by
    apply B.hom_ext
      (cartierPullback_comp_of_flat I (C.map ≫ i) (cartier_composite i hI C) c)
    · simp only [Category.assoc, map_triangle]
    · rw [Category.assoc, hb, ← Category.assoc, hk, Category.assoc,
        Scheme.isoSpec_inv_naturality, ← Category.assoc, ← hc, Category.assoc]
  have he' : map i hI B C = inv c ≫ k₀ ≫ b := by
    rw [← he]
    simp
  rw [he']
  infer_instance

/-- A closed immersion induces a closed immersion of the actual blowups in inverse-image
centres. Only open base changes occur in the locality proof. -/
theorem map_isClosedImmersion {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    {I : X.IdealSheafData} {J : Z.IdealSheafData} (hI : I.comap i = J)
    (B : BlowupDatum I) (C : BlowupDatum J) :
    IsClosedImmersion (map i hI B C) := by
  let k := map i hI B C
  let 𝒰 := X.affineCover.pullback₁ B.map
  rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @IsClosedImmersion) 𝒰]
  intro a
  change X.affineCover.I₀ at a
  let : IsAffine (X.affineCover.X a) := inferInstance
  let u : X.affineCover.X a ⟶ X := X.affineCover.f a
  let : IsOpenImmersion u := X.affineCover.map_prop a
  let v := pullback.fst i u
  let : IsOpenImmersion v := show IsOpenImmersion (pullback.fst i u) from inferInstance
  let i₀ := pullback.snd i u
  let : IsClosedImmersion i₀ := show IsClosedImmersion (pullback.snd i u) from inferInstance
  let B₀ := flatPullbackDatum B u
  let C₀ := flatPullbackDatum C v
  let b : B₀.Y ⟶ B.Y := pullback.fst B.map u
  let c : C₀.Y ⟶ C.Y := pullback.fst C.map v
  let : IsOpenImmersion c := show IsOpenImmersion (pullback.fst C.map v) from inferInstance
  have h₀ : (I.comap u).comap i₀ = J.comap v := by
    rw [← Scheme.IdealSheafData.comap_comp, ← pullback.condition,
      Scheme.IdealSheafData.comap_comp, hI]
  let k₀ := map i₀ h₀ B₀ C₀
  let : IsClosedImmersion k₀ := map_isClosedImmersion_of_isAffine i₀ h₀ B₀ C₀
  have hc : c ≫ C.map = C₀.map ≫ v := pullback.condition
  have hb : b ≫ B.map = B₀.map ≫ u := pullback.condition
  have hk₀ : k₀ ≫ B₀.map = C₀.map ≫ i₀ := map_triangle _ _ _ _
  have hk : k ≫ B.map = C.map ≫ i := map_triangle _ _ _ _
  have he : k₀ ≫ b = c ≫ k := by
    apply B.hom_ext
      (cartierPullback_comp_of_flat I (C.map ≫ i) (cartier_composite i hI C) c)
    · rw [Category.assoc, hb, ← Category.assoc, hk₀, Category.assoc,
        ← pullback.condition, ← Category.assoc, ← hc, Category.assoc]
    · simp only [Category.assoc, hk]
  have hout : IsPullback (k₀ ≫ B₀.map) c u (k ≫ B.map) := by
    rw [hk₀, hk]
    exact (IsPullback.of_hasPullback C.map v).flip.paste_horiz
      (IsPullback.of_hasPullback i u).flip
  have hs : IsPullback k₀ c b k := hout.of_right he
    (IsPullback.of_hasPullback B.map u).flip
  change IsClosedImmersion (pullback.snd k b)
  rw [← hs.flip.isoPullback_inv_snd]
  infer_instance

end AlgebraicGeometry.Scheme.Blowup.BaseChange
