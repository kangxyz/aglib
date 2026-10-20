/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.Properties

/-!
# Relative normalization comparisons and smooth descent

The comparisons use Mathlib's actual relative normalization and its universal maps.
Integral final factors and source isomorphisms retain the stated structural triangles;
smooth pullback and descent retain the supplied cartesian square.

Source: `R5Lab/Aglib/AlgebraicGeometry/Normalization/Relative.lean`, R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`650965d46d326d81575d6457010fa1de4322761ba02e99750e4ccb68df65bbbc`.
The source's dense-open theorem-family predicate and its proved supplier are in
`Normalization.DenseOpen`. Its regular-local normality predicate is supplied by
`IsRegularLocalRing.isIntegrallyClosed_of_regularLocal` in the native ring owner.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Hom
universe u

variable {X T Y : Scheme.{u}}

/-- Relative normalization is unchanged by an integral final factor, with the
canonical comparison constructed from the existing universal property. -/
def normalizationIntegralFactorIso (j : X ⟶ T) (g : T ⟶ Y)
    [QuasiCompact j] [QuasiSeparated j] [IsIntegralHom g] :
    (j ≫ g).normalization ≅ j.normalization := by
  let d := (j ≫ g).normalizationDesc j g rfl
  let a := (j ≫ g).normalizationDesc j.toNormalization
    (j.fromNormalization ≫ g) (by simp)
  let b := j.normalizationDesc (j ≫ g).toNormalization d (by simp [d])
  have ha : a ≫ j.fromNormalization = d := by
    apply Scheme.Hom.normalization.hom_ext (j ≫ g) _ _ g
    · simp [a, d]
    · simpa only [Category.assoc] using
        (j ≫ g).normalizationDesc_comp j.toNormalization (j.fromNormalization ≫ g) (by simp)
    · exact (j ≫ g).normalizationDesc_comp j g rfl
  refine ⟨a, b, ?_, ?_⟩
  · apply Scheme.Hom.normalization.hom_ext (j ≫ g) _ _ (j ≫ g).fromNormalization
    · simp [a, b]
    · rw [← (j ≫ g).normalizationDesc_comp j g rfl]
      change (a ≫ b) ≫ d ≫ g = _
      simp only [Category.assoc]
      rw [← Category.assoc b d g, show b ≫ d = j.fromNormalization from
        j.normalizationDesc_comp (j ≫ g).toNormalization d (by simp [d])]
      rw [← Category.assoc, ha]
    · simp
  · apply Scheme.Hom.normalization.hom_ext j _ _ j.fromNormalization
    · simp [a, b]
    · rw [Category.assoc, ha]
      exact j.normalizationDesc_comp (j ≫ g).toNormalization d (by simp [d])
    · simp

@[reassoc, simp] theorem normalizationIntegralFactorIso_hom_over
    (j : X ⟶ T) (g : T ⟶ Y) [QuasiCompact j] [QuasiSeparated j] [IsIntegralHom g] :
    (normalizationIntegralFactorIso j g).hom ≫ j.fromNormalization ≫ g =
      (j ≫ g).fromNormalization := by
  exact (j ≫ g).normalizationDesc_comp j.toNormalization (j.fromNormalization ≫ g) (by simp)

/-- Invariance under the exact isomorphism of the original generic sources. -/
def normalizationSourceIso {X' : Scheme.{u}} (e : X ≅ X') (f : X ⟶ Y) (f' : X' ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact f'] [QuasiSeparated f']
    (h : e.hom ≫ f' = f) : f.normalization ≅ f'.normalization := by
  let a := f.normalizationDesc (e.hom ≫ f'.toNormalization) f'.fromNormalization (by simp [h])
  have h' : e.inv ≫ f = f' := by rw [← h]; simp
  let b := f'.normalizationDesc (e.inv ≫ f.toNormalization) f.fromNormalization (by simp [h'])
  refine ⟨a, b, ?_, ?_⟩
  · apply Scheme.Hom.normalization.hom_ext f _ _ f.fromNormalization
    · simp [a, b]
    · simp [a, b]
    · simp
  · apply Scheme.Hom.normalization.hom_ext f' _ _ f'.fromNormalization
    · simp [a, b]
    · simp [a, b]
    · simp

@[reassoc, simp] theorem normalizationSourceIso_hom_over {X' : Scheme.{u}}
    (e : X ≅ X') (f : X ⟶ Y) (f' : X' ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact f'] [QuasiSeparated f']
    (h : e.hom ≫ f' = f) :
    (normalizationSourceIso e f f' h).hom ≫ f'.fromNormalization = f.fromNormalization := by
  exact f.normalizationDesc_comp (e.hom ≫ f'.toNormalization) f'.fromNormalization (by simp [h])

@[reassoc, simp] theorem normalizationSourceIso_hom_generic {X' : Scheme.{u}}
    (e : X ≅ X') (f : X ⟶ Y) (f' : X' ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact f'] [QuasiSeparated f']
    (h : e.hom ≫ f' = f) :
    f.toNormalization ≫ (normalizationSourceIso e f f' h).hom = e.hom ≫ f'.toNormalization := by
  exact f.toNormalization_normalizationDesc (e.hom ≫ f'.toNormalization)
    f'.fromNormalization (by simp [h])

/-- Smooth pullback of a morphism with trivial relative normalization again
has trivial relative normalization, retaining the given pullback square. -/
theorem normalizationFrom_isIso_of_smooth_pullback {X' : Scheme.{u}}
    (f : X ⟶ Y) (g : T ⟶ Y) (p : X' ⟶ X) (j : X' ⟶ T)
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact j] [QuasiSeparated j]
    [Smooth g] [IsIso f.fromNormalization] (hp : IsPullback p j f g) :
    IsIso j.fromNormalization := by
  let e := normalizationSourceIso hp.isoPullback j (pullback.snd f g)
    hp.isoPullback_hom_snd
  have he : e.hom ≫ f.normalizationPullback g ≫ pullback.snd f.fromNormalization g =
      j.fromNormalization := by
    rw [Scheme.Hom.normalizationPullback_snd]
    exact normalizationSourceIso_hom_over ..
  rw [← he]
  infer_instance

/-- The canonical integral factor comparison is an isomorphism once the
source-side relative normalization is trivial. -/
theorem normalizationDesc_isIso (f : X ⟶ Y) (j : X ⟶ T) (g : T ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact j] [QuasiSeparated j]
    [IsIntegralHom g] [IsIso j.fromNormalization] (h : f = j ≫ g) :
    IsIso (f.normalizationDesc j g h) := by
  subst f
  have he : (normalizationIntegralFactorIso j g).hom ≫ j.fromNormalization =
      (j ≫ g).normalizationDesc j g rfl := by
    apply Scheme.Hom.normalization.hom_ext (j ≫ g) _ _ g
    · simp [normalizationIntegralFactorIso]
    · exact normalizationIntegralFactorIso_hom_over j g
    · simp
  rw [← he]
  infer_instance

/-- Normalization étaleness descends along the same actual smooth fpqc square. -/
theorem normalization_etale_of_smooth_pullback
    {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y)
    (p : X' ⟶ X) (f' : X' ⟶ Y')
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact f'] [QuasiSeparated f']
    [Smooth g] [Surjective g] [QuasiCompact g]
    (hp : IsPullback p f' f g) (h : Etale f'.fromNormalization) :
    Etale f.fromNormalization := by
  let eN := normalizationSourceIso hp.isoPullback f' (pullback.snd f g)
    hp.isoPullback_hom_snd
  have he : Etale (eN.hom ≫ (pullback.snd f g).fromNormalization) := by
    rw [normalizationSourceIso_hom_over]
    exact h
  let hN : Etale (pullback.snd f g).fromNormalization :=
    (MorphismProperty.cancel_left_of_respectsIso (P := @Etale)
      eN.hom (pullback.snd f g).fromNormalization).mp he
  have hpb : Etale (pullback.snd f.fromNormalization g) :=
    (MorphismProperty.cancel_left_of_respectsIso (P := @Etale)
      (f.normalizationPullback g) (pullback.snd f.fromNormalization g)).mp (by
        rw [Scheme.Hom.normalizationPullback_snd]
        exact hN)
  exact MorphismProperty.of_pullback_snd_of_descendsAlong
    (P := @Etale) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    (f := f.fromNormalization) (g := g) ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ hpb
end AlgebraicGeometry.Scheme.Hom

end
