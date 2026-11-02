/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Normalization.Relative

/-!
# Composition of the original normalization base-change comparisons

This is a categorical compatibility lemma for native relative normalization.
It does not assert normalization compatibility with arbitrary flat morphisms.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The actual comparison for two successive base changes agrees with the
composite comparison, through the original source normalization isomorphism. -/
theorem normalizationPullback_comp
    {X S Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] :
    (pullback.snd f g).normalizationPullback h ≫
      pullback.map (pullback.snd f g).fromNormalization h
        (pullback.snd f.fromNormalization g) h
        (f.normalizationPullback g) (𝟙 Z) (𝟙 Y) (by simp) (by simp) ≫
      (pullbackLeftPullbackSndIso f.fromNormalization g h).hom =
    (normalizationSourceIso (pullbackLeftPullbackSndIso f g h)
      (pullback.snd (pullback.snd f g) h) (pullback.snd f (h ≫ g)) (by simp)).hom ≫
      f.normalizationPullback (h ≫ g) := by
  apply normalization.hom_ext (pullback.snd (pullback.snd f g) h) _ _
    (pullback.snd f.fromNormalization (h ≫ g))
  · apply pullback.hom_ext
    · simp [Category.assoc, pullback.map, normalizationSourceIso_hom_generic_assoc]
    · simp [Category.assoc, pullback.map]
  · simp [Category.assoc, pullback.map]
  · simp [Category.assoc]

/-- The normalization comparison for a composite base change is invertible
when the two successive original comparisons are invertible. -/
theorem normalizationPullback_isIso_comp
    {X S Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f]
    [IsIso (f.normalizationPullback g)]
    [IsIso ((pullback.snd f g).normalizationPullback h)] :
    IsIso (f.normalizationPullback (h ≫ g)) := by
  let p := pullback.snd f g
  let q := pullback.snd p h
  let r := pullback.snd f (h ≫ g)
  let e := normalizationSourceIso (pullbackLeftPullbackSndIso f g h) q r (by simp [q, r, p])
  let k := pullback.map p.fromNormalization h (pullback.snd f.fromNormalization g) h
    (f.normalizationPullback g) (𝟙 Z) (𝟙 Y) (by simp [p]) (by simp)
  let a := p.normalizationPullback h ≫ k ≫
    (pullbackLeftPullbackSndIso f.fromNormalization g h).hom
  have ha : a = e.hom ≫ f.normalizationPullback (h ≫ g) :=
    normalizationPullback_comp f g h
  have : IsIso a := by dsimp only [a, k, p]; infer_instance
  have : IsIso (e.hom ≫ f.normalizationPullback (h ≫ g)) := by rw [← ha]; infer_instance
  exact IsIso.of_isIso_comp_left e.hom _

/-- If the comparison after the second base change and the composite
comparison are invertible, the base change of the first comparison is
invertible. This cancels actual maps, not abstract isomorphic objects. -/
theorem normalizationPullback_isIso_baseChange_of_comp
    {X S Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f]
    [IsIso ((pullback.snd f g).normalizationPullback h)]
    [IsIso (f.normalizationPullback (h ≫ g))] :
    IsIso (pullback.map (pullback.snd f g).fromNormalization h
      (pullback.snd f.fromNormalization g) h
      (f.normalizationPullback g) (𝟙 Z) (𝟙 Y) (by simp) (by simp)) := by
  let k := pullback.map (pullback.snd f g).fromNormalization h
    (pullback.snd f.fromNormalization g) h
    (f.normalizationPullback g) (𝟙 Z) (𝟙 Y) (by simp) (by simp)
  let e := pullbackLeftPullbackSndIso f.fromNormalization g h
  have H : IsIso ((pullback.snd f g).normalizationPullback h ≫ k ≫ e.hom) := by
    change IsIso ((pullback.snd f g).normalizationPullback h ≫
      pullback.map (pullback.snd f g).fromNormalization h
        (pullback.snd f.fromNormalization g) h
        (f.normalizationPullback g) (𝟙 Z) (𝟙 Y) (by simp) (by simp) ≫
      (pullbackLeftPullbackSndIso f.fromNormalization g h).hom)
    rw [normalizationPullback_comp]
    infer_instance
  let := H
  have : IsIso (k ≫ e.hom) :=
    IsIso.of_isIso_comp_left ((pullback.snd f g).normalizationPullback h) _
  exact IsIso.of_isIso_comp_right k e.hom

end AlgebraicGeometry.Scheme.Hom
