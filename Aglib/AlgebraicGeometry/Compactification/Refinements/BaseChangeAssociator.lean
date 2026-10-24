/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.BaseChange
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-!
# Original pullback associators for three base changes

Both parenthesizations use the native pullback-pasting isomorphism. Equality is
proved from the original two projections, including the base-associativity
identification supplied by `pullback.congrHom`. This applies equally to source
schemes and to unnormalized compactification ambients.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom.DenseCompactification

variable {X S T U V : Scheme.{u}} (f : X ⟶ S) (b : T ⟶ S) (c : U ⟶ T) (d : V ⟶ U)

/-- First collapse the two outer pullbacks, then the inner pullback. -/
def tripleSourceLeft : pullback d (pullback.fst c (pullback.fst b f)) ≅
    pullback (d ≫ c ≫ b) f :=
  pullbackRightPullbackFstIso c (pullback.fst b f) d ≪≫
    pullbackRightPullbackFstIso b f (d ≫ c) ≪≫
      pullback.congrHom (Category.assoc d c b) rfl

/-- The original pullback map induced by the inner native associator. -/
def tripleSourceInnerMap : pullback d (pullback.fst c (pullback.fst b f)) ⟶
    pullback d (pullback.fst (c ≫ b) f) :=
  pullback.map d (pullback.fst c (pullback.fst b f)) d (pullback.fst (c ≫ b) f)
    (𝟙 V) (pullbackRightPullbackFstIso b f c).hom (𝟙 U)
    ((Category.comp_id _).trans (Category.id_comp _).symm)
    ((Category.comp_id _).trans (pullbackRightPullbackFstIso_hom_fst b f c).symm)

instance tripleSourceInnerMap_isIso : IsIso (tripleSourceInnerMap f b c d) :=
  inferInstanceAs (IsIso
    (pullback.map d (pullback.fst c (pullback.fst b f)) d (pullback.fst (c ≫ b) f)
      (𝟙 V) (pullbackRightPullbackFstIso b f c).hom (𝟙 U)
      ((Category.comp_id _).trans (Category.id_comp _).symm)
      ((Category.comp_id _).trans (pullbackRightPullbackFstIso_hom_fst b f c).symm)))

/-- First collapse the inner pullbacks, then the outer pullback. -/
def tripleSourceRight : pullback d (pullback.fst c (pullback.fst b f)) ≅
    pullback (d ≫ c ≫ b) f :=
  asIso (tripleSourceInnerMap f b c d) ≪≫ pullbackRightPullbackFstIso (c ≫ b) f d

@[reassoc (attr := simp)]
lemma tripleSourceLeft_hom_fst :
    (tripleSourceLeft f b c d).hom ≫ pullback.fst (d ≫ c ≫ b) f =
      pullback.fst d (pullback.fst c (pullback.fst b f)) := by
  simp [tripleSourceLeft, pullback.congrHom_hom, pullback.map, Category.assoc,
    pullback.lift_fst]

@[reassoc (attr := simp)]
lemma tripleSourceLeft_hom_snd :
    (tripleSourceLeft f b c d).hom ≫ pullback.snd (d ≫ c ≫ b) f =
      pullback.snd d (pullback.fst c (pullback.fst b f)) ≫
        pullback.snd c (pullback.fst b f) ≫ pullback.snd b f := by
  simp [tripleSourceLeft, pullback.congrHom_hom, pullback.map, Category.assoc,
    pullback.lift_snd]

@[reassoc (attr := simp)]
lemma tripleSourceRight_hom_fst :
    (tripleSourceRight f b c d).hom ≫ pullback.fst (d ≫ c ≫ b) f =
      pullback.fst d (pullback.fst c (pullback.fst b f)) := by
  simp [tripleSourceRight, tripleSourceInnerMap, pullback.map, Category.assoc,
    pullback.lift_fst]

@[reassoc (attr := simp)]
lemma tripleSourceRight_hom_snd :
    (tripleSourceRight f b c d).hom ≫ pullback.snd (d ≫ c ≫ b) f =
      pullback.snd d (pullback.fst c (pullback.fst b f)) ≫
        pullback.snd c (pullback.fst b f) ≫ pullback.snd b f := by
  simp [tripleSourceRight, tripleSourceInnerMap, pullback.map, Category.assoc,
    pullback.lift_snd_assoc]

/-- The original source and ambient pullback associators obey triple associativity. -/
lemma tripleSourceIso_assoc : tripleSourceLeft f b c d = tripleSourceRight f b c d := by
  apply Iso.ext
  apply pullback.hom_ext
  · exact (tripleSourceLeft_hom_fst f b c d).trans (tripleSourceRight_hom_fst f b c d).symm
  · exact (tripleSourceLeft_hom_snd f b c d).trans (tripleSourceRight_hom_snd f b c d).symm

end AlgebraicGeometry.Scheme.Hom.DenseCompactification
