/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.LineBundleFamily.UniversalTranslation

/-! Arbitrary, possibly nonreduced parameter tests for the original family. -/

@[expose] public noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open AlgebraicGeometry Scheme.Modules.Invertible Scheme.RelativePicard

universe u

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k] (G : Over (Spec (.of k))) [GrpObj G]
  {D T T' : Over (Spec (.of k))}

example (f : T' ⟶ T) (t : T ⟶ G) (d : T ⟶ D)
    (a : PicardGroup (pullback G.hom D.hom)) :
    pullbackClass ((familyScheme G.hom).map f) (universalTranslationClass G t d a) =
      universalTranslationClass G (f ≫ t) (f ≫ d) a :=
  universalTranslationClass_pullback G f t d a

example (s t : T ⟶ G) (d : T ⟶ D) :
    universalTranslationMorphism G s (𝟙 T) ≫ universalTranslationMorphism G t d =
      universalTranslationMorphism G (s * t) d :=
  universalTranslationMorphism_comp G s t d

example [MonObj D] (t : T ⟶ G) (a : PicardGroup (pullback G.hom D.hom))
    (ha : pullbackClass (lift (𝟙 G) (1 : G ⟶ D)).left a = 0) :
    universalTranslationClass G t (1 : T ⟶ D) a = 0 :=
  universalTranslationClass_parameter_one G t a ha

end
