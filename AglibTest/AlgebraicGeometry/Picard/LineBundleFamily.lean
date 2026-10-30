/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.LineBundleFamily.Classifying
public import Aglib.AlgebraicGeometry.Picard.LineBundleFamily.Rigidified

/-! Native family interfaces, including arbitrary nonreduced test schemes and
the original rigidification composition equation. -/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite AlgebraicGeometry
open Scheme.Modules.Invertible Scheme.RelativePicard

universe u

variable {S X : Scheme.{u}} (p : X ⟶ S) (o : S ⟶ X) (ho : o ≫ p = 𝟙 S)

example {T T' : Over S} (f : T' ⟶ T) (a : PicardGroup (pullback p T.hom)) :
    normalizedFamilyClass p o ho T' (pullbackClass ((familyScheme p).map f) a) =
      ((normalizedPicardFunctor p o ho).map f.op).hom
        (normalizedFamilyClass p o ho T a) :=
  normalizedFamilyClass_pullback p o ho f a

example {T₀ T₁ T₂ : Over S} (f : T₀ ⟶ T₁) (g : T₁ ⟶ T₂)
    (P : RigidifiedPair p o ho T₂) :
    (Scheme.Modules.pullback (originSection p o ho T₀)).map
        (RigidifiedPair.mapCompIso f g P).iso.hom ≫
      (RigidifiedPair.map f (RigidifiedPair.map g P)).rigidification.hom =
        (RigidifiedPair.map (f ≫ g) P).rigidification.hom :=
  (RigidifiedPair.mapCompIso f g P).comm

example {P : Scheme.LocallyNoetherianOver S}
    (R : ((Scheme.locallyNoetherianOverInclusion S).op ⋙ normalizedPicardFunctor p o ho ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
    (T : Scheme.LocallyNoetherianOver S) (a : PicardGroup (pullback p T.obj.hom)) :
    pullbackClass ((familyScheme p).map
      (normalizedFamilyClassifyingMap p o ho R T a).hom)
        (normalizedUniversalClass p o ho R).val =
      (normalizedFamilyClass p o ho T.obj a).val :=
  pullback_normalizedUniversalClass p o ho R T a

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.normalizedFamilyClass_pullback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms normalizedFamilyClass_pullback

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.RigidifiedPair.mapCompIso_assoc' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms RigidifiedPair.mapCompIso_assoc

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.pullback_normalizedUniversalClass' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms pullback_normalizedUniversalClass
