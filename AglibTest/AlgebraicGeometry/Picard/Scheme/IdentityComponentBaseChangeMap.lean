/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Scheme.IdentityComponentBaseChangeMap

/-!
# Consumer checks for the actual Picard component base-change triangle

The native comparison preserves its original structure map over every field extension.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.RelativePicard

namespace AglibTest.PicardIdentityComponentBaseChangeMap

example {k : Type u} [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k))
    (P : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType P.obj.hom]
    (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙ (fppfPicardSheaf p).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
    (K : Type u) [Field K] [Algebra k K] :
    (picardIdentityComponentBaseChangeIso p P R K).hom ≫
        (picardIdentityComponent
          (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap k K))))
          (LocallyNoetherianOver.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K))) P)
          (baseChangeRepresentableBy p (Spec.map (CommRingCat.ofHom (algebraMap k K))) P R)).hom =
      pullback.snd (picardIdentityComponent p P R).hom
        (Spec.map (CommRingCat.ofHom (algebraMap k K))) :=
  picardIdentityComponentBaseChangeIso_hom_comp p P R K

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.picardIdentityComponentBaseChangeIso_hom_comp' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.RelativePicard.picardIdentityComponentBaseChangeIso_hom_comp

end AglibTest.PicardIdentityComponentBaseChangeMap
