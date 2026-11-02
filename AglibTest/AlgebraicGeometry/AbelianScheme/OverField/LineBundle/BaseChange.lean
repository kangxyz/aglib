/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.LineBundle.BaseChange

/-!
# Original line-bundle morphisms under arbitrary field extension

The original supplied representative is pulled back once. No algebraic
closedness, finite-extension assumption, alternate representative or dual
smoothness input appears in this consumer.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.RelativePicard
open AlgebraicGeometry.Scheme.Modules.Invertible

universe u

namespace AglibTest.LineBundleFieldBaseChange

example {k K : Type u} [Field k] [Field K]
    (s : Spec (.of K) ⟶ Spec (.of k)) (G : Over (Spec (.of k))) [GrpObj G]
    [IsProper G.hom] [Flat G.hom] [GeometricallyIntegral G.hom]
    (P : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType P.obj.hom]
    (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
      (fppfPicardSheaf G.hom).obj ⋙
        CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
    (L : LineBundle G.left) :
    let G' := (Over.pullback s).obj G
    letI : GrpObj G' := Functor.grpObjObj
    letI : IsProper G'.hom := by change IsProper (pullback.snd G.hom s); infer_instance
    letI : Flat G'.hom := by change Flat (pullback.snd G.hom s); infer_instance
    letI : GeometricallyIntegral G'.hom := by
      change GeometricallyIntegral (pullback.snd G.hom s)
      infer_instance
    lineBundleMorphism G' (LocallyNoetherianOver.baseChange s P)
        (baseChangeRepresentableBy G.hom s P R)
        (pullbackLineBundle (pullback.fst G.hom s) L) =
      (Over.pullback s).map (lineBundleMorphism G P R L) :=
  lineBundleMorphism_baseChange s G P R L

end AglibTest.LineBundleFieldBaseChange

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.lineBundleClassMorphism_baseChange' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.RelativePicard.lineBundleClassMorphism_baseChange

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.lineBundleMorphism_baseChange' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.RelativePicard.lineBundleMorphism_baseChange
