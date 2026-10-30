/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.LineBundle.Translation

/-!
# Translation, inversion and arbitrary parameter descent

The class and rigidified-family laws have no reducedness or Noetherian
restriction on test schemes. Classification into the original representative
uses locally Noetherian tests, with no field assumption on the parameter base.
The Picard component is the actual pullback of the original component.
-/

@[expose] public noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite
open AlgebraicGeometry Scheme Scheme.RelativePicard Scheme.Modules.Invertible
open scoped CategoryTheory.MonObj

universe u

namespace AglibTest.LineBundleTranslation

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k] (G : Over (Spec (.of k))) [GrpObj G]
  [IsHProjective G.hom] [GeometricallyIntegral G.hom]

-- Both parameters may vary over an arbitrary, possibly nonreduced scheme.
example {T : Over (Spec (.of k))} (t b : T ⟶ G) (a : PicardGroup G.left) :
    normalizedFamilyClass G.hom η[G].left (Over.w η[G]) T
        (translationFamilyClass G (t * b) a - translationFamilyClass G b a) =
      normalizedFamilyClass G.hom η[G].left (Over.w η[G]) T
        (translationFamilyClass G t a) :=
  normalized_translationFamilyClass_mul_sub G t b a

-- The comparison is an actual rigidified pullback square on those same schemes.
example {T T' : Over (Spec (.of k))} (f : T' ⟶ T) (t b : T ⟶ G)
    (L : LineBundle G.left) :
    (RigidifiedPair.Iso.map f (normalizedTranslationFamilyParameterIso G t b L)).trans
        (normalizedTranslationFamilyPullbackIso G f t L) =
      (normalizedTranslationFamilyParameterPullbackIso G f t b L).trans
        (normalizedTranslationFamilyParameterIso G (f ≫ t) (f ≫ b) L) :=
  normalizedTranslationFamilyParameterIso_naturality G f t b L

variable (P : LocallyNoetherianOver (Spec (.of k)))
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf G.hom).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)

-- A finite-extension double base may be nonreduced. Only local Noetherianity
-- is requested; the map is over the original parameter base, not a new field.
example (T : LocallyNoetherianOver (Spec (.of k))) (b : T.obj ⟶ G)
    (a : PicardGroup G.left) :
    lineBundleClassMorphismTranslatedFamilyOver G P R T b a =
      (Over.pullback T.obj.hom).map (lineBundleClassMorphism G P R a) :=
  lineBundleClassMorphismTranslatedFamilyOver_eq G P R T b a

-- Inversion pullback of the coefficient preserves phi, before any dual geometry.
example (L : LineBundle G.left) :
    lineBundleMorphism G P R (pullbackLineBundle ι[G].left L) =
      lineBundleMorphism G P R L :=
  lineBundleMorphism_pullback_inv G P R L

variable [LocallyOfFiniteType P.obj.hom]

example (a : PicardGroup G.left) :
    letI := picardCommGrpObj G.hom P R
    lineBundleClassMorphismIdentityComponent G P R (pullbackClass ι[G].left a) =
      lineBundleClassMorphismIdentityComponent G P R a :=
  lineBundleClassMorphismIdentityComponent_pullback_inv G P R a

-- Dualizing the coefficient has the opposite operation: inversion of values.
example (L : LineBundle G.left) :
    letI := picardCommGrpObj G.hom P R
    lineBundleMorphism G P R (dualLineBundle G.left L) = (lineBundleMorphism G P R L)⁻¹ :=
  lineBundleMorphism_dual G P R L

end AglibTest.LineBundleTranslation

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.normalized_translationFamilyClass_mul_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.RelativePicard.normalized_translationFamilyClass_mul_sub

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.normalizedTranslationFamilyParameterPullbackIso_comp' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.RelativePicard.normalizedTranslationFamilyParameterPullbackIso_comp

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.lineBundleClassMorphismTranslatedFamilyOver_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.RelativePicard.lineBundleClassMorphismTranslatedFamilyOver_eq

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.lineBundleClassMorphismIdentityComponent_pullback_inv' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.RelativePicard.lineBundleClassMorphismIdentityComponent_pullback_inv
