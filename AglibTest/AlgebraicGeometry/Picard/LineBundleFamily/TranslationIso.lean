/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.LineBundleFamily.TranslationIso

/-! # Same-map canonical shear and original Picard translated class -/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open Scheme.RelativePicard Scheme.Modules.Invertible
open scoped CategoryTheory.MonObj

universe u

attribute [local instance] Over.cartesianMonoidalCategory

example {k : Type u} [Field k] (G : Over (Spec (.of k))) [GrpObj G]
    {T : Over (Spec (.of k))} (t : T ⟶ G) :
    translationFamilyMorphism G t = (GrpObj.translationFamily G t).hom ≫ fst G T :=
  translationFamilyMorphism_eq_translationFamily_hom_fst G t

example {k : Type u} [Field k] (G : Over (Spec (.of k))) [GrpObj G]
    {T : Over (Spec (.of k))} (t : T ⟶ G) (a : PicardGroup G.left) :
    translationFamilyClass G t a =
      pullbackClass (GrpObj.translationFamily G t).hom.left
        (pullbackClass (fst G T).left a) - pullbackClass (fst G T).left a :=
  translationFamilyClass_eq_translationFamily_pullback G t a

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.translationFamilyClass_eq_translationFamily_pullback' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.RelativePicard.translationFamilyClass_eq_translationFamily_pullback
