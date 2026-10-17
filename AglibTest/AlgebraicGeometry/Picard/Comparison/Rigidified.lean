/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Picard.Comparison.Rigidified

/-! Focused consumer of rigidified pairs (Kleiman, *The Picard scheme*, arXiv:math/0504020v1,
Def. 2.8, Lemmas 2.9 and 2.10, p. 19). The pairs consist of an actual line bundle on the
actual fibre product `pullback p T.hom` and an isomorphism of its pullback along the actual
origin section with the structure module; the comparison is with the committed normalized and
relative Picard functors. Universes are `Scheme.{u}` and `Type (u + 1)`. -/

@[expose] public section

noncomputable section
open CategoryTheory Limits Opposite AlgebraicGeometry
open Scheme.Modules.Invertible Scheme.RelativePicard

universe u

variable {S X : Scheme.{u}} (p : X ⟶ S) (o : S ⟶ X) (ho : o ≫ p = 𝟙 S)

example (T : Over S) (P : RigidifiedPair p o ho T) : LineBundle (pullback p T.hom) := P.bundle

example (T : Over S) (P : RigidifiedPair p o ho T) :
    (Scheme.Modules.pullback (originSection p o ho T)).obj P.bundle.val ≅
      (SheafOfModules.unit T.left.ringCatSheaf : T.left.Modules) :=
  P.rigidification

example (T : (Over S)ᵒᵖ) :
    (rigidifiedPicardFunctor p o ho).obj T =
      Quotient (RigidifiedPair.setoid (p := p) (o := o) (ho := ho) T.unop) :=
  rfl

example {T T' : Over S} (f : T' ⟶ T) (P : RigidifiedPair p o ho T) :
    (RigidifiedPair.map f P).bundle = pullbackLineBundle ((familyScheme p).map f) P.bundle :=
  rfl

example {T T' : Over S} (f : T' ⟶ T) {P Q : RigidifiedPair p o ho T}
    (φ : RigidifiedPair.Iso P Q) :
    (RigidifiedPair.Iso.map f φ).iso =
      (Scheme.Modules.pullback ((familyScheme p).map f)).mapIso φ.iso :=
  rfl

example : rigidifiedPicardFunctor p o ho ≅
    normalizedPicardFunctor p o ho ⋙ CategoryTheory.forget AddCommGrpCat :=
  rigidifiedNormalizedIso p o ho

example {T : (Over S)ᵒᵖ} (P : RigidifiedPair p o ho T.unop) :
    ((rigidifiedNormalizedIso p o ho).hom.app T (Quotient.mk _ P)).val = classOf _ P.bundle :=
  rfl

example {T : (Over S)ᵒᵖ} (P : RigidifiedPair p o ho T.unop) :
    (rigidifiedRelativeIso p o ho).hom.app T (Quotient.mk _ P) =
      (QuotientAddGroup.mk (classOf _ P.bundle) :
        (familyPicardFunctor p).obj T ⧸ baseImage p T) :=
  rigidifiedRelativeIso_hom_app_mk p o ho P

example {T : Over S} [IsIso (pullback.snd p T.hom).c] {P : RigidifiedPair p o ho T}
    (φ : RigidifiedPair.Iso P P) : φ = RigidifiedPair.Iso.refl P :=
  RigidifiedPair.Iso.eq_refl_of_isIso_c p o ho φ

example [IsLocallyNoetherian S] [IsProper p] [Flat p] [GeometricallyIntegral p] {T : Over S}
    {P Q : RigidifiedPair p o ho T} (φ ψ : RigidifiedPair.Iso P Q) : φ = ψ :=
  RigidifiedPair.Iso.eq_of_isProper_of_flat_of_geometricallyIntegral p o ho φ ψ

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.rigidifiedNormalizedIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms rigidifiedNormalizedIso

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.rigidifiedRelativeIso_hom_app_mk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms rigidifiedRelativeIso_hom_app_mk

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.RigidifiedPair.Iso.eq_of_isIso_c' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms RigidifiedPair.Iso.eq_of_isIso_c

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.RigidifiedPair.Iso.eq_of_isProper_of_flat_of_geometricallyIntegral' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms RigidifiedPair.Iso.eq_of_isProper_of_flat_of_geometricallyIntegral

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.RigidifiedPair.Iso.map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms RigidifiedPair.Iso.map
