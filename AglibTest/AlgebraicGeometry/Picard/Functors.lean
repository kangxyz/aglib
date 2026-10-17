/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Picard.Normalized
public import Aglib.AlgebraicGeometry.Picard.Fppf

/-! Focused consumer of the Picard functor layer. The presheaves have the actual Picard
groups as values and the actual additive pullbacks along `pullback.snd`,
`pullback.map` and the origin sections as maps; `Pic_{X/S,(fppf)}` is Mathlib's
sheafification of the relative quotient. Universes are `Scheme.{u}` and
`AddCommGrpCat.{u + 1}`. -/

@[expose] public section

noncomputable section
open CategoryTheory Limits Opposite AlgebraicGeometry
open Scheme.Modules.Invertible Scheme.Modules.Invertible.PullbackTensor.Local
open Scheme.RelativePicard

universe u

variable {S X : Scheme.{u}} (p : X ⟶ S)

example (T : (Over S)ᵒᵖ) : (basePicardFunctor S).obj T = AddCommGrpCat.of (PicardGroup T.unop.left) :=
  rfl

example (T : (Over S)ᵒᵖ) :
    (familyPicardFunctor p).obj T = AddCommGrpCat.of (PicardGroup (pullback p T.unop.hom)) :=
  rfl

example {T T' : (Over S)ᵒᵖ} (f : T ⟶ T') :
    (basePicardFunctor S).map f = AddCommGrpCat.ofHom (pullbackHom f.unop.left) :=
  rfl

example {T T' : (Over S)ᵒᵖ} (f : T ⟶ T') :
    (familyPicardFunctor p).map f = AddCommGrpCat.ofHom (pullbackHom
      (pullback.map p T'.unop.hom p T.unop.hom (𝟙 X) f.unop.left (𝟙 S) (by simp) (by simp))) :=
  rfl

example (T : (Over S)ᵒᵖ) :
    (basePullback p).app T = AddCommGrpCat.ofHom (pullbackHom (pullback.snd p T.unop.hom)) :=
  rfl

example (T : (Over S)ᵒᵖ) :
    (relativePicardFunctor p).obj T = AddCommGrpCat.of
      (PicardGroup (pullback p T.unop.hom) ⧸ (pullbackHom (pullback.snd p T.unop.hom)).range) :=
  rfl

example (T : (Over S)ᵒᵖ) :
    ((quotientProjection p).app T).hom.ker = ((basePullback p).app T).hom.range :=
  quotientProjection_app_ker p T

example : fppfPicardSheaf p =
    (presheafToSheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1}).obj
      (relativePicardFunctor p) :=
  rfl

example : toFppfPicardSheaf p = toSheafify (Scheme.fppfTopology.over S) (relativePicardFunctor p) :=
  rfl

example {T : Scheme.{u}} (a : PicardGroup T) :
    vanishingSieve a ∈ Scheme.zariskiTopology T :=
  vanishingSieve_mem_zariskiTopology a

example : IsIso ((presheafToSheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1}).map
    (quotientProjection p)) :=
  isIso_presheafToSheaf_map_quotientProjection p

example : (presheafToSheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1}).obj
    (familyPicardFunctor p) ≅ fppfPicardSheaf p :=
  fppfFamilyPicardSheafIso p

section Section

variable (o : S ⟶ X) (ho : o ≫ p = 𝟙 S)

example (T : Over S) : originSection p o ho T = pullback.lift (T.hom ≫ o) (𝟙 T.left) (by simp [ho]) :=
  rfl

example (T : (Over S)ᵒᵖ) :
    (originRestriction p o ho).app T = AddCommGrpCat.ofHom (pullbackHom (originSection p o ho T.unop)) :=
  rfl

example : basePullback p ≫ originRestriction p o ho = 𝟙 _ :=
  basePullback_originRestriction p o ho

example (T : (Over S)ᵒᵖ) : Function.Injective ((basePullback p).app T).hom :=
  basePullback_app_injective p o ho T

example (T : (Over S)ᵒᵖ) :
    (normalizedPicardFunctor p o ho).obj T =
      AddCommGrpCat.of (pullbackHom (originSection p o ho T.unop)).ker :=
  rfl

example : (quotientNormalizedIso p o ho).inv = normalizedInclusion p o ho ≫ quotientProjection p :=
  quotientNormalizedIso_inv p o ho

end Section

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.quotientNormalizedIso_inv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms quotientNormalizedIso_inv

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.fppfPicardSheafHomEquiv_apply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms fppfPicardSheafHomEquiv_apply

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.quotientProjection_app_ker' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms quotientProjection_app_ker

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.fppfFamilyPicardSheafIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms fppfFamilyPicardSheafIso
