/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Picard.BaseChange

/-! Focused consumer of the base change of the fppf Picard sheaf along `g : S' ⟶ S` (Kleiman,
Ex. 4.4, p. 27, and Answer 4.4, p. 65), with axiom guards. -/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite
open AlgebraicGeometry Scheme.RelativePicard Scheme.Modules.Invertible

universe u

variable {S S' X : Scheme.{u}} (p : X ⟶ S) (g : S' ⟶ S)

/-- `Pic_{X'/S',(fppf)}(T) ≅ Pic_{X/S,(fppf)}(T)` as abelian groups, for an `S'`-scheme `T` viewed
over `S` through `g`. -/
example (T : Over S') :
    (fppfPicardSheaf (pullback.snd p g)).obj.obj (op T) ≅
      (fppfPicardSheaf p).obj.obj (op ((Over.map g).obj T)) :=
  (fppfPicardSheafBaseChangeIso p g).app (op T)

/-- The presheaf isomorphism underlies the isomorphism of fppf sheaves. -/
example :
    (sheafToPresheaf (Scheme.fppfTopology.over S') AddCommGrpCat.{u + 1}).mapIso
        (fppfPicardSheafBaseChangeSheafIso p g) =
      fppfPicardSheafBaseChangeIso p g :=
  rfl

/-- Naturality along a morphism `i : T₀ ⟶ T` of `S'`-schemes, in the form used for kernels of
restriction maps. -/
example {T₀ T : Over S'} (i : T₀ ⟶ T) :
    (fppfPicardSheaf (pullback.snd p g)).obj.map i.op ≫
        (fppfPicardSheafBaseChangeIso p g).hom.app (op T₀) =
      (fppfPicardSheafBaseChangeIso p g).hom.app (op T) ≫
        (fppfPicardSheaf p).obj.map ((Over.map g).map i).op :=
  fppfPicardSheafBaseChangeIso_hom_naturality p g i.op

/-- Compatibility with the sheafification units. -/
example :
    toFppfPicardSheaf (pullback.snd p g) ≫ (fppfPicardSheafBaseChangeIso p g).hom =
      (relativePicardFunctorBaseChangeIso p g).hom ≫
        Functor.whiskerLeft (Over.map g).op (toFppfPicardSheaf p) :=
  toFppfPicardSheaf_comp_fppfPicardSheafBaseChangeIso_hom p g

/-- The class of a line bundle `L` on `(X ×_S S') ×_{S'} T` goes to the class of its pullback to
`X ×_S T`. -/
example (T : (Over S')ᵒᵖ) (a : PicardGroup (pullback (pullback.snd p g) T.unop.hom)) :
    ((fppfPicardSheafBaseChangeIso p g).hom.app T).hom
        (((toFppfPicardSheaf (pullback.snd p g)).app T).hom (QuotientAddGroup.mk a)) =
      ((toFppfPicardSheaf p).app (op ((Over.map g).obj T.unop))).hom
        (QuotientAddGroup.mk (pullbackClass (pullbackLeftPullbackSndIso p g T.unop.hom).inv a)) :=
  fppfPicardSheafBaseChangeIso_hom_app_toFppfPicardSheaf_mk p g T a

/-- Kernels of restriction maps correspond, as for tangent spaces at the origin. -/
example {T₀ T : Over S'} (i : T₀ ⟶ T)
    (x : ((fppfPicardSheaf (pullback.snd p g)).obj.map i.op).hom.ker) :
    ((fppfPicardSheafBaseChangeKerAddEquiv p g i x : (fppfPicardSheaf p).obj.obj
        (op ((Over.map g).obj T))) =
      ((fppfPicardSheafBaseChangeIso p g).hom.app (op T)).hom x) :=
  fppfPicardSheafBaseChangeKerAddEquiv_apply_coe p g i x

/-- The relative Picard functors: the base change lifts that of the family Picard functors. -/
example :
    quotientProjection (pullback.snd p g) ≫ (relativePicardFunctorBaseChangeIso p g).hom =
      (familyPicardFunctorBaseChangeIso p g).hom ≫
        Functor.whiskerLeft (Over.map g).op (quotientProjection p) :=
  quotientProjection_comp_relativePicardFunctorBaseChangeIso_hom p g

/-- Fppf coverings of an `S'`-scheme are its fppf coverings over `S`. -/
example {T : Over S'} (R : Sieve T) :
    R.functorPushforward (Over.map g) ∈ Scheme.fppfTopology.over S ((Over.map g).obj T) ↔
      R ∈ Scheme.fppfTopology.over S' T :=
  fppf_functorPushforward_over_map_mem_iff g R

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.fppfPicardSheafBaseChangeIso' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms fppfPicardSheafBaseChangeIso

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.relativePicardFunctorBaseChangeIso' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms relativePicardFunctorBaseChangeIso

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.toFppfPicardSheaf_comp_fppfPicardSheafBaseChangeIso_hom' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms toFppfPicardSheaf_comp_fppfPicardSheafBaseChangeIso_hom

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.fppfPicardSheafBaseChangeIso_hom_app_toFppfPicardSheaf_mk' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms fppfPicardSheafBaseChangeIso_hom_app_toFppfPicardSheaf_mk

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.fppfPicardSheafBaseChangeKerAddEquiv' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms fppfPicardSheafBaseChangeKerAddEquiv

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.fppf_functorPushforward_over_map_mem_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms fppf_functorPushforward_over_map_mem_iff
