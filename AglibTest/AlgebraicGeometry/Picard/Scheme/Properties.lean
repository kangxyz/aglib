/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Scheme.Properties

/-!
# Consumer checks for the basic properties of the Picard scheme

For a closed subscheme `X` of `P^N_A`, `A` Noetherian, flat with geometrically integral fibres, and
its Picard scheme `picardScheme h` (Kleiman, *The Picard scheme*, arXiv:math/0504020v1, Thm 4.8):
the group law and its additivity on locally Noetherian points, the normalized, rigidified and
relative representations (Thm 2.5(2), p. 18), base change with its group law and the uniqueness of
the representing scheme (Ex. 4.4, p. 27), the strata, and the collected statement; axiom guards.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.RelativePicard AlgebraicGeometry.Scheme.RelativePicard.Strata

universe u

namespace AglibTest.PicardSchemeProperties

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {ι : Type u} {X : Scheme.{u}}
  {i : X ⟶ ProjectiveSpace A ι} [IsClosedImmersion i] [Flat (i ≫ toSpec A ι)]
  [GeometricallyIntegral (i ≫ toSpec A ι)] {N : ℕ} {e : ι ≃ Fin (N + 1)}
  (h : FineStrataRepresentableByHQuasiProjective i N e)

/-- **The group law of the Picard scheme**, a commutative group object of `Over (Spec A)`. -/
example : CommGrpObj (picardScheme h).obj :=
  picardCommGrpObj (i ≫ toSpec A ι) (picardScheme h) (picardSchemeRepresentableBy h)

/-- `R` is additive on locally Noetherian points: the product `lift a b ≫ μ` of `T ⟶ P` goes to
the sum. -/
example {T : LocallyNoetherianOver (Spec (.of A))} (a b : T.obj ⟶ (picardScheme h).obj) :
    letI := picardCommGrpObj (i ≫ toSpec A ι) (picardScheme h) (picardSchemeRepresentableBy h);
    (picardSchemeRepresentableBy h).homEquiv
        (ObjectProperty.homMk (CartesianMonoidalCategory.lift a b ≫ MonObj.mul)) =
      (picardSchemeRepresentableBy h).homEquiv'
          (F := (locallyNoetherianOverInclusion (Spec (.of A))).op ⋙
            (fppfPicardSheaf (i ≫ toSpec A ι)).obj) (ObjectProperty.homMk a) +
        (picardSchemeRepresentableBy h).homEquiv'
          (F := (locallyNoetherianOverInclusion (Spec (.of A))).op ⋙
            (fppfPicardSheaf (i ≫ toSpec A ι)).obj) (ObjectProperty.homMk b) :=
  picard_homEquiv_mul _ _ _ a b

section GroupNotation

open scoped CategoryTheory.MonObj

/-- With the notation of `CategoryTheory.MonObj` (where `ι` is the inverse, so the coordinate type
is written `«ι»`): `R` sends `a * b` to the sum, and the points form an abelian group isomorphic to
`Pic_{X/S,(fppf)}(T)`. -/
example {«ι» : Type u} {i : X ⟶ ProjectiveSpace A «ι»} [IsClosedImmersion i]
    [Flat (i ≫ toSpec A «ι»)] [GeometricallyIntegral (i ≫ toSpec A «ι»)] {e : «ι» ≃ Fin (N + 1)}
    (h : FineStrataRepresentableByHQuasiProjective i N e) {T : LocallyNoetherianOver (Spec (.of A))}
    (a b : T.obj ⟶ (picardScheme h).obj) :
    letI := picardCommGrpObj (i ≫ toSpec A «ι») (picardScheme h) (picardSchemeRepresentableBy h);
    (picardSchemeRepresentableBy h).homEquiv (ObjectProperty.homMk (a * b)) =
      (picardSchemeRepresentableBy h).homEquiv'
          (F := (locallyNoetherianOverInclusion (Spec (.of A))).op ⋙
            (fppfPicardSheaf (i ≫ toSpec A «ι»)).obj) (ObjectProperty.homMk a) +
        (picardSchemeRepresentableBy h).homEquiv'
          (F := (locallyNoetherianOverInclusion (Spec (.of A))).op ⋙
            (fppfPicardSheaf (i ≫ toSpec A «ι»)).obj) (ObjectProperty.homMk b) :=
  picard_homEquiv_mul _ _ _ a b

example {«ι» : Type u} {i : X ⟶ ProjectiveSpace A «ι»} [IsClosedImmersion i]
    [Flat (i ≫ toSpec A «ι»)] [GeometricallyIntegral (i ≫ toSpec A «ι»)] {e : «ι» ≃ Fin (N + 1)}
    (h : FineStrataRepresentableByHQuasiProjective i N e) (T : LocallyNoetherianOver (Spec (.of A))) :
    letI := picardCommGrpObj (i ≫ toSpec A «ι») (picardScheme h) (picardSchemeRepresentableBy h);
    Additive (T.obj ⟶ (picardScheme h).obj) ≃+
      (fppfPicardSheaf (i ≫ toSpec A «ι»)).obj.obj (op T.obj) :=
  picardHomAddEquiv _ _ _ T

end GroupNotation

/-- With a section, the normalized and rigidified functors are represented by the Picard scheme. -/
example (o : Spec (.of A) ⟶ X) (ho : o ≫ i ≫ toSpec A ι = 𝟙 _) :
    ((locallyNoetherianOverInclusion (Spec (.of A))).op ⋙
      normalizedPicardFunctor (i ≫ toSpec A ι) o ho ⋙
        CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy (picardScheme h) :=
  picardSchemeNormalizedRepresentableBy h o ho

example (o : Spec (.of A) ⟶ X) (ho : o ≫ i ≫ toSpec A ι = 𝟙 _) :
    ((locallyNoetherianOverInclusion (Spec (.of A))).op ⋙
      rigidifiedPicardFunctor (i ≫ toSpec A ι) o ho).RepresentableBy (picardScheme h) :=
  picardSchemeRigidifiedRepresentableBy h o ho

/-- With `IsSplitEpi p`, the relative functor `P_{X/S}` is represented by the Picard scheme. -/
example [IsSplitEpi (i ≫ toSpec A ι)] :
    ((locallyNoetherianOverInclusion (Spec (.of A))).op ⋙ relativePicardFunctor (i ≫ toSpec A ι) ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy (picardScheme h) :=
  picardSchemeRelativeRepresentableByOfIsSplitEpi h

/-- **Base change**: `P ×_S S'` represents `Pic_{X_{S'}/S',(fppf)}`, with the base-changed group
law, and any representing scheme is isomorphic to it. -/
example {S' : Scheme.{u}} [IsLocallyNoetherian S'] (g : S' ⟶ Spec (.of A)) :
    ((locallyNoetherianOverInclusion S').op ⋙
      (fppfPicardSheaf (pullback.snd (i ≫ toSpec A ι) g)).obj ⋙
        CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy
      (LocallyNoetherianOver.baseChange g (picardScheme h)) :=
  baseChangeRepresentableBy _ g _ (picardSchemeRepresentableBy h)

open scoped CategoryTheory.Obj in
example {S' : Scheme.{u}} [IsLocallyNoetherian S'] (g : S' ⟶ Spec (.of A)) :
    letI := picardCommGrpObj (i ≫ toSpec A ι) (picardScheme h) (picardSchemeRepresentableBy h);
    (picardCommGrpObj (pullback.snd (i ≫ toSpec A ι) g)
        (LocallyNoetherianOver.baseChange g (picardScheme h))
        (baseChangeRepresentableBy _ g _ (picardSchemeRepresentableBy h))).toGrpObj =
      Functor.grpObjObj (F := Over.pullback g) (G := (picardScheme h).obj) :=
  picardCommGrpObj_baseChange_toGrpObj _ g _ _

example {S' : Scheme.{u}} [IsLocallyNoetherian S'] (g : S' ⟶ Spec (.of A))
    {P' : LocallyNoetherianOver S'}
    (e' : ((locallyNoetherianOverInclusion S').op ⋙
      (fppfPicardSheaf (pullback.snd (i ≫ toSpec A ι) g)).obj ⋙
        CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P') :
    P' ≅ LocallyNoetherianOver.baseChange g (picardScheme h) :=
  picardSchemeBaseChangeIso h g e'

/-- The Hilbert-polynomial decomposition of target 5. -/
example : ⨆ φ, picardStratumOpens h φ = ⊤ ∧
    Pairwise (Function.onFun Disjoint (picardStratumOpens h)) ∧
    ∀ φ, IsClopen (picardStratumOpens h φ : Set (picardScheme h).obj.left) :=
  ⟨iSup_picardStratumOpens h, pairwise_disjoint_picardStratumOpens h,
    isClopen_picardStratumOpens h⟩

/-- The collected statement of target 6. -/
example (e : ι ≃ Fin (N + 1)) := exists_representableBy_fppfPicardSheaf_basicProperties i e

end AglibTest.PicardSchemeProperties

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.picardSchemeNormalizedRepresentableBy' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.RelativePicard.picardSchemeNormalizedRepresentableBy

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.picardSchemeRigidifiedRepresentableBy' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.RelativePicard.picardSchemeRigidifiedRepresentableBy

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.picardSchemeRelativeRepresentableByOfIsSplitEpi' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.RelativePicard.picardSchemeRelativeRepresentableByOfIsSplitEpi

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.picardSchemeBaseChangeIso' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.RelativePicard.picardSchemeBaseChangeIso

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.exists_representableBy_fppfPicardSheaf_basicProperties' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.RelativePicard.exists_representableBy_fppfPicardSheaf_basicProperties

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.picardSchemeNormalizedRepresentableBy_homEquiv' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.RelativePicard.picardSchemeNormalizedRepresentableBy_homEquiv

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.picardSchemeRigidifiedRepresentableBy_homEquiv' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.RelativePicard.picardSchemeRigidifiedRepresentableBy_homEquiv

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.picardSchemeRelativeRepresentableByOfIsSplitEpi_homEquiv' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.RelativePicard.picardSchemeRelativeRepresentableByOfIsSplitEpi_homEquiv
