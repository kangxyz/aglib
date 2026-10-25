/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Representability.LocallyNoetherianBase
public import Aglib.AlgebraicGeometry.Picard.Scheme.Properties

/-!
# Consumer checks for the Picard scheme over a locally Noetherian base

For `S` locally Noetherian, `f : X ⟶ S` flat with geometrically integral fibres and projective
Zariski locally over `S` (`E : ProjectiveSpace.ZariskiLocalClosedImmersion f`), the glued Picard scheme
`E.picardScheme` (Kleiman, *The Picard scheme*, arXiv:math/0504020v1, Thm 4.8(1), p. 27): the
collected statement, separatedness and local finite type, the base change to the charts, and the
generic results on schemes representing `Pic_{X/S,(fppf)}` applied as they stand: the group law
and its additivity, base change along any locally Noetherian `S' ⟶ S` with its group law, the
normalized and rigidified representations with a section (Thm 2.5(2), p. 18), and the tangent
space at the unit over the field points of `S` (Thm 5.11, p. 42); the form for `f` H-projective
Zariski locally over `S`; axiom guards.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.RelativePicard AlgebraicGeometry.Scheme.Cohomology

universe u

namespace AglibTest.PicardLocallyNoetherianBase

variable {S X : Scheme.{u}} [IsLocallyNoetherian S] {f : X ⟶ S} [Flat f] [GeometricallyIntegral f]
  (E : ZariskiLocalClosedImmersion f)

/-- **The collected statement** (Kleiman, Thm 4.8(1), fppf form on locally Noetherian test
schemes). -/
example :
    ∃ (P : LocallyNoetherianOver S)
      (R : ((locallyNoetherianOverInclusion S).op ⋙ (fppfPicardSheaf f).obj ⋙
        CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
      (_ : LocallyOfFiniteType P.obj.hom),
      IsSeparated P.obj.hom ∧
        ∀ (a : E.I) (h : Strata.FineStrataRepresentableByHQuasiProjective (E.c a) (E.N a) (E.e a)),
          ∃ i : LocallyNoetherianOver.baseChange (E.j a) P ≅ picardScheme h,
            ∀ {T : LocallyNoetherianOver (Spec (.of (E.A a)))}
              (g : T ⟶ LocallyNoetherianOver.baseChange (E.j a) P),
              (representableByOfEq (E.c_comp_toSpec a) (picardSchemeRepresentableBy h)).homEquiv
                  (g ≫ i.hom) =
                (baseChangeRepresentableBy f (E.j a) P R).homEquiv g :=
  exists_representableBy_fppfPicardSheaf_of_zariskiLocalClosedImmersion E

/-- The glued Picard scheme is separated and locally of finite type over `S`, by instances. -/
example : IsSeparated E.picardScheme.obj.hom ∧ LocallyOfFiniteType E.picardScheme.obj.hom :=
  ⟨inferInstance, inferInstance⟩

/-- Over the chart `a`, the glued Picard scheme is the Picard scheme of `c a`. -/
example (a : E.I) :
    LocallyNoetherianOver.baseChange (E.j a) E.picardScheme ≅
      picardScheme (Strata.fineStrataRepresentableByHQuasiProjective (E.c a) (E.e a)) :=
  E.picardSchemeBaseChangeIso a

/-- **The group law** of the glued Picard scheme, a commutative group object of `Over S`. -/
example : CommGrpObj E.picardScheme.obj :=
  picardCommGrpObj f E.picardScheme E.picardSchemeRepresentableBy

/-- The representation is additive on locally Noetherian points. -/
example {T : LocallyNoetherianOver S} (a b : T.obj ⟶ E.picardScheme.obj) :
    letI := picardCommGrpObj f E.picardScheme E.picardSchemeRepresentableBy;
    E.picardSchemeRepresentableBy.homEquiv
        (ObjectProperty.homMk (CartesianMonoidalCategory.lift a b ≫ MonObj.mul)) =
      E.picardSchemeRepresentableBy.homEquiv'
          (F := (locallyNoetherianOverInclusion S).op ⋙ (fppfPicardSheaf f).obj)
          (ObjectProperty.homMk a) +
        E.picardSchemeRepresentableBy.homEquiv'
          (F := (locallyNoetherianOverInclusion S).op ⋙ (fppfPicardSheaf f).obj)
          (ObjectProperty.homMk b) :=
  picard_homEquiv_mul _ _ _ a b

/-- **Base change** along any `g : S' ⟶ S` with `S'` locally Noetherian (Kleiman, Ex. 4.4,
p. 27). -/
example {S' : Scheme.{u}} [IsLocallyNoetherian S'] (g : S' ⟶ S) :
    ((locallyNoetherianOverInclusion S').op ⋙ (fppfPicardSheaf (pullback.snd f g)).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy
        (LocallyNoetherianOver.baseChange g E.picardScheme) :=
  baseChangeRepresentableBy f g E.picardScheme E.picardSchemeRepresentableBy

/-- The group law of the base change is the base change of the group law. -/
example {S' : Scheme.{u}} [IsLocallyNoetherian S'] (g : S' ⟶ S) :
    letI := picardCommGrpObj f E.picardScheme E.picardSchemeRepresentableBy;
    (picardCommGrpObj (pullback.snd f g) (LocallyNoetherianOver.baseChange g E.picardScheme)
        (baseChangeRepresentableBy f g E.picardScheme E.picardSchemeRepresentableBy)).toGrpObj =
      Functor.grpObjObj (F := Over.pullback g) (G := E.picardScheme.obj) :=
  picardCommGrpObj_baseChange_toGrpObj _ g _ _

/-- Every scheme representing `Pic_{X_{S'}/S',(fppf)}` is isomorphic to the base change. -/
example {S' : Scheme.{u}} [IsLocallyNoetherian S'] (g : S' ⟶ S) {P' : LocallyNoetherianOver S'}
    (e' : ((locallyNoetherianOverInclusion S').op ⋙ (fppfPicardSheaf (pullback.snd f g)).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P') :
    P' ≅ LocallyNoetherianOver.baseChange g E.picardScheme :=
  e'.uniqueUpToIso (baseChangeRepresentableBy f g E.picardScheme E.picardSchemeRepresentableBy)

/-- **With a section** `o` of `f` (Kleiman, Thm 2.5(2), p. 18): the glued Picard scheme also
represents the normalized and the rigidified Picard functors; `f` is proper since it is projective
Zariski locally over `S`. -/
example (o : S ⟶ X) (ho : o ≫ f = 𝟙 S) :
    ((locallyNoetherianOverInclusion S).op ⋙ normalizedPicardFunctor f o ho ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy E.picardScheme :=
  haveI := E.isProper
  normalizedRepresentableByOfIsProperOfFlatOfGeometricallyIntegral f o ho
    E.picardSchemeRepresentableBy

example (o : S ⟶ X) (ho : o ≫ f = 𝟙 S) :
    ((locallyNoetherianOverInclusion S).op ⋙ rigidifiedPicardFunctor f o ho).RepresentableBy
      E.picardScheme :=
  haveI := E.isProper
  rigidifiedRepresentableByOfIsProperOfFlatOfGeometricallyIntegral f o ho
    E.picardSchemeRepresentableBy

/-- **The tangent space at the unit over a field point** `g : Spec K ⟶ S` (Kleiman, Thm 5.11,
p. 42): `ker(Pic_{X_K/K,(fppf)}(K[ε]) → Pic_{X_K/K,(fppf)}(K)) ≃ₗ[K] H^1(X_K, 𝒪)`, for the
representation of `Pic_{X_K/K,(fppf)}` by the base change of the glued Picard scheme. -/
example (K : Type u) [Field K] (g : Spec (.of K) ⟶ S) :
    letI := tangentKernelModule
      (baseChangeRepresentableBy f g E.picardScheme E.picardSchemeRepresentableBy) K;
    Nonempty (tangentKernel (fppfPicardSheaf (pullback.snd f g)).obj K ≃ₗ[K]
      structureCohomology K (Over.mk (pullback.snd f g)) 1) :=
  haveI := E.isProper
  haveI : IsProper (Over.mk (pullback.snd f g)).hom := inferInstanceAs (IsProper (pullback.snd f g))
  haveI : Flat (Over.mk (pullback.snd f g)).hom := inferInstanceAs (Flat (pullback.snd f g))
  haveI : GeometricallyIntegral (Over.mk (pullback.snd f g)).hom :=
    inferInstanceAs (GeometricallyIntegral (pullback.snd f g))
  ⟨tangentKernelLinearEquivStructureCohomologyOfIsProperOfFlatOfGeometricallyIntegral
    (Over.mk (pullback.snd f g))
    (baseChangeRepresentableBy f g E.picardScheme E.picardSchemeRepresentableBy)⟩

/-- **The property form**: for `f` H-projective Zariski locally over `S`, the conclusion holds for
all embeddings at once. -/
example [IsZariskiLocallyHProjective f] :
    ∃ (P : LocallyNoetherianOver S)
      (R : ((locallyNoetherianOverInclusion S).op ⋙ (fppfPicardSheaf f).obj ⋙
        CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
      (_ : LocallyOfFiniteType P.obj.hom),
      IsSeparated P.obj.hom ∧
        ∀ (E : ZariskiLocalClosedImmersion f) (a : E.I)
          (h : Strata.FineStrataRepresentableByHQuasiProjective (E.c a) (E.N a) (E.e a)),
          ∃ i : LocallyNoetherianOver.baseChange (E.j a) P ≅ picardScheme h,
            ∀ {T : LocallyNoetherianOver (Spec (.of (E.A a)))}
              (g : T ⟶ LocallyNoetherianOver.baseChange (E.j a) P),
              (representableByOfEq (E.c_comp_toSpec a) (picardSchemeRepresentableBy h)).homEquiv
                  (g ≫ i.hom) =
                (baseChangeRepresentableBy f (E.j a) P R).homEquiv g :=
  exists_representableBy_fppfPicardSheaf_of_isZariskiLocallyHProjective

/-- Any representing scheme `P` locally of finite type over `S` is, over each chart, the Picard
scheme of the chart. -/
example {P : LocallyNoetherianOver S} [LocallyOfFiniteType P.obj.hom]
    (R : ((locallyNoetherianOverInclusion S).op ⋙ (fppfPicardSheaf f).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P) (a : E.I) :
    LocallyNoetherianOver.baseChange (E.j a) P ≅ E.chartPicardScheme a :=
  E.baseChangeIsoChartPicardScheme R a

end AglibTest.PicardLocallyNoetherianBase

/-- info: 'AlgebraicGeometry.Scheme.RelativePicard.representableByOfEq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.RelativePicard.representableByOfEq

/-- info:
'AlgebraicGeometry.ProjectiveSpace.ZariskiLocalClosedImmersion.fineStrataRepresentableByHQuasiProjective'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  AlgebraicGeometry.ProjectiveSpace.ZariskiLocalClosedImmersion.fineStrataRepresentableByHQuasiProjective

/-- info: 'AlgebraicGeometry.ProjectiveSpace.ZariskiLocalClosedImmersion.chartPicardScheme' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.ZariskiLocalClosedImmersion.chartPicardScheme

/-- info: 'AlgebraicGeometry.ProjectiveSpace.ZariskiLocalClosedImmersion.chartPicardSchemeRepresentableBy'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.ZariskiLocalClosedImmersion.chartPicardSchemeRepresentableBy

/-- info: 'AlgebraicGeometry.ProjectiveSpace.ZariskiLocalClosedImmersion.picardBaseCover' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.ZariskiLocalClosedImmersion.picardBaseCover

/-- info: 'AlgebraicGeometry.ProjectiveSpace.ZariskiLocalClosedImmersion.picardScheme' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.ZariskiLocalClosedImmersion.picardScheme

/-- info: 'AlgebraicGeometry.ProjectiveSpace.ZariskiLocalClosedImmersion.picardSchemeRepresentableBy'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.ZariskiLocalClosedImmersion.picardSchemeRepresentableBy

/-- info: 'AlgebraicGeometry.ProjectiveSpace.ZariskiLocalClosedImmersion.locallyOfFiniteType_picardScheme'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.ZariskiLocalClosedImmersion.locallyOfFiniteType_picardScheme

/-- info: 'AlgebraicGeometry.ProjectiveSpace.ZariskiLocalClosedImmersion.picardSchemeBaseChangeIso'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.ZariskiLocalClosedImmersion.picardSchemeBaseChangeIso

/-- info:
'AlgebraicGeometry.ProjectiveSpace.ZariskiLocalClosedImmersion.baseChangeIsoChartPicardScheme'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  AlgebraicGeometry.ProjectiveSpace.ZariskiLocalClosedImmersion.baseChangeIsoChartPicardScheme

/-- info:
'AlgebraicGeometry.ProjectiveSpace.ZariskiLocalClosedImmersion.baseChangeIsoChartPicardScheme_homEquiv'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  AlgebraicGeometry.ProjectiveSpace.ZariskiLocalClosedImmersion.baseChangeIsoChartPicardScheme_homEquiv

/-- info: 'AlgebraicGeometry.ProjectiveSpace.ZariskiLocalClosedImmersion.isSeparated_picardScheme'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.ZariskiLocalClosedImmersion.isSeparated_picardScheme

/-- info:
'AlgebraicGeometry.Scheme.RelativePicard.exists_representableBy_fppfPicardSheaf_of_zariskiLocalClosedImmersion'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  AlgebraicGeometry.Scheme.RelativePicard.exists_representableBy_fppfPicardSheaf_of_zariskiLocalClosedImmersion

/-- info:
'AlgebraicGeometry.Scheme.RelativePicard.exists_representableBy_fppfPicardSheaf_of_isZariskiLocallyHProjective'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  AlgebraicGeometry.Scheme.RelativePicard.exists_representableBy_fppfPicardSheaf_of_isZariskiLocallyHProjective
