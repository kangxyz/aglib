/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Comparison.Isomorphism
public import Aglib.AlgebraicGeometry.Properties.Noetherian.LocallyNoetherianOver

/-!
# One representing scheme for the normalized, rigidified and relative Picard functors

Let `S` be locally Noetherian and `p : X ⟶ S` proper and flat with geometrically integral fibres.
Let `e` be a representation of the fppf Picard sheaf `Pic_{X/S,(fppf)}` on locally Noetherian test
schemes by `P : Scheme.LocallyNoetherianOver S`. Then `P` also represents, on locally Noetherian
test schemes:

* for a section `o` of `p` (`o ≫ p = 𝟙 S`), the normalized Picard functor
  `T ↦ ker(o_T^* : Pic(X ×_S T) → Pic(T))`
  (`normalizedRepresentableByOfIsProperOfFlatOfGeometricallyIntegral`) and the rigidified Picard
  functor of isomorphism classes of pairs `(L, u)` with `u : O_T ≅ o_T^* L`
  (`rigidifiedRepresentableByOfIsProperOfFlatOfGeometricallyIntegral`);
* if `p` has a section (`IsSplitEpi p`), the relative Picard functor
  `P_{X/S}(T) = Pic(X ×_S T) / Pic(T)`
  (`relativeRepresentableByOfIsSplitEpiOfIsProperOfFlatOfGeometricallyIntegral`).

Each representation is `e` composed with the inverse of a comparison isomorphism of functors on
all of `Over S`, restricted to locally Noetherian test schemes:
`normalizedFppfIsoOfIsProperOfFlatOfGeometricallyIntegral`,
`rigidifiedFppfIsoOfIsProperOfFlatOfGeometricallyIntegral` and
`relativeFppfIsoOfIsSplitEpiOfIsProperOfFlatOfGeometricallyIntegral` (Kleiman, *The Picard
scheme*, arXiv:math/0504020v1, Thm 2.5(2), p. 18, with Def. 2.8 and Lemma 2.9, p. 19, for
rigidified pairs; [Stacks 0B9N](https://stacks.math.columbia.edu/tag/0B9N)). The representation
`e` is an explicit argument; its existence is not proved here.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.RelativePicard

variable {S X : Scheme.{u}} (p : X ⟶ S) (o : S ⟶ X) (ho : o ≫ p = 𝟙 S)
  {P : LocallyNoetherianOver S}
  (e : ((locallyNoetherianOverInclusion S).op ⋙ (fppfPicardSheaf p).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)

/-- **The normalized Picard functor is represented by the same scheme.** For `S` locally
Noetherian, `p` proper and flat with geometrically integral fibres, and a section `o`, a
representation of `Pic_{X/S,(fppf)}` on locally Noetherian test schemes by `P` gives one of the
normalized Picard functor `T ↦ ker(o_T^*)` by `P`. -/
def normalizedRepresentableByOfIsProperOfFlatOfGeometricallyIntegral [IsLocallyNoetherian S]
    [IsProper p] [Flat p] [GeometricallyIntegral p] :
    ((locallyNoetherianOverInclusion S).op ⋙ normalizedPicardFunctor p o ho ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P :=
  e.ofIso (Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight
    (normalizedFppfIsoOfIsProperOfFlatOfGeometricallyIntegral p o ho).symm _))

theorem normalizedRepresentableByOfIsProperOfFlatOfGeometricallyIntegral_homEquiv
    [IsLocallyNoetherian S] [IsProper p] [Flat p] [GeometricallyIntegral p]
    {T : LocallyNoetherianOver S} (f : T ⟶ P) :
    (normalizedRepresentableByOfIsProperOfFlatOfGeometricallyIntegral p o ho e).homEquiv f =
      ((normalizedFppfIsoOfIsProperOfFlatOfGeometricallyIntegral p o ho).inv.app
        (op T.obj)).hom (e.homEquiv f) :=
  rfl

/-- **The rigidified Picard functor is represented by the same scheme.** Under the hypotheses of
`normalizedRepresentableByOfIsProperOfFlatOfGeometricallyIntegral`, `P` represents the functor of
isomorphism classes of line bundles rigidified along the section `o`, on locally Noetherian test
schemes. -/
def rigidifiedRepresentableByOfIsProperOfFlatOfGeometricallyIntegral [IsLocallyNoetherian S]
    [IsProper p] [Flat p] [GeometricallyIntegral p] :
    ((locallyNoetherianOverInclusion S).op ⋙ rigidifiedPicardFunctor p o ho).RepresentableBy P :=
  e.ofIso (Functor.isoWhiskerLeft _
    (rigidifiedFppfIsoOfIsProperOfFlatOfGeometricallyIntegral p o ho).symm)

theorem rigidifiedRepresentableByOfIsProperOfFlatOfGeometricallyIntegral_homEquiv
    [IsLocallyNoetherian S] [IsProper p] [Flat p] [GeometricallyIntegral p]
    {T : LocallyNoetherianOver S} (f : T ⟶ P) :
    (rigidifiedRepresentableByOfIsProperOfFlatOfGeometricallyIntegral p o ho e).homEquiv f =
      (rigidifiedFppfIsoOfIsProperOfFlatOfGeometricallyIntegral p o ho).inv.app (op T.obj)
        (e.homEquiv f) :=
  rfl

/-- **The relative Picard functor is represented by the same scheme** when `p` has a section
(`IsSplitEpi p`): under the hypotheses of
`normalizedRepresentableByOfIsProperOfFlatOfGeometricallyIntegral`, `P` represents
`P_{X/S}(T) = Pic(X ×_S T) / Pic(T)` on locally Noetherian test schemes. -/
def relativeRepresentableByOfIsSplitEpiOfIsProperOfFlatOfGeometricallyIntegral [IsSplitEpi p]
    [IsLocallyNoetherian S] [IsProper p] [Flat p] [GeometricallyIntegral p] :
    ((locallyNoetherianOverInclusion S).op ⋙ relativePicardFunctor p ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P :=
  e.ofIso (Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight
    (relativeFppfIsoOfIsSplitEpiOfIsProperOfFlatOfGeometricallyIntegral p).symm _))

theorem relativeRepresentableByOfIsSplitEpiOfIsProperOfFlatOfGeometricallyIntegral_homEquiv
    [IsSplitEpi p] [IsLocallyNoetherian S] [IsProper p] [Flat p] [GeometricallyIntegral p]
    {T : LocallyNoetherianOver S} (f : T ⟶ P) :
    (relativeRepresentableByOfIsSplitEpiOfIsProperOfFlatOfGeometricallyIntegral p e).homEquiv f =
      ((relativeFppfIsoOfIsSplitEpiOfIsProperOfFlatOfGeometricallyIntegral p).inv.app
        (op T.obj)).hom (e.homEquiv f) :=
  rfl

end AlgebraicGeometry.Scheme.RelativePicard
