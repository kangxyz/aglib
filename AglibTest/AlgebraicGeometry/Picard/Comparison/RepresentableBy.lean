/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Picard.Comparison.RepresentableBy

/-! Focused consumer of the transport of a representation of `Pic_{X/S,(fppf)}` on locally
Noetherian test schemes to the normalized, rigidified and relative Picard functors (Kleiman,
Thm 2.5(2), p. 18), with axiom guards. -/

@[expose] public section

noncomputable section

open CategoryTheory Opposite
open AlgebraicGeometry Scheme.RelativePicard

universe u

variable {S X : Scheme.{u}} (p : X ⟶ S) (o : S ⟶ X) (ho : o ≫ p = 𝟙 S)
  {P : Scheme.LocallyNoetherianOver S}
  (e : ((Scheme.locallyNoetherianOverInclusion S).op ⋙ (fppfPicardSheaf p).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)

example [IsLocallyNoetherian S] [IsProper p] [Flat p] [GeometricallyIntegral p]
    {T : Scheme.LocallyNoetherianOver S} (f : T ⟶ P) :
    ((Scheme.locallyNoetherianOverInclusion S).op ⋙ normalizedPicardFunctor p o ho ⋙
        CategoryTheory.forget AddCommGrpCat.{u + 1}).IsRepresentable ∧
      (normalizedRepresentableByOfIsProperOfFlatOfGeometricallyIntegral p o ho e).homEquiv f =
        ((normalizedFppfIsoOfIsProperOfFlatOfGeometricallyIntegral p o ho).inv.app
          (op T.obj)).hom (e.homEquiv f) :=
  ⟨(normalizedRepresentableByOfIsProperOfFlatOfGeometricallyIntegral p o ho e).isRepresentable,
    normalizedRepresentableByOfIsProperOfFlatOfGeometricallyIntegral_homEquiv p o ho e f⟩

example [IsLocallyNoetherian S] [IsProper p] [Flat p] [GeometricallyIntegral p] :
    ((Scheme.locallyNoetherianOverInclusion S).op ⋙
      rigidifiedPicardFunctor p o ho).IsRepresentable :=
  (rigidifiedRepresentableByOfIsProperOfFlatOfGeometricallyIntegral p o ho e).isRepresentable

example [IsSplitEpi p] [IsLocallyNoetherian S] [IsProper p] [Flat p] [GeometricallyIntegral p] :
    ((Scheme.locallyNoetherianOverInclusion S).op ⋙ relativePicardFunctor p ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).IsRepresentable :=
  (relativeRepresentableByOfIsSplitEpiOfIsProperOfFlatOfGeometricallyIntegral p e).isRepresentable

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.normalizedRepresentableByOfIsProperOfFlatOfGeometricallyIntegral' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms normalizedRepresentableByOfIsProperOfFlatOfGeometricallyIntegral

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.rigidifiedRepresentableByOfIsProperOfFlatOfGeometricallyIntegral' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms rigidifiedRepresentableByOfIsProperOfFlatOfGeometricallyIntegral

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.relativeRepresentableByOfIsSplitEpiOfIsProperOfFlatOfGeometricallyIntegral' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms relativeRepresentableByOfIsSplitEpiOfIsProperOfFlatOfGeometricallyIntegral
