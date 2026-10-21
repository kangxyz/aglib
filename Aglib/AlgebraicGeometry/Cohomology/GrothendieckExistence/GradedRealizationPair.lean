/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedRealizationMap
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedRealizationNaturality

/-! # Simultaneous coherent realization of an original formal morphism

Both coefficients are constructed on the same actual finite affine cover.
The realized map retains the original coproduct map under direct image;
no separately supplied realization or comparison square is a hypothesis.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Coherent
namespace AlgebraicGeometry.Scheme.Cohomology
variable {A : Type u} [CommRing A] [IsNoetherianRing A]
  {X : Scheme.{u}} [IsLocallyNoetherian X] [X.IsSeparated] [CompactSpace X]
  (f : X ⟶ Spec (CommRingCat.of A)) [LocallyOfFiniteType f] (I : Ideal A)
  {F G : AdicSystem X (idealThickeningIdealSheaf f I)} (φ : F ⟶ G)

/-- Every original formal morphism has coherent graded realizations with the
original direct-image map square. No epimorphism hypothesis is needed. -/
theorem exists_formalGradedRealizationPair :
    ∃ (P Q : (formalGradedSpace f I).CoherentSheaf) (g : P.obj ⟶ Q.obj)
      (eP : (pushforward (formalGradedProjection f I)).obj P.obj ≅ F.gradedUnderlying)
      (eQ : (pushforward (formalGradedProjection f I)).obj Q.obj ≅ G.gradedUnderlying),
      (pushforward (formalGradedProjection f I)).map g ≫ eQ.hom =
        eP.hom ≫ CategoryTheory.Limits.Sigma.map (fun n => F.gradedPieceMap φ n) := by
  obtain ⟨ι, hι, U, hU, _⟩ := exists_formalGradedChartCover_with_base f I
  let : Finite ι := hι
  obtain ⟨P, p, hp, eP, hP⟩ := exists_formalGradedCoherentQuotient_on_cover f I F U hU
  obtain ⟨Q, q, hq, eQ, hQ⟩ := exists_formalGradedCoherentQuotient_on_cover f I G U hU
  let : Epi p := hp
  let : Epi q := hq
  obtain ⟨g, _, hg⟩ :=
    exists_formalGradedRealizationMap_on_cover f I φ U hU P.obj Q.obj p q eP eQ hP hQ
  exact ⟨P, Q, g, formalGradedPushforwardIsoOnCover f I F U hU P.obj p eP hP,
    formalGradedPushforwardIsoOnCover f I G U hU Q.obj q eQ hQ,
    formalGradedPushforwardIsoOnCover_naturality f I φ P.obj Q.obj g U hU
      p q eP eQ hP hQ hg⟩

end AlgebraicGeometry.Scheme.Cohomology
