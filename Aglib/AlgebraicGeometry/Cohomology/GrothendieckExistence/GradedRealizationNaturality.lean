/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedRealization
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedRealizationMap
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedPushforwardChartMap

/-! # The original pushforward square of realized formal morphisms -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Coherent
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Cohomology
variable {A : Type u} [CommRing A] {X : Scheme.{u}} [IsLocallyNoetherian X]
  (f : X ⟶ Spec (CommRingCat.of A)) (I : Ideal A)
  {F G : AdicSystem X (idealThickeningIdealSheaf f I)} (φ : F ⟶ G)
  (P Q : (formalGradedSpace f I).Modules) (g : P ⟶ Q)

/-- The global realized morphism induces the original coproduct of graded
piece maps under the actual direct-image comparisons. -/
@[reassoc]
theorem formalGradedPushforwardIsoOnCover_naturality [X.IsSeparated]
    {ι : Type u} (U : ι → X.affineOpens) (hU : ∀ x : X, ∃ i, x ∈ (U i).val)
    (p : formalGradedAmbient f I F ⟶ P) (q : formalGradedAmbient f I G ⟶ Q)
    [Epi p] [Epi q] :
    letI (W : X.Opens) : Algebra A Γ(X, W) := formalGradedSectionAlgebra f W
    ∀ (eP : ∀ i, P.restrict (formalGradedChart f I (U i)) ≅
      tilde (R := CommRingCat.of (Γ(X, (U i)) ⊗[A] I.associatedGraded))
        (formalGradedLocalModule f I F (U i)))
    (eQ : ∀ i, Q.restrict (formalGradedChart f I (U i)) ≅
      tilde (R := CommRingCat.of (Γ(X, (U i)) ⊗[A] I.associatedGraded))
        (formalGradedLocalModule f I G (U i)))
    (hP : ∀ i, (Scheme.Modules.restrictFunctor (formalGradedChart f I (U i))).map p ≫ (eP i).hom =
      formalGradedLocalQuotient f I F (U i))
    (hQ : ∀ i, (Scheme.Modules.restrictFunctor (formalGradedChart f I (U i))).map q ≫ (eQ i).hom =
      formalGradedLocalQuotient f I G (U i))
    (_hg : ∀ i, (Scheme.Modules.restrictFunctor (formalGradedChart f I (U i))).map g ≫ (eQ i).hom =
      (eP i).hom ≫ formalGradedLocalMap f I φ (U i)),
    (Scheme.Modules.pushforward (formalGradedProjection f I)).map g ≫
      (formalGradedPushforwardIsoOnCover f I G U hU Q q eQ hQ).hom =
    (formalGradedPushforwardIsoOnCover f I F U hU P p eP hP).hom ≫
      CategoryTheory.Limits.Sigma.map (fun n => F.gradedPieceMap φ n) := by
  let (W : X.Opens) : Algebra A Γ(X, W) := formalGradedSectionAlgebra f W
  intro eP eQ hP hQ hg
  let L := (Scheme.Modules.pushforward (formalGradedProjection f I)).map g ≫
    (formalGradedPushforwardIsoOnCover f I G U hU Q q eQ hQ).hom
  let R := (formalGradedPushforwardIsoOnCover f I F U hU P p eP hP).hom ≫
    CategoryTheory.Limits.Sigma.map (fun n => F.gradedPieceMap φ n)
  have hloc (i : ι) : (Scheme.Modules.restrictFunctor (U i).property.fromSpec).map L =
      (Scheme.Modules.restrictFunctor (U i).property.fromSpec).map R := by
    dsimp only [L, R]
    rw [Functor.map_comp, Functor.map_comp,
      formalGradedPushforwardIsoOnCover_restrict,
      formalGradedPushforwardIsoOnCover_restrict]
    exact formalGradedPushforwardChartIso_naturality f I φ P Q g (U i) (eP i) (eQ i) (hg i)
  have hc : ∀ x : X, ∃ i, ∃ y, (U i).property.fromSpec y = x := by
    intro x
    obtain ⟨i, hi⟩ := hU x
    have hi' : x ∈ Set.range (U i).property.fromSpec := by
      rw [(U i).property.range_fromSpec]
      exact hi
    exact ⟨i, hi'⟩
  let a (i : ι) := (U i).property.fromSpec
  let loc (i : ι) := (Scheme.Modules.restrictFunctor (a i)).map L
  have hcomp : InternalHom.RestrictionHomCompatible a _ _ loc := by
    intro i k
    exact (overlapRestrictIso (a i) (a k)).hom.naturality L
  exact (InternalHom.glueRestrictionHom_unique (fun i => Spec Γ(X, U i)) a hc _ _
    loc hcomp L (fun _ => rfl)).trans
      (InternalHom.glueRestrictionHom_unique (fun i => Spec Γ(X, U i)) a hc _ _
        loc hcomp R (fun i => (hloc i).symm)).symm

end AlgebraicGeometry.Scheme.Cohomology
