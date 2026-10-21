/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedRealizationPair
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.RelationGraded
public import Aglib.CategoryTheory.Abelian.CoproductKernelTransport

/-! # Coherent realization of the original graded relation kernels

The coefficient is the actual kernel of a realized graded morphism. Exact
coproducts and the original direct-image kernel comparison identify its
pushforward with the original ordinary relation pieces. The relation system
is not assumed cartesian or generated in degree zero.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Coherent
open AlgebraicGeometry.Scheme.Modules.Coherent.AdicSystem
namespace AlgebraicGeometry.Scheme.Cohomology
variable {A : Type u} [CommRing A] [IsNoetherianRing A]
  {X : Scheme.{u}} [IsLocallyNoetherian X] [X.IsSeparated] [CompactSpace X]
  (f : X ⟶ Spec (CommRingCat.of A)) [LocallyOfFiniteType f] (I : Ideal A)
  {F G : AdicSystem X (idealThickeningIdealSheaf f I)} (φ : F ⟶ G)

/-- Actual ordinary relation pieces admit a coherent graded realization,
without an adic relation-system, generation or realization hypothesis. -/
theorem exists_formalGradedRelationRealization :
    ∃ K : (formalGradedSpace f I).CoherentSheaf,
      Nonempty ((pushforward (formalGradedProjection f I)).obj K.obj ≅
        ∐ relationGradedPiece φ) := by
  obtain ⟨P, Q, g, eP, eQ, h⟩ := exists_formalGradedRealizationPair f I φ
  let K : (formalGradedSpace f I).CoherentSheaf :=
    ⟨kernel g, (QuasiCoherent.affineLocallyFiniteType (formalGradedSpace f I)).prop_kernel
      g P.property Q.property⟩
  refine ⟨K, ⟨?_⟩⟩
  exact mapKernelCoproductIso (pushforward (formalGradedProjection f I))
    (fun n => F.gradedPieceMap φ n) (relationGradedPieceIso φ) g eP eQ h

end AlgebraicGeometry.Scheme.Cohomology
