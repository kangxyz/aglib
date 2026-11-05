/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.SourceCover.Images
public import Aglib.AlgebraicGeometry.EtaleCohomology.PullbackIsomorphism
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-! # Original top-chart normalization for source-cover images

For an actual etale chart whose structure morphism is an isomorphism, the
original inverse-image adjunction unit and etale restriction comparison
identify its source-image functor with the unchanged direct image. The native
same-degree derived comparison then closes the top-open induction step.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

variable {X S : Scheme.{u}} (f : X ⟶ S) (U : X.Etale) [IsIso U.hom]

/-- The original adjunction unit identifies an actual isomorphic chart with identity. -/
def etaleProductSheafIsoOfIso : 𝟭 (AbelianSheaf.{u, u + 1} X) ≅ etaleProductSheaf U := by
  let : (inverseImage U.hom).IsEquivalence :=
    (inverseImageEquivalenceOfIso
      (asIso U.hom)).isEquivalence_functor
  exact asIso (inverseImageAdjunction U.hom).unit ≪≫
    Functor.isoWhiskerRight (inverseImageEtaleIso U.hom) (directImage U.hom)

/-- The whole original direct-image functor is recovered from the top source chart. -/
def sourceEtaleImageIsoOfIso : sourceEtaleImage f U ≅ directImage f :=
  Functor.isoWhiskerRight (etaleProductSheafIsoOfIso U).symm (directImage f) ≪≫
    Functor.leftUnitor (directImage f)

/-- The same original natural cohomological degree survives top-chart normalization. -/
def sourceEtaleImageRightDerivedIsoOfIso (q : ℕ) :
    (sourceEtaleImage f U).rightDerived q ≅ higherDirectImage f q :=
  Functor.rightDerivedNatIsoOfAdditive (sourceEtaleImageIsoOfIso f U) q

end AlgebraicGeometry.Scheme.EtaleCohomology
