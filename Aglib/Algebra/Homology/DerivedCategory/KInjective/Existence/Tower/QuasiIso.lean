/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.KInjective.Existence.Tower.RegularStage
public import Aglib.Algebra.Homology.QuasiIso.Transfinite

/-! # The original transfinite replacement augmentation is a quasi-isomorphism -/

@[expose] public noncomputable section

universe w v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.SmallObject

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  {ι : Type w} (A : ι → CochainComplex C ℤ) (hA : ∀ i, (A i).Acyclic)

include hA

/-- Each genuine successor unit is pointwise a quasi-isomorphism. -/
lemma replacementSuccStruct_prop_le_quasiIso :
    (replacementSuccStruct A).prop ≤
      (HomologicalComplex.quasiIso C (.up ℤ)).functorCategory (CochainComplex C ℤ) := by
  rw [SuccStruct.prop, MorphismProperty.ofHoms_le_iff]
  intro G K
  exact replacementStepUnit_quasiIso A hA (G.obj K)

/-- Exact filtered colimits preserve the original augmentation of the actual tower. -/
lemma replacementIterationUnit_quasiIso (J : Type w)
    [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
    (K : CochainComplex C ℤ) : QuasiIso ((replacementIterationUnit A J).app K) := by
  let W := (HomologicalComplex.quasiIso C (.up ℤ)).functorCategory (CochainComplex C ℤ)
  have h := ((replacementSuccStruct A).transfiniteCompositionOfShapeιIteration J).ofLE
    (replacementSuccStruct_prop_le_quasiIso A hA)
  exact (W.transfiniteCompositionsOfShape_le J _ h.mem) K

/-- The chosen regular-stage functor retains its original quasi-isomorphic unit. -/
lemma regularReplacementUnit_quasiIso (G : C) (K : CochainComplex C ℤ) :
    QuasiIso ((regularReplacementUnit A G).app K) :=
  replacementIterationUnit_quasiIso A hA (replacementIndex A G) K

end CochainComplex
