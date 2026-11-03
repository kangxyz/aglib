/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.ClosedImmersion.RightAdjoint.FlatBaseChange.LiteralQuotient

/-! # Original quotient ideals in a commuting affine-open refinement square

The four original edge actions are retained. These laws concern ordinary
mapped ideals and native quotient pullbacks, not a homology compatibility.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u
namespace AlgebraicGeometry.Scheme.Modules

variable {R S U V : CommRingCat.{u}}
  [Algebra R S] [Algebra R U] [Algebra S V] [Algebra U V]
  (I : Ideal R)
  (hSquare : (algebraMap U V).comp (algebraMap R U) =
    (algebraMap S V).comp (algebraMap R S))

/-- A genuine ambient Cartesian square supplies its original ring equality. -/
theorem affineOpenRefinement_ringSquare_of_isPullback
    (P : IsPullback (Spec.map (CommRingCat.ofHom (algebraMap U V)))
      (Spec.map (CommRingCat.ofHom (algebraMap S V)))
      (Spec.map (CommRingCat.ofHom (algebraMap R U)))
      (Spec.map (CommRingCat.ofHom (algebraMap R S)))) :
    (algebraMap U V).comp (algebraMap R U) =
      (algebraMap S V).comp (algebraMap R S) := by
  have h : (CommRingCat.ofHom (algebraMap R U)) ≫
      (CommRingCat.ofHom (algebraMap U V)) =
      (CommRingCat.ofHom (algebraMap R S)) ≫
      (CommRingCat.ofHom (algebraMap S V)) :=
    Spec.map_injective (by simpa only [Spec.map_comp] using P.w)
  exact congrArg (fun f : R ⟶ V => f.hom) h

include hSquare in
/-- The direct quotient action is the retained original target-branch action. -/
theorem affineOpenRefinement_targetIdeal :
    I.map ((algebraMap S V).comp (algebraMap R S)) =
      (I.map (algebraMap R U)).map (algebraMap U V) := by
  rw [Ideal.map_map, hSquare]

include hSquare in
/-- The actual target vertical quotient has the proved mapped ideal. -/
theorem affineOpenRefinement_targetIdeal_map :
    (I.map (algebraMap R S)).map (algebraMap S V) =
      (I.map (algebraMap R U)).map (algebraMap U V) := by
  rw [Ideal.map_map]
  exact affineOpenRefinement_targetIdeal I hSquare

/-- The original target quotientMap square is genuinely Cartesian. -/
theorem affineOpenRefinement_targetSource_isPullback :
    IsPullback
      (Spec.map (CommRingCat.ofHom (Ideal.quotientMap
        ((I.map (algebraMap R U)).map (algebraMap U V)) (algebraMap S V)
        (literalQuotient_le_comap (I.map (algebraMap R S)) _
          (affineOpenRefinement_targetIdeal_map I hSquare)))))
      (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk ((I.map (algebraMap R U)).map (algebraMap U V)))))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap R S)))))
      (Spec.map (CommRingCat.ofHom (algebraMap S V))) :=
  literalQuotient_isPullback _ _ (affineOpenRefinement_targetIdeal_map I hSquare)

end AlgebraicGeometry.Scheme.Modules
