/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.OpenBoundedCandidate
public import Aglib.AlgebraicGeometry.Modules.Restriction.Overlap

/-! # Original pullback coordinates on open overlaps

The overlap comparison is transported from the actual restriction comparison
used by coherent subobject gluing. Thus no separate pullback coherence choice
is introduced, including for ambient module sheaves which are not quasicoherent.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules.Coherent

universe u

/-- The original comparison of iterated restriction with iterated pullback. -/
def iteratedRestrictIsoPullback {X Y Z : Scheme.{u}}
    (q : Z ⟶ Y) (p : Y ⟶ X) [IsOpenImmersion q] [IsOpenImmersion p] :
    restrictFunctor p ⋙ restrictFunctor q ≅ pullback p ⋙ pullback q :=
  Functor.isoWhiskerRight (restrictFunctorIsoPullback p) (restrictFunctor q) ≪≫
    Functor.isoWhiskerLeft (pullback p) (restrictFunctorIsoPullback q)

/-- The original overlap isomorphism in geometric pullback coordinates. -/
def reconstructionOverlapPullbackIso {X U V : Scheme.{u}}
    (p : U ⟶ X) (q : V ⟶ X) [IsOpenImmersion p] [IsOpenImmersion q] :
    pullback p ⋙ pullback (pullback.fst p q) ≅
      pullback q ⋙ pullback (pullback.snd p q) :=
  (iteratedRestrictIsoPullback (pullback.fst p q) p).symm ≪≫
    overlapRestrictIso p q ≪≫
      iteratedRestrictIsoPullback (pullback.snd p q) q

variable {X Y Z : Scheme.{u}}
  [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian Z]
  (q : Z ⟶ Y) (p : Y ⟶ X) [IsOpenImmersion q] [IsOpenImmersion p]
  (K : X.IdealSheafData) (H : X.CoherentSheaf)

/-- Iterated open pullback of the original completion diagram. -/
def iteratedOpenCompletionDiagramIso :
    (idealSheafQuotientTower X K H.obj ⋙ pullback p) ⋙ pullback q ≅
      idealSheafQuotientTower Z ((K.comap p).comap q)
        ((pullback q).obj ((pullback p).obj H.obj)) :=
  Functor.isoWhiskerRight (openIdealPullbackCompletionDiagramIso p K H) (pullback q) ≪≫
    openIdealPullbackCompletionDiagramIso q (K.comap p) ((coherentPullback p).obj H)

/-- The iterated comparison retains the actual original quotient unit. -/
@[reassoc]
theorem iteratedOpenCompletionDiagramIso_unit (n : ℕ) :
    (pullback q).map ((pullback p).map
      ((idealSheafQuotientUnit X (K ^ n)).app H.obj)) ≫
        (iteratedOpenCompletionDiagramIso q p K H).hom.app (op n) =
      (idealSheafQuotientUnit Z ((K.comap p).comap q ^ n)).app
        ((pullback q).obj ((pullback p).obj H.obj)) := by
  change _ ≫ (pullback q).map ((openIdealPullbackCompletionIso p K H).hom.hom.app
    (op n)) ≫ (openIdealPullbackCompletionIso q (K.comap p)
      ((coherentPullback p).obj H)).hom.hom.app (op n) = _
  rw [← Functor.map_comp_assoc, openIdealPullbackCompletionIso_unit p K H n]
  exact openIdealPullbackCompletionIso_unit q (K.comap p) ((coherentPullback p).obj H) n

/-- The inverse comparison retains the unit in the reverse coordinates. -/
@[reassoc]
theorem iteratedOpenCompletionDiagramIso_inv_unit (n : ℕ) :
    (idealSheafQuotientUnit Z ((K.comap p).comap q ^ n)).app
        ((pullback q).obj ((pullback p).obj H.obj)) ≫
      (iteratedOpenCompletionDiagramIso q p K H).inv.app (op n) =
    (pullback q).map ((pullback p).map
      ((idealSheafQuotientUnit X (K ^ n)).app H.obj)) := by
  exact diagramIso_unit_inv (iteratedOpenCompletionDiagramIso q p K H) n _ _
    (iteratedOpenCompletionDiagramIso_unit q p K H n)

/-- The iterated original formal comparison has the original iterated diagram
map followed by the iterated original completion comparison. -/
theorem iteratedOpenReconstructionComparison_app
    {F : AdicSystem X K} (α : F ⟶ (completionFunctor X K).obj H) (n : ℕᵒᵖ) :
    (openReconstructionComparison q (openReconstructionComparison p α)).hom.app n =
      (pullback q).map ((pullback p).map (α.hom.app n)) ≫
        (iteratedOpenCompletionDiagramIso q p K H).hom.app n := by
  change (pullback q).map ((pullback p).map (α.hom.app n) ≫ _) ≫ _ = _
  rw [Functor.map_comp, Category.assoc]
  rfl

end AlgebraicGeometry.Scheme.Modules.Coherent
