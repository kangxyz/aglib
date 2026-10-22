/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.ClosedImmersionReduction.FormalDescent
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.ClosedImmersionReduction.Comparison

/-! # Independent quotient effectivity from actual closed-thickening effectivity

These are intermediate implications. Effectivity on the closed subscheme is
an explicit hypothesis, not an assumed proper-existence conclusion.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Coherent

namespace AlgebraicGeometry.Scheme.Cohomology

universe u

variable {A : Type u} [CommRing A] {X Y : Scheme.{u}}
  [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
  (i : X ⟶ Y) [IsClosedImmersion i]
  (f : Y ⟶ Spec (CommRingCat.of A)) (I : Ideal A)

/-- Effectivity on the actual closed source algebraizes the independent
closed quotient of an ambient formal system. -/
theorem quotient_mem_essImage_of_closedImmersion
    [(completionFunctor X (idealThickeningIdealSheaf (i ≫ f) I)).EssSurj]
    (F : AdicSystem Y (idealThickeningIdealSheaf f I)) :
    (completionFunctor Y (idealThickeningIdealSheaf f I)).essImage
      (AdicSystem.quotient Y (idealThickeningIdealSheaf f I) i.ker F) := by
  let Q := AdicSystem.quotient Y (idealThickeningIdealSheaf f I) i.ker F
  let P := (baseIdealPullbackFunctor i f I).obj Q
  let C := completionFunctor X (idealThickeningIdealSheaf (i ≫ f) I)
  let G := C.objPreimage P
  let : G.obj.IsQuasicoherent := QuasiCoherent.quasicoherent_of_affineCharts _
    (fun R j _ => (G.property R j).1)
  let H : Y.CoherentSheaf := ⟨(pushforward i).obj G.obj,
    QuasiCoherent.FiniteMorphism.affineLocallyFiniteType_pushforward i G.property⟩
  let e : (C.obj G).obj ≅ P.obj :=
    (adicSystemToDiagram X (idealThickeningIdealSheaf (i ≫ f) I)).mapIso
      (C.objObjPreimageIso P)
  let s : ((completionFunctor Y (idealThickeningIdealSheaf f I)).obj H).obj ≅ Q.obj :=
    (closedPushforwardCompletionDiagramIso i f I G.obj).symm ≪≫
      Functor.isoWhiskerRight e (pushforward i) ≪≫
      (closedFormalDescentDiagramIso i f I Q
        (fun n => AdicSystem.quotient_killed Y (idealThickeningIdealSheaf f I) i.ker F n)).symm
  exact ⟨H, ⟨ObjectProperty.isoMk _ s⟩⟩

variable {Z : Scheme.{u}} [IsLocallyNoetherian Z]

/-- The explicit induction hypothesis used by the two-ideal assembly:
original completion is essentially surjective on every actual K-power thickening. -/
def ClosedThickeningCompletionEssSurj (g : Z ⟶ Spec (CommRingCat.of A))
    (J : Ideal A) (K : Z.IdealSheafData) : Prop :=
  ∀ n : ℕ, letI : IsLocallyNoetherian (K ^ n).subscheme :=
      LocallyOfFiniteType.isLocallyNoetherian (K ^ n).subschemeι
    (completionFunctor (K ^ n).subscheme
      (idealThickeningIdealSheaf ((K ^ n).subschemeι ≫ g) J)).EssSurj

/-- Actual thickening effectivity gives every independent-power quotient
in the ambient original completion's essential image, including power zero. -/
theorem quotientPower_mem_essImage_of_thickening_effectivity
    (g : Z ⟶ Spec (CommRingCat.of A)) (J : Ideal A) (K : Z.IdealSheafData)
    (h : ClosedThickeningCompletionEssSurj g J K)
    (F : AdicSystem Z (idealThickeningIdealSheaf g J)) (n : ℕ) :
    (completionFunctor Z (idealThickeningIdealSheaf g J)).essImage
      (AdicSystem.quotient Z (idealThickeningIdealSheaf g J) (K ^ n) F) := by
  let : IsLocallyNoetherian (K ^ n).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (K ^ n).subschemeι
  let := h n
  simpa only [IdealSheafData.ker_subschemeι] using
    quotient_mem_essImage_of_closedImmersion (K ^ n).subschemeι g J F

end AlgebraicGeometry.Scheme.Cohomology
