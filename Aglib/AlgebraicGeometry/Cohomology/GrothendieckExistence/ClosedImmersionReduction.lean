/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.ClosedImmersionReduction.Annihilation
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.ClosedImmersionReduction.Comparison

/-! # Reduction of coherent effectivity along an actual closed embedding

This is a reduction theorem, not the projective-space existence theorem. Its
sole effectivity premise concerns the ambient scheme, never the source. Once
ambient projective-space effectivity is supplied, this applies to every actual
closed projective embedding without flatness or generation hypotheses.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Coherent

namespace AlgebraicGeometry.Scheme.Cohomology

universe u
variable {A : Type u} [CommRing A] [IsNoetherianRing A]
  (I : Ideal A) [IsAdicComplete I A] {X Y : Scheme.{u}}
  [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
  (i : X ⟶ Y) [IsClosedImmersion i]
  (f : Y ⟶ Spec (CommRingCat.of A)) [IsProper f]

local notation "KX" => idealThickeningIdealSheaf (i ≫ f) I
local notation "KY" => idealThickeningIdealSheaf f I

local instance closedDescentCoefficient_isQuasicoherent (F : X.CoherentSheaf) :
    F.obj.IsQuasicoherent :=
  QuasiCoherent.quasicoherent_of_affineCharts _ (fun R j _ => (F.property R j).1)

/-- Ambient effectivity descends along a genuine closed immersion. The algebraic
coefficient on the closed subscheme is the original pullback of an ambient
algebraization; annihilation is proved by proper completion, not assumed. -/
theorem completionFunctor_essSurj_of_closedImmersion
    [(completionFunctor Y KY).EssSurj] : (completionFunctor X KX).EssSurj where
  mem_essImage F := by
    let C := completionFunctor Y KY
    let D := adicSystemToDiagram Y KY
    let P := closedPushforwardAdicSystem i f I F
    let G := C.objPreimage P
    let e : (C.obj G).obj ≅ F.obj ⋙ pushforward i :=
      D.mapIso (C.objObjPreimageIso P)
    have hG : killedByIdealSheaf i.ker G.obj :=
      killedByIdealSheaf_of_completion_pushforward I i f G
        (fun n => F.obj.obj (op n)) (fun n => e.app (op n))
    let H : X.CoherentSheaf := ⟨(pullback i).obj G.obj,
      QuasiCoherent.affineLocallyFiniteType_pullback i G.property⟩
    let G' : Y.CoherentSheaf := ⟨(pushforward i).obj H.obj,
      QuasiCoherent.FiniteMorphism.affineLocallyFiniteType_pushforward i H.property⟩
    let d : G' ≅ G := ObjectProperty.isoMk _ (closedImmersionDescentIso i G.obj hG)
    let t : idealSheafQuotientTower X KX H.obj ⋙ pushforward i ≅
        F.obj ⋙ pushforward i :=
      closedPushforwardCompletionDiagramIso i f I H.obj ≪≫
        D.mapIso (C.mapIso d) ≪≫ e
    let s : idealSheafQuotientTower X KX H.obj ≅ F.obj :=
      ((fullyFaithfulPushforwardOfClosedImmersion i).whiskeringRight ℕᵒᵖ).preimageIso t
    exact ⟨H, ⟨ObjectProperty.isoMk _ s⟩⟩

end AlgebraicGeometry.Scheme.Cohomology
