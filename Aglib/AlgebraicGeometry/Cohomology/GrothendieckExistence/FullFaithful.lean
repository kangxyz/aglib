/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.FullFaithfulOriginal

/-! # Full faithfulness of proper coherent completion

The forward functor is the native ideal-sheaf completion functor. No flatness
hypothesis on the coefficient sheaves or the proper morphism is required.
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Coherent

namespace AlgebraicGeometry.Scheme.Cohomology

universe u
variable {A : Type u} [CommRing A] [IsNoetherianRing A]
  (I : Ideal A) [IsAdicComplete I A] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]

section
variable [IsLocallyNoetherian X]

local instance coherentCoefficient_isQuasicoherent (F : X.CoherentSheaf) :
    F.obj.IsQuasicoherent :=
  QuasiCoherent.quasicoherent_of_affineCharts _ (fun R j _ => (F.property R j).1)

/-- Original quotient diagrams recover every coherent coefficient morphism uniquely. -/
def idealPowerCompletionToDiagramFullyFaithful :
    (idealPowerCompletionToDiagram I f).FullyFaithful where
  preimage {F G} η := ObjectProperty.homMk
    (formalHomLift I f F.obj G.obj F.property G.property η)
  map_preimage {F G} η :=
    idealPowerQuotientTowerHom_formalHomLift I f F.obj G.obj F.property G.property η
  preimage_map {F G} φ := by
    apply ObjectProperty.hom_ext
    exact formalHomLift_towerHom I f F.obj G.obj F.property G.property φ.hom

/-- Proper coherent completion is fully faithful over a complete noetherian base,
for the actual base-ideal sheaf and the actual pullback/pushforward quotient functor. -/
def completionFunctorFullyFaithful :
    (completionFunctor X (idealThickeningIdealSheaf f I)).FullyFaithful :=
  Functor.FullyFaithful.ofCompFaithful
    ((idealPowerCompletionToDiagramFullyFaithful I f).ofIso
      (idealPowerCompletionComparison I f))

end

/-- The full-faithfulness theorem with local noetherianity derived from properness,
so the only geometric hypothesis is the original proper morphism. -/
def properCompletionFullyFaithful :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    (completionFunctor X (idealThickeningIdealSheaf f I)).FullyFaithful := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  exact completionFunctorFullyFaithful I f

end AlgebraicGeometry.Scheme.Cohomology
