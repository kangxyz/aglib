/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Topology.KrullDimension
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Aglib.AlgebraicGeometry.Stalk.GenericFiber
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# Conditional dimension family for proper flat DVR schemes

Source: `R5Lab.Aglib.AlgebraicGeometry.KrullDimension.FlatDVR`.
R5 packet revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256: `a6c105afea56fdf2f2f4f4a1eefe0690581d80ddae824372d3e65d8fbe59dde6`.
Actual objects, maps, universes and hypotheses are retained.
Native declaration ownership replaces the source application namespaces.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry
universe u

namespace AlgebraicGeometry.Scheme.FlatDVR

/-- Independent general dimension-formula corollary for actual proper flat DVR
schemes with a literal smooth one-dimensional generic fibre. Stacks 02JT
(Lemma 29.53.4) gives dimension of a dominant closed locally-finite-type map.
The retained corollary includes the actual generic-pullback/function-field
transcendence-degree bridge, dominance from nonempty flatness, DVR dimension
one, and proper closedness. It contains no polygon, minimality or cover result.
No excellence or perfect-residue-field premise is used. -/
def ProperFlatDVRGenericCurveDimension : Prop :=
  ∀ (R F : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field F] [Algebra R F] [IsFractionRing R F]
    (Y : Scheme.{u}) [IsIntegral Y] (π : Y ⟶ Spec (.of R)),
    Flat π → IsProper π →
    SmoothOfRelativeDimension 1
      (pullback.snd π (Scheme.LocalRing.GenericFiber.baseMap R F)) →
    topologicalKrullDim Y = 2

end AlgebraicGeometry.Scheme.FlatDVR
