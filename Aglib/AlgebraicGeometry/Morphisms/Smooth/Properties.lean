/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: R5Lab contributors
-/
module

public import Aglib.AlgebraicGeometry.Properties.Normal.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Topology.KrullDimension

/-!
# General smooth-field theorem interfaces

The original all-fields and arbitrary-dimensional scheme proposition definitions
from `R5Lab.AlgebraicGeometry.Curves.Core` at revision
`95a3772b895fbc19a81684be4ffd519d0fdcd6b3`.
These definitions assert no realization by themselves. Their original proved
suppliers live in `Smooth.Regularity`, `Smooth.Normality` and `Smooth.Dimension`.
`Normal.Basic` is reexported for the original general Core consumers.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

universe u

/-- General smooth-field normality premise, Stacks 056T (33.25.4), using
its ordinary normality consequence. Inspected 2026-10-09; the page has no
correction comments. The proof passes through 056S and 0569. This statement
is retained, not claimed to be proved in the pinned library. -/
def SmoothFieldNormality : Prop :=
  ∀ (K : Type u) [Field K] (X : Scheme.{u}) (f : X ⟶ Spec (.of K)),
    Smooth f → NormalStalks X

/-- General smooth-field regularity of actual local rings, Stacks 056S.
Statement, proof route and comment inspected 2026-10-09. -/
def SmoothFieldRegularity : Prop :=
  ∀ (K : Type u) [Field K] (X : Scheme.{u}) (f : X ⟶ Spec (.of K)),
    Smooth f → ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x)

/-- General relative-to-absolute dimension theorem for nonempty smooth field
schemes. The standard-smooth convention is related to fibre dimension by
Stacks 02G1/02G2 (29.35.12–13), via 10.137.6. Retained general premise,
not a theorem of the pinned library. -/
def SmoothFieldDimension : Prop :=
  ∀ (K : Type u) [Field K] (X : Scheme.{u}) (f : X ⟶ Spec (.of K)) (n : ℕ),
    SmoothOfRelativeDimension n f → Nonempty X → topologicalKrullDim X = n

/-- General closed-point dimension theorem for smooth field schemes.
Stacks 02G1/02G2 and 0A21 (33.20.3(2)); statement and proof inspected
2026-10-09. The 2026 correction to 0A21 concerns specialization notation in
part (9), not part (2). This does not assert dimension n at generic points. -/
def SmoothClosedPointDimension : Prop :=
  ∀ (K : Type u) [Field K] (X : Scheme.{u}) (f : X ⟶ Spec (.of K)) (n : ℕ),
    SmoothOfRelativeDimension n f → ∀ x : X, IsClosed ({x} : Set X) →
      ringKrullDim (X.presheaf.stalk x) = n

end AlgebraicGeometry.Scheme
