/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.SchemeOverField
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# The geometric-fibre cardinality predicate
-/

@[expose] public section


noncomputable section
open CategoryTheory MonoidalCategory
open AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.OverField (Base FScheme)
namespace AlgebraicGeometry.Scheme.OverField
universe u
variable {F : Type u} [Field F]
/-- Every fibre of the actual morphism over an algebraically closed field of the
specified universe has cardinality `n`. Equality with finite locally free rank
is a separate theorem input. -/
def HasGeometricDegree {X Y : FScheme F} (f : X ⟶ Y) (n : ℕ) : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K] (s : Spec (CommRingCat.of K) ⟶ Base F)
    (y : Over.mk s ⟶ Y), Nat.card {x : Over.mk s ⟶ X // x ≫ f = y} = n

end AlgebraicGeometry.Scheme.OverField

/- Migration source: R5Lab/Aglib/AlgebraicGeometry/Morphisms/Finite/GeometricDegree.lean
Frozen packet R5 f8a3314ddecffcada2ec721d26d56a937bed9690.
SHA-256 16390eab7546d35b635ceaeacbbbe36fe54098673e46f3a5ff24928e6b2cdf10.
Native names and imports replace source wrappers; stated conditions and maps are retained. -/
