/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteFlat.FieldRank

/-! Original structural rank without etaleness or reducedness. -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.OverField

universe u

example {k : Type u} [Field k] (X : FScheme k) [IsFinite X.hom] (n : ℕ) :
    Scheme.Hom.HasLocallyFreeRank X.hom n ↔ Scheme.Hom.finiteSchemeDegree k X.hom = n :=
  Scheme.Hom.hasLocallyFreeRank_iff_finiteSchemeDegree_eq X n
