/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Finite.Monomorphism

/-! Scheme monomorphism and structural degree detect nilpotents as well as points. -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.OverField

universe u

example {k : Type u} [Field k] {X Y : FScheme k}
    [IsFinite X.hom] [IsFinite Y.hom] (f : X ⟶ Y) [Mono f]
    (hdegree : Scheme.Hom.finiteSchemeDegree k X.hom =
      Scheme.Hom.finiteSchemeDegree k Y.hom) : IsIso f :=
  Scheme.Hom.isIso_of_mono_of_finiteSchemeDegree_eq f hdegree
