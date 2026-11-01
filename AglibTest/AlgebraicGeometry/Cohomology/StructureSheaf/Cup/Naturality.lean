/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.StructureSheaf.Cup.Naturality

/-! Consumers retain flatness for the complete cup/algebra pullback,
and its homogeneous map is the original degreewise cohomology pullback. -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.Cohomology

universe u

variable {k : Type u} [Field k] {X Y : FScheme k} (f : X ⟶ Y) [Flat f.left]

example {p q : ℕ} (x : Scheme.structureCohomology k Y p)
    (y : Scheme.structureCohomology k Y q) :
    structureCohomologyPullbackLinear f (p + q) (structureCup Y rfl x y) =
      structureCup X rfl (structureCohomologyPullbackLinear f p x)
        (structureCohomologyPullbackLinear f q y) :=
  structureCup_pullback_of_flat f rfl x y

example (n : ℕ) (x : Scheme.structureCohomology k Y n) :
    structureCohomologyAlgebraPullback f (structureCohomologyInclusion Y n x) =
      structureCohomologyInclusion X n (structureCohomologyPullbackLinear f n x) :=
  structureCohomologyAlgebraPullback_inclusion f n x

example : (structureCohomologyAlgebraPullback f).toLinearMap =
    structureCohomologyAlgebraPullbackLinear f :=
  structureCohomologyAlgebraPullback_toLinearMap f

example : (structureCohomologyGradedPullback f).toAlgHom =
    structureCohomologyAlgebraPullback f :=
  structureCohomologyGradedPullback_toAlgHom f
