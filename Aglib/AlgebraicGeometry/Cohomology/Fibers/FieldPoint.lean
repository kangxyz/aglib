/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Fibers.FieldPoint.Core
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.FieldExtension

/-! # Field extension comparison for original field-point dimensions -/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Cohomology

variable {K : Type u} [Field K] {Y : Scheme.{u}}

/-- **Field extension.** For `b : Y ⟶ Spec K` quasi-compact and quasi-separated, a field map
`σ : K →+* K'` and a quasicoherent `M`, the dimension of `H^q(Y ×_K Spec K', M_{K'})` over `K'`
is that of `H^q(Y, M)` over `K` (flat base change over a field). -/
theorem moduleCohomologyDimension_fieldBaseChange (b : Y ⟶ Spec (.of K)) [QuasiCompact b]
    [QuasiSeparated b] {K' : Type u} [Field K'] (σ : K →+* K') (M : Y.Modules)
    [M.IsQuasicoherent] (q : ℕ) :
    moduleCohomologyDimension (pullback.snd b (Spec.map (CommRingCat.ofHom σ)))
        ((Scheme.Modules.pullback (pullback.fst b (Spec.map (CommRingCat.ofHom σ)))).obj M) q =
      moduleCohomologyDimension b M q :=
  moduleCohomology_finrank_fieldBaseChange b σ M q


end AlgebraicGeometry.Scheme.Cohomology
