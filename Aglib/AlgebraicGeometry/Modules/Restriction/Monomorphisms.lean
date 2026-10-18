/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Exact
public import Aglib.AlgebraicGeometry.Modules.Pullback.OpenRestriction

/-!
# Monomorphisms under actual open pullback

## Extraction basis

Existing proofs transferred from frozen dirty R5 revision
`79307ff88f07d34fd5c3edb859f799c55e38f290`. Source identities:

- `R5Lab/AlgebraicGeometry/Curves/RelativeDivisors/FibrewiseRegularity.lean`, SHA-256
  `79621aa63046ca16c5f98424d77f16bc8cd45b99a84ddc8bc561fc8f9ccfe923`.

Actual objects, maps, universes and stated conditions are retained.
Native validation coverage is recorded separately in `docs/WORK_PLAN.md` and
the migration records; the source hashes above identify extraction inputs.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w t

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Modules
open LinearMap

section
namespace AlgebraicGeometry.Scheme.Modules

/-- The actual pullback along an open immersion preserves monomorphisms. -/
theorem pullback_mono_of_isOpenImmersion {X Y : Scheme.{u}}
    (i : X ⟶ Y) [IsOpenImmersion i] {M N : Y.Modules} (φ : M ⟶ N) [Mono φ] :
    Mono ((Scheme.Modules.pullback i).map φ) := by
  have : (Scheme.Modules.restrictFunctor i).PreservesMonomorphisms := inferInstance
  have : (Scheme.Modules.pullback i).PreservesMonomorphisms :=
    Functor.PreservesMonomorphisms.of_iso (Scheme.Modules.restrictFunctorIsoPullback i)
  infer_instance

end AlgebraicGeometry.Scheme.Modules
end
