/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Surjectivity of a closed spectral ring map

## Extraction basis

Existing proofs transferred from frozen dirty R5 revision
`79307ff88f07d34fd5c3edb859f799c55e38f290`. Source identities:

- `R5Lab/AlgebraicGeometry/Curves/RelativeDivisors/SmoothIdeal.lean`, SHA-256
  `1e1f564e4d5d68f6f673a435f935642b06c6faeca7632d110bc71565993a96e4`.

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
open LinearMap

section
namespace AlgebraicGeometry.IsClosedImmersion

theorem surjective_of_specMap {A B : CommRingCat.{u}}
    (φ : A ⟶ B) [IsClosedImmersion (Spec.map φ)] : Function.Surjective φ.hom := by
  have h := (Spec.map φ).app_surjective ⊤ (isAffineOpen_top (Spec A))
  have he : (Scheme.ΓSpecIso A).inv ≫ (Spec.map φ).appTop ≫ (Scheme.ΓSpecIso B).hom = φ := by
    rw [← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality]
    simp
  have hs := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso B).hom).2.comp
    (h.comp (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso A).inv).2)
  change Function.Surjective (fun x ↦
    ((Scheme.ΓSpecIso A).inv ≫ (Spec.map φ).appTop ≫ (Scheme.ΓSpecIso B).hom) x) at hs
  simpa only [he] using hs

end AlgebraicGeometry.IsClosedImmersion
end
