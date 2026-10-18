/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Local section tests for module-sheaf morphisms

## Extraction basis

Existing proofs transferred from frozen dirty R5 revision
`79307ff88f07d34fd5c3edb859f799c55e38f290`. Source identities:

- `R5Lab/AlgebraicGeometry/Curves/RelativeDivisors/FibrewiseRegularity.lean`, SHA-256
  `79621aa63046ca16c5f98424d77f16bc8cd45b99a84ddc8bc561fc8f9ccfe923`.
- `R5Lab/AlgebraicGeometry/Curves/RelativeDivisors/ZeroLocus.lean`, SHA-256
  `965a9542a747894891b7cc04c235143b80984b77c931144b0b17f93d36a2c820`.

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

/-- Monicity of a module sheaf map gives injectivity on actual sections. -/
theorem moduleHom_app_injective {X : Scheme.{u}} {M N : X.Modules}
    (φ : M ⟶ N) [Mono φ] (U : X.Opens) : Function.Injective (φ.app U) := by
  have : Mono ((SheafOfModules.evaluation X.ringCatSheaf (op U)).map φ) := inferInstance
  exact (ModuleCat.mono_iff_injective _).mp this

/-- Injectivity on actual sections gives monicity of the module sheaf map. -/
theorem moduleHom_mono_of_app_injective {X : Scheme.{u}} {M N : X.Modules}
    (φ : M ⟶ N) (h : ∀ U : X.Opens, Function.Injective (φ.app U)) : Mono φ := by
  constructor
  intro P a b hab
  apply Scheme.Modules.hom_ext
  intro U
  ext m
  apply h U
  exact congrArg (fun k : P ⟶ N ↦ k.app U m) hab

end AlgebraicGeometry.Scheme.Modules
end

section
namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {M N : X.Modules}

theorem moduleHom_ext_affine (φ ψ : M ⟶ N)
    (h : ∀ U : X.affineOpens, φ.app U.val = ψ.app U.val) : φ = ψ := by
  apply (Scheme.Modules.toPresheaf X).map_injective
  apply TopCat.Sheaf.hom_ext M.presheaf ⟨N.presheaf, N.isSheaf⟩
    (B := fun U : X.affineOpens ↦ U.val) (by simpa using X.isBasis_affineOpens)
  exact h

end AlgebraicGeometry.Scheme.Modules
end
