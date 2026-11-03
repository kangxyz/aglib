/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! # Original scalar extension along an actual ring-map triangle

These are the original scalar-triangle construction and unit law, shared by
finite matrix-cokernel descent and actual pushout-source composition.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory
open scoped ChangeOfRings TensorProduct

universe u

namespace ModuleCat

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]

/-- Native scalar-extension composition for a specified actual scalar
triangle, using equality only to identify its composite ring map. -/
def extendScalarsCompOfEq (φ : R →+* S) (ψ : S →+* T) (ρ : R →+* T)
    (hρ : ψ.comp φ = ρ) : extendScalars ρ ≅ extendScalars φ ⋙ extendScalars ψ :=
  eqToIso (congrArg (fun q : R →+* T ↦ extendScalars q) hρ.symm) ≪≫
    extendScalarsComp φ ψ

/-- At a reflexive scalar triangle, the original component is native scalar composition. -/
theorem extendScalarsCompOfEq_refl_hom_app (f : R →+* S) (g : S →+* T)
    (N : ModuleCat.{u} R) :
    (extendScalarsCompOfEq f g (g.comp f) rfl).hom.app N =
      (extendScalarsComp f g).hom.app N := by
  simp only [extendScalarsCompOfEq, eqToIso_refl, Iso.trans_hom,
    Iso.refl_hom, Category.id_comp]

/-- The original unit tensor is retained by the actual scalar triangle. -/
theorem extendScalarsCompOfEq_hom_app_one_tmul
    (φ : R →+* S) (ψ : S →+* T) (ρ : R →+* T)
    (hρ : ψ.comp φ = ρ) (M : ModuleCat.{u} R) (x : M) :
    (extendScalarsCompOfEq φ ψ ρ hρ).hom.app M ((1 : T) ⊗ₜ[R,ρ] x) =
      (1 : T) ⊗ₜ[S,ψ] ((1 : S) ⊗ₜ[R,φ] x) := by
  subst ρ
  exact extendScalarsComp_hom_app_one_tmul φ ψ M x

end ModuleCat
