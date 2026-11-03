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

/-- At a reflexive triangle, the actual equality transport is the native comparison. -/
theorem extendScalarsCompOfEq_refl_hom_app (f : R →+* S) (g : S →+* T)
    (N : ModuleCat.{u} R) :
    ((eqToIso (congrArg (fun q : R →+* T => extendScalars q)
        (rfl : g.comp f = g.comp f)) ≪≫ extendScalarsComp f g).hom.app N) =
      (extendScalarsComp f g).hom.app N := by
  simp only [eqToIso_refl, Iso.trans_hom, Iso.refl_hom, Category.id_comp]

/-- The native scalar comparison along the actual triangle preserves the unit tensor. -/
theorem extendScalarsComp_congr_hom_app_one_tmul
    (φ : R →+* S) (ψ : S →+* T) (ρ : R →+* T)
    (hρ : ψ.comp φ = ρ) (M : ModuleCat.{u} R) (x : M) :
    ((eqToIso (congrArg (fun q : R →+* T => extendScalars q) hρ.symm) ≪≫
        extendScalarsComp φ ψ).hom.app M) ((1 : T) ⊗ₜ[R,ρ] x) =
      (1 : T) ⊗ₜ[S,ψ] ((1 : S) ⊗ₜ[R,φ] x) := by
  subst ρ
  exact extendScalarsComp_hom_app_one_tmul φ ψ M x

end ModuleCat
