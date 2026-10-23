/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.FieldTheory.Galois.FiniteAction
public import Aglib.AlgebraicGeometry.FundamentalGroup.Field.ArbitraryGalois

/-! # Actual finite Galois factorization of finite-etale fibre monodromy

The original natural fibre automorphism is evaluated on the actual cover.
Its discrete finite automorphism group supplies an open kernel, so the native
Krull topology produces a genuine finite Galois intermediate field. The
factorization retains the original fibre automorphism, without replacing the
coefficient or assuming that its monodromy factors through a chosen field.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.PreGaloisCategory
open Scheme.FiniteEtale Scheme.EtaleFundamentalGroups
open Scheme.FiniteEtale.FieldGalois.OverRing

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u

/-- The actual finite-etale fibre action factors through an actual finite
Galois intermediate field, in arbitrary characteristic. -/
theorem exists_finiteGalois_fiberAction_factorization
    (E Ω : Type u) [Field E] [Field Ω] [Algebra E Ω] [IsGalois E Ω]
    (Y : Scheme.FiniteEtale (Spec (.of E))) :
    ∃ L : FiniteGaloisIntermediateField E Ω,
      ∃ ρL : (L ≃ₐ[E] L) →* Aut ((fiberToFinite (basePoint E Ω)).obj Y),
        ∀ σ : Ω ≃ₐ[E] Ω, ρL (σ.restrictNormal L) =
          (galoisToFibre E E Ω σ).app Y := by
  let F := fiberToFinite (basePoint E Ω)
  let e := FieldGalois.Arbitrary.fundamentalGroupContinuousEquiv E Ω
  let ρ : (Ω ≃ₐ[E] Ω) →* Aut (F.obj Y) :=
    MonoidHom.mk' (fun σ => (e σ).app Y) (fun σ τ => by rw [map_mul]; rfl)
  have hρ : Continuous ρ := by
    exact (continuous_apply Y).comp (continuous_induced_dom.comp e.continuous)
  exact InfiniteGalois.exists_finiteGalois_factorization ρ hρ

end AlgebraicGeometry.Scheme.EtaleCohomology
