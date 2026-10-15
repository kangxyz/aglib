/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Flat
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.Qcqs.MayerVietoris
public import Aglib.AlgebraicGeometry.Cohomology.MayerVietoris.Scalars.Zero
public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four

/-! # Gluing invertibility of the original open-cohomology tensor map

Flat scalar extension preserves the original native module Mayer–Vietoris
exact sequence. Its actual tensor ladder and the native five lemma then
glue invertibility on two opens and their intersection. The zero-degree
case uses the original monomorphic restriction map, without an acyclicity
premise.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open CategoryTheory.ComposableArrows

namespace AlgebraicGeometry.Scheme.Cohomology

variable {R S : Type u} [CommRing R] [CommRing S]

/-- Flat scalar extension preserves the exactness of the original native module sequence. -/
theorem moduleMayerVietorisTensorSequence_exact (X : Scheme.{u})
    (α : R →+* Γ(X, ⊤)) (M : X.Modules) (σ : R →+* S) (hflat : σ.Flat)
    (U V : X.Opens) (n : ℕ) :
    ComposableArrows.Exact (moduleMayerVietorisSequence X α M U V n ⋙
      ModuleCat.extendScalars.{u, u, u + 1} σ) := by
  let A := moduleMayerVietorisSequence X α M U V n
  let E := ModuleCat.extendScalars.{u, u, u + 1} σ
  have hA := moduleMayerVietorisSequence_exact X α M U V n
  have hz : ComposableArrows.IsComplex (A ⋙ E) := ⟨fun i hi => by
    change E.map (A.map' i (i + 1)) ≫ E.map (A.map' (i + 1) (i + 2)) = 0
    rw [← E.map_comp, hA.toIsComplex.zero i hi, E.map_zero]⟩
  refine { toIsComplex := hz, exact := fun i hi => ?_ }
  exact ModuleCat.extendScalars_map_exact_of_flat σ hflat (A.sc hA.toIsComplex i hi)
    (hA.exact i hi)

variable {X Y : Scheme.{u}} (p : Y ⟶ X) (σ : R →+* S)
  (α : R →+* Γ(X, ⊤)) (β : S →+* Γ(Y, ⊤))
  (h : p.appTop.hom.comp α = β.comp σ)
  {M : X.Modules} {N : Y.Modules}
  (φ : M ⟶ (Scheme.Modules.pushforward p).obj N)

/-- The original zero-degree tensor map is invertible on a union if it is invertible
on both opens and their intersection. -/
theorem moduleHPrimeTensorMap_isIso_sup_zero (hflat : σ.Flat) (U V : X.Opens)
    [IsIso ((moduleHPrimeTensorMap p σ α β h φ 0).app (op U))]
    [IsIso ((moduleHPrimeTensorMap p σ α β h φ 0).app (op V))]
    [IsIso ((moduleHPrimeTensorMap p σ α β h φ 0).app (op (U ⊓ V)))] :
    IsIso ((moduleHPrimeTensorMap p σ α β h φ 0).app (op (U ⊔ V))) := by
  let : (ModuleCat.extendScalars.{u, u, u + 1} σ).IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{u + 1, u, u} σ).isLeftAdjoint
  let : PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u + 1} σ) :=
    ModuleCat.extendScalars_preservesFiniteLimits_of_flat σ hflat
  let : Mono (moduleMayerVietorisToBiprod X α M U V 0) :=
    moduleMayerVietorisToBiprod_mono_zero X α M U V
  let : IsIso (moduleMayerVietorisTensorBiprodMap p σ α β h φ U V 0) :=
    moduleMayerVietorisTensorBiprodMap_isIso p σ α β h φ U V 0
  let F := natAddLEFunctor (C := ModuleCat.{u + 1} S) (show 0 + 2 ≤ 5 by omega)
  let ψ := F.map (moduleMayerVietorisTensorSequenceMap p σ α β h φ U V 0)
  have h₁ := natAddLEFunctor_obj_exact (show 0 + 2 ≤ 5 by omega)
    (moduleMayerVietorisTensorSequence_exact X α M σ hflat U V 0)
  have h₂ := natAddLEFunctor_obj_exact (show 0 + 2 ≤ 5 by omega)
    (moduleMayerVietorisSequence_exact Y β N (p ⁻¹ᵁ U) (p ⁻¹ᵁ V) 0)
  exact Abelian.isIso_of_isIso_of_mono ψ h₁ h₂
    (by change Mono ((ModuleCat.extendScalars.{u, u, u + 1} σ).map
          (moduleMayerVietorisToBiprod X α M U V 0))
        infer_instance)
    (by change Mono (moduleMayerVietorisToBiprod Y β N (p ⁻¹ᵁ U) (p ⁻¹ᵁ V) 0)
        exact moduleMayerVietorisToBiprod_mono_zero Y β N (p ⁻¹ᵁ U) (p ⁻¹ᵁ V))
    (by change IsIso (moduleMayerVietorisTensorBiprodMap p σ α β h φ U V 0)
        infer_instance)
    (by change Mono ((moduleHPrimeTensorMap p σ α β h φ 0).app (op (U ⊓ V)))
        infer_instance)

/-- The native five lemma glues the original positive-degree tensor map on a union. -/
theorem moduleHPrimeTensorMap_isIso_sup_succ (hflat : σ.Flat) (U V : X.Opens) (n : ℕ)
    [IsIso ((moduleHPrimeTensorMap p σ α β h φ n).app (op U))]
    [IsIso ((moduleHPrimeTensorMap p σ α β h φ n).app (op V))]
    [IsIso ((moduleHPrimeTensorMap p σ α β h φ n).app (op (U ⊓ V)))]
    [IsIso ((moduleHPrimeTensorMap p σ α β h φ (n + 1)).app (op U))]
    [IsIso ((moduleHPrimeTensorMap p σ α β h φ (n + 1)).app (op V))]
    [IsIso ((moduleHPrimeTensorMap p σ α β h φ (n + 1)).app (op (U ⊓ V)))] :
    IsIso ((moduleHPrimeTensorMap p σ α β h φ (n + 1)).app (op (U ⊔ V))) := by
  let : IsIso (moduleMayerVietorisTensorBiprodMap p σ α β h φ U V n) :=
    moduleMayerVietorisTensorBiprodMap_isIso p σ α β h φ U V n
  let : IsIso (moduleMayerVietorisTensorBiprodMap p σ α β h φ U V (n + 1)) :=
    moduleMayerVietorisTensorBiprodMap_isIso p σ α β h φ U V (n + 1)
  let ψ := δ₀Functor.map (moduleMayerVietorisTensorSequenceMap p σ α β h φ U V n)
  have h₁ := moduleMayerVietorisTensorSequence_exact X α M σ hflat U V n
  have h₂ := moduleMayerVietorisSequence_exact Y β N (p ⁻¹ᵁ U) (p ⁻¹ᵁ V) n
  exact Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono h₁.δ₀ h₂.δ₀ ψ
    (by change Epi (moduleMayerVietorisTensorBiprodMap p σ α β h φ U V n)
        infer_instance)
    (by change IsIso ((moduleHPrimeTensorMap p σ α β h φ n).app (op (U ⊓ V)))
        infer_instance)
    (by change IsIso (moduleMayerVietorisTensorBiprodMap p σ α β h φ U V (n + 1))
        infer_instance)
    (by change Mono ((moduleHPrimeTensorMap p σ α β h φ (n + 1)).app (op (U ⊓ V)))
        infer_instance)

/-- Invertibility of the original tensor map in all degrees glues across two opens. -/
theorem moduleHPrimeTensorMap_isIso_sup (hflat : σ.Flat) (U V : X.Opens)
    (hU : ∀ n, IsIso ((moduleHPrimeTensorMap p σ α β h φ n).app (op U)))
    (hV : ∀ n, IsIso ((moduleHPrimeTensorMap p σ α β h φ n).app (op V)))
    (hUV : ∀ n, IsIso ((moduleHPrimeTensorMap p σ α β h φ n).app (op (U ⊓ V))))
    (n : ℕ) : IsIso ((moduleHPrimeTensorMap p σ α β h φ n).app (op (U ⊔ V))) := by
  let := hU
  let := hV
  let := hUV
  cases n with
  | zero => exact moduleHPrimeTensorMap_isIso_sup_zero p σ α β h φ hflat U V
  | succ n => exact moduleHPrimeTensorMap_isIso_sup_succ p σ α β h φ hflat U V n

end AlgebraicGeometry.Scheme.Cohomology
