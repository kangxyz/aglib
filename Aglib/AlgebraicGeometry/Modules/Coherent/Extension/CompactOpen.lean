/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Coherent.Basic
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Restriction.Comparison
public import Aglib.AlgebraicGeometry.Modules.Restriction.Isomorphisms

/-!
# Compact-open induction for coherent extension

An explicit one-affine-chart enlargement hypothesis yields finite-type extension across a
compact open. The whole-scheme conclusion also assumes CompactSpace; the enlargement hypothesis
is an input to both theorems.
-/

/-!
Source: frozen dirty Quillen `6db56ddd3fdb898ef5de29d5fe51a0c61f9ba116`.
`Quillen/AlgebraicGeometry/Scheme/Coherent/Localization/ObjectExtensionInduction.lean`.
SHA-256: `fae0e7c98763b1aec5f6b8208d1df6c5dd5838d77999d3bd4004285f5f11bc2e`.
Selected original statements and proofs; canonical lower APIs replace the recorded source wrappers.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ModuleCat
open AlgebraicGeometry.Scheme.Modules
attribute [local instance] Abelian.hasFiniteBiproducts
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open CategoryTheory.ExactCategory
namespace AlgebraicGeometry.Scheme.Modules.Coherent

/-- The compact-open induction preserves the original open restriction and
accumulates coherence on the genuine union of affine opens. -/
theorem affineLocallyFiniteType_subobject_on_compact_open_of_enlargement
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    (henlarge : ∀ (N : X.Modules) [N.IsQuasicoherent]
      (W : X.Opens), affineLocallyFiniteType W.toScheme (N.restrict W.ι) →
      ∀ (R : CommRingCat.{u}) [IsNoetherianRing R]
      (a : Spec R ⟶ X) [IsOpenImmersion a],
      ∃ (N' : X.Modules) (s : N' ⟶ N), N'.IsQuasicoherent ∧ Mono s ∧
        IsIso ((restrictFunctor W.ι).map s) ∧
        affineLocallyFiniteType (W ⊔ a.opensRange).toScheme
          (N'.restrict (W ⊔ a.opensRange).ι))
    (M : X.Modules) [M.IsQuasicoherent]
    (W : X.Opens) (hW : affineLocallyFiniteType W.toScheme (M.restrict W.ι))
    (S : X.Opens) (hS : IsCompact (S : Set X)) :
    ∃ (N : X.Modules) (s : N ⟶ M), N.IsQuasicoherent ∧ Mono s ∧
      IsIso ((restrictFunctor W.ι).map s) ∧
      affineLocallyFiniteType (W ⊔ S).toScheme (N.restrict (W ⊔ S).ι) := by
  refine compact_open_induction_on S hS ?_ ?_
  · refine ⟨M, 𝟙 M, inferInstance, inferInstance, ?_, ?_⟩
    · exact (restrictFunctor W.ι).map_isIso (𝟙 M)
    · rw [sup_bot_eq]
      exact hW
  · intro S hS V ih
    obtain ⟨N, s, hN, hs, hsW, hNW⟩ := ih
    have : N.IsQuasicoherent := hN
    have : Mono s := hs
    have : IsIso ((restrictFunctor W.ι).map s) := hsW
    have : IsNoetherianRing Γ(X, (V : X.Opens)) :=
      IsLocallyNoetherian.component_noetherian V
    obtain ⟨N', t, hN', ht, htW, hN'W⟩ :=
      henlarge N (W ⊔ S) hNW Γ(X, (V : X.Opens)) V.property.fromSpec
    have : Mono t := ht
    have : IsIso ((restrictFunctor (W ⊔ S).ι).map t) := htW
    have : IsIso ((restrictFunctor W.ι).map t) :=
      isIso_restrict_map_of_le (le_sup_left : W ≤ W ⊔ S) t
    refine ⟨N', t ≫ s, hN', inferInstance, ?_, ?_⟩
    · rw [Functor.map_comp]
      infer_instance
    · rw [V.property.opensRange_fromSpec, sup_assoc] at hN'W
      exact hN'W

/-- Covering a quasi-compact scheme by finitely many affine opens completes
the coherent subobject extension. -/
theorem affineLocallyFiniteType_subobject_extension_of_affine_enlargement
    {X : Scheme.{u}} [IsLocallyNoetherian X] [CompactSpace X]
    (henlarge : ∀ (N : X.Modules) [N.IsQuasicoherent]
      (W : X.Opens), affineLocallyFiniteType W.toScheme (N.restrict W.ι) →
      ∀ (R : CommRingCat.{u}) [IsNoetherianRing R]
      (a : Spec R ⟶ X) [IsOpenImmersion a],
      ∃ (N' : X.Modules) (s : N' ⟶ N), N'.IsQuasicoherent ∧ Mono s ∧
        IsIso ((restrictFunctor W.ι).map s) ∧
        affineLocallyFiniteType (W ⊔ a.opensRange).toScheme
          (N'.restrict (W ⊔ a.opensRange).ι))
    (M : X.Modules) [M.IsQuasicoherent]
    (W : X.Opens) (hW : affineLocallyFiniteType W.toScheme (M.restrict W.ι)) :
    ∃ (N : FiniteTypeSheaves X) (s : N.obj ⟶ M), Mono s ∧
      IsIso ((restrictFunctor W.ι).map s) := by
  obtain ⟨N, s, hN, hs, hsW, hNW⟩ :=
    affineLocallyFiniteType_subobject_on_compact_open_of_enlargement
      henlarge M W hW ⊤ isCompact_univ
  have hcoh : affineLocallyFiniteType X N := affineLocallyFiniteType_of_restrict_top N (by
    rw [show W ⊔ (⊤ : X.Opens) = ⊤ from sup_top_eq W] at hNW
    exact hNW)
  exact ⟨⟨N, hcoh⟩, s, hs, hsW⟩

end AlgebraicGeometry.Scheme.Modules.Coherent
