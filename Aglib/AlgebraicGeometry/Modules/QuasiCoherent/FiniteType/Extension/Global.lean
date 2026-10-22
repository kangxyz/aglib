/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Extension.Enlargement
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
# Finite-type quasicoherent subobject extension on qcqs schemes

Finite affine-open induction extends a finite-type subobject from a compact open inside
its specified quasicoherent ambient module. All comparison maps are actual restrictions,
and the final isomorphism commutes with the original inclusion.

This proves the module extension statement of Stacks Project, Tag 01PF. Neither the scheme
nor its affine rings are assumed Noetherian, and the ambient module need not be finite type.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules.QuasiCoherent

/-- Finite affine-open induction enlarges the finite-type region while preserving the
actual restriction to the original compact open. -/
theorem affineLocallyFiniteType_subobject_on_compact_open
    {X : Scheme.{u}} [QuasiSeparatedSpace X]
    (M : X.Modules) [M.IsQuasicoherent]
    (W : X.Opens) (hcompactW : IsCompact (W : Set X))
    (hW : affineLocallyFiniteType W.toScheme (M.restrict W.ι))
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
    have : CompactSpace (W ⊔ S).toScheme :=
      isCompact_iff_compactSpace.mp (hcompactW.union hS)
    obtain ⟨N', t, hN', ht, htW, hN'W⟩ :=
      affineLocallyFiniteType_affine_enlargement_of_quasiCompact
        N (W ⊔ S) hNW Γ(X, (V : X.Opens)) V.property.fromSpec
    have : Mono t := ht
    have : IsIso ((restrictFunctor (W ⊔ S).ι).map t) := htW
    have : IsIso ((restrictFunctor W.ι).map t) :=
      isIso_restrict_map_of_le (le_sup_left : W ≤ W ⊔ S) t
    refine ⟨N', t ≫ s, hN', inferInstance, ?_, ?_⟩
    · rw [Functor.map_comp]
      infer_instance
    · rw [V.property.opensRange_fromSpec, sup_assoc] at hN'W
      exact hN'W

/-- On a qcqs scheme, a quasicoherent module finite type on a compact open contains a
finite-type submodule whose actual restriction inclusion is an isomorphism. -/
theorem exists_finiteType_subsheaf_restrict_isIso_of_qcqs
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (M : X.Modules) [M.IsQuasicoherent]
    (W : X.Opens) (hcompactW : IsCompact (W : Set X))
    (hW : affineLocallyFiniteType W.toScheme (M.restrict W.ι)) :
    ∃ (N : FiniteTypeSheaves X) (s : N.obj ⟶ M), Mono s ∧
      IsIso ((restrictFunctor W.ι).map s) := by
  obtain ⟨N, s, hN, hs, hsW, hNW⟩ :=
    affineLocallyFiniteType_subobject_on_compact_open M W hcompactW hW ⊤ isCompact_univ
  have hfinite : affineLocallyFiniteType X N := affineLocallyFiniteType_of_restrict_top N (by
    rw [show W ⊔ (⊤ : X.Opens) = ⊤ from sup_top_eq W] at hNW
    exact hNW)
  exact ⟨⟨N, hfinite⟩, s, hs, hsW⟩

/-- Finite-type quasicoherent subobjects on quasi-compact opens of qcqs schemes extend
inside their specified quasicoherent ambient module, with the original inclusion equation. -/
theorem affineLocallyFiniteType_subobject_extension_of_qcqs
    {U X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (M : X.Modules) [M.IsQuasicoherent]
    (A : FiniteTypeSheaves U) (i : A.obj ⟶ M.restrict j) [Mono i] :
    ∃ (B : FiniteTypeSheaves X) (b : B.obj ⟶ M), Mono b ∧
      ∃ (e : B.obj.restrict j ≅ A.obj),
        (restrictFunctor j).map b = e.hom ≫ i := by
  have : A.obj.IsQuasicoherent :=
    quasicoherent_of_affineCharts A.obj (fun R a _ => (A.property R a).1)
  obtain ⟨K, s, hK, hs, e, he⟩ :=
    quasicoherent_subobject_preimage_of_quasiCompact j M A.obj i
  have : K.IsQuasicoherent := hK
  have : Mono s := hs
  have hKj : affineLocallyFiniteType U (K.restrict j) :=
    (affineLocallyFiniteType U).prop_of_iso e.symm A.property
  have : CompactSpace U := QuasiCompact.compactSpace_of_compactSpace j
  have hcompact : IsCompact (j.opensRange : Set X) := isCompact_range j.continuous
  obtain ⟨B, t, ht, htW⟩ := exists_finiteType_subsheaf_restrict_isIso_of_qcqs
    K j.opensRange hcompact (affineLocallyFiniteType_restrict_opensRange j K hKj)
  have : Mono t := ht
  have : IsIso ((restrictFunctor j.opensRange.ι).map t) := htW
  have : IsIso ((restrictFunctor j).map t) := isIso_restrict_map_of_opensRange j t
  let e' : B.obj.restrict j ≅ A.obj := asIso ((restrictFunctor j).map t) ≪≫ e
  refine ⟨B, t ≫ s, inferInstance, e', ?_⟩
  rw [Functor.map_comp, he]
  rfl

end AlgebraicGeometry.Scheme.Modules.QuasiCoherent
