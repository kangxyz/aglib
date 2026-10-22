/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Extension.Subobject
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Locality
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Subobjects.Gluing

/-!
# Finite-type enlargement across one affine open

A quasicoherent submodule finite type on one quasi-compact open immersion can be shrunk
inside its ambient module to become finite type on the union with an affine chart.
The restriction over the original open remains an isomorphism. This is the enlargement
step of Stacks Project, Tag 01PF, with quasi-compactness stated directly on the immersions.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules.QuasiCoherent

/-- A global quasicoherent sheaf finite type on `W` has a quasicoherent
subsheaf equal to it on `W` and finite type on the union of `W` with one affine
chart. This is the actual finite-cover induction step. -/
theorem affineLocallyFiniteType_affine_enlargement_of_quasiCompact
    {X : Scheme.{u}}
    (N : X.Modules) [N.IsQuasicoherent] (W : X.Opens) [QuasiCompact W.ι]
    (hW : affineLocallyFiniteType W.toScheme (N.restrict W.ι))
    (R : CommRingCat.{u})
    (a : Spec R ⟶ X) [IsOpenImmersion a] [QuasiCompact a] :
    ∃ (N' : X.Modules) (s : N' ⟶ N), N'.IsQuasicoherent ∧ Mono s ∧
      IsIso ((Scheme.Modules.restrictFunctor W.ι).map s) ∧
      affineLocallyFiniteType (W ⊔ a.opensRange).toScheme (N'.restrict (W ⊔ a.opensRange).ι) := by
  let p := pullback.fst W.ι a
  let q := pullback.snd W.ι a
  let A : FiniteTypeSheaves W.toScheme := ⟨N.restrict W.ι, hW⟩
  let Ap : FiniteTypeSheaves (CategoryTheory.Limits.pullback W.ι a) := (finiteTypeSheavesRestriction
    p).obj A
  let E := overlapRestrictIso W.ι a
  let i : Ap.obj ⟶ (N.restrict a).restrict q := (E.app N).hom
  have : Mono i := by dsimp only [i]; infer_instance
  obtain ⟨B, b, hb, eB, heB⟩ :=
    affineLocallyFiniteType_subobject_extension_affine_of_quasiCompact R q (N.restrict a) Ap i
  have : Mono b := hb
  have : B.obj.IsQuasicoherent :=
    quasicoherent_of_affineCharts B.obj (fun S k _ => (B.property S k).1)
  have he : (Scheme.Modules.restrictFunctor p).map (𝟙 (N.restrict W.ι)) ≫
      E.hom.app N = eB.inv ≫ (Scheme.Modules.restrictFunctor q).map b := by
    rw [heB]
    simp [i]
  obtain ⟨N', s, hN', hs, eW, ea, hsW, hsa⟩ :=
    exists_quasicoherent_glued_subobject_of_quasiCompact W.ι a (𝟙 (N.restrict W.ι)) b eB.symm he
  have : N'.IsQuasicoherent := hN'
  have hN'W : affineLocallyFiniteType W.toScheme (N'.restrict W.ι) :=
    (affineLocallyFiniteType W.toScheme).prop_of_iso eW.symm hW
  have hN'a : affineLocallyFiniteType (Spec R) (N'.restrict a) :=
    (affineLocallyFiniteType (Spec R)).prop_of_iso ea.symm B.property
  refine ⟨N', s, hN', hs, ?_, ?_⟩
  · rw [hsW, Category.comp_id]
    infer_instance
  · exact affineLocallyFiniteType_restrict_sup_of_quasicoherent N' W a.opensRange hN'W
      (affineLocallyFiniteType_restrict_opensRange a N' hN'a)


end AlgebraicGeometry.Scheme.Modules.QuasiCoherent
