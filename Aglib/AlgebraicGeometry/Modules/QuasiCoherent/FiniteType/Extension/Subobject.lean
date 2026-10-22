/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Extension.Affine
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Subobjects.Preimage
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Restriction.Comparison
public import Aglib.AlgebraicGeometry.Modules.Restriction.Isomorphisms

/-!
# Finite-type open subobjects over an arbitrary affine scheme

A finite-type quasicoherent subobject on a quasi-compact open extends inside the given
quasicoherent ambient module. The actual restriction isomorphism commutes with the original
inclusion. The ring and ambient module have no Noetherian or finiteness assumption.

This is the affine case of Stacks Project, Tag 01PF. The quasicoherent preimage kernel is
approximated by a finite-type submodule using a finite principal-open cover.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules.QuasiCoherent

/-- A finite-type subobject on a quasi-compact open of an affine scheme extends
inside the actual quasicoherent ambient module, preserving its inclusion. -/
theorem affineLocallyFiniteType_subobject_extension_affine_of_quasiCompact
    (R : CommRingCat.{u}) {U : Scheme.{u}}
    (j : U ⟶ Spec R) [IsOpenImmersion j] [QuasiCompact j]
    (M : (Spec R).Modules) [M.IsQuasicoherent]
    (A : FiniteTypeSheaves U) (a : A.obj ⟶ M.restrict j) [Mono a] :
    ∃ (B : FiniteTypeSheaves (Spec R)) (b : B.obj ⟶ M), Mono b ∧
      ∃ (e : B.obj.restrict j ≅ A.obj),
        (restrictFunctor j).map b = e.hom ≫ a := by
  have : A.obj.IsQuasicoherent :=
    quasicoherent_of_affineCharts A.obj (fun S k _ => (A.property S k).1)
  obtain ⟨K, s, hK, hs, e, he⟩ :=
    quasicoherent_subobject_preimage_of_quasiCompact j M A.obj a
  have : K.IsQuasicoherent := hK
  have : Mono s := hs
  have hKj : affineLocallyFiniteType U (K.restrict j) :=
    (affineLocallyFiniteType U).prop_of_iso e.symm A.property
  have : CompactSpace U := QuasiCompact.compactSpace_of_compactSpace j
  have hcompact : IsCompact (j.opensRange : Set (Spec R)) := isCompact_range j.continuous
  obtain ⟨B, t, ht, htW⟩ := exists_finiteType_subsheaf_restrict_isIso
    R K j.opensRange hcompact (affineLocallyFiniteType_restrict_opensRange j K hKj)
  have : Mono t := ht
  have : IsIso ((restrictFunctor j.opensRange.ι).map t) := htW
  have : IsIso ((restrictFunctor j).map t) := isIso_restrict_map_of_opensRange j t
  let e' : B.obj.restrict j ≅ A.obj := asIso ((restrictFunctor j).map t) ≪≫ e
  refine ⟨B, t ≫ s, inferInstance, e', ?_⟩
  rw [Functor.map_comp, he]
  rfl

end AlgebraicGeometry.Scheme.Modules.QuasiCoherent
