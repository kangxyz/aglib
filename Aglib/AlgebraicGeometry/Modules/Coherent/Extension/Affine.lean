/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Extension.Affine
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Subobjects.Preimage
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Subobjects.Gluing
public import Aglib.AlgebraicGeometry.Modules.Coherent.Gluing

/-!
# Affine extension and enlargement of coherent subobjects

A finite-type open subobject extends inside a quasicoherent sheaf on a Noetherian affine scheme.
One additional Noetherian affine chart enlarges an existing finite-type region while preserving
the given restriction isomorphism.
-/

/-!
Source: frozen dirty Quillen `6db56ddd3fdb898ef5de29d5fe51a0c61f9ba116`.
`Quillen/AlgebraicGeometry/Scheme/Coherent/Localization/AffineExtension.lean`.
SHA-256: `f3123846564192b4dd5bfc1e9fb14e7320fe197db62e2aa0f411e4b547a3f5a6`.
`Quillen/AlgebraicGeometry/Scheme/Coherent/Localization/AffineEnlargement.lean`.
SHA-256: `1c66fc512c3d458b75d6297240bf629f19f1a3df85c2240579d5c7d8f4c97986`.
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

/-- A coherent subobject on an arbitrary open of a noetherian affine
scheme extends to a coherent subobject of its actual quasicoherent ambient. -/
theorem affineLocallyFiniteType_subobject_extension_affine
    (R : CommRingCat.{u}) [IsNoetherianRing R]
    {U : Scheme.{u}} [IsLocallyNoetherian U]
    (j : U ⟶ Spec R) [IsOpenImmersion j]
    (M : (Spec R).Modules) [M.IsQuasicoherent]
    (A : FiniteTypeSheaves U) (a : A.obj ⟶ M.restrict j) [Mono a] :
    ∃ (B : FiniteTypeSheaves (Spec R)) (b : B.obj ⟶ M), Mono b ∧
      ∃ (e : B.obj.restrict j ≅ A.obj),
        (Scheme.Modules.restrictFunctor j).map b = e.hom ≫ a := by
  obtain ⟨K, s, hK, hs, e, he⟩ := quasicoherent_subobject_preimage j M A a
  have : K.IsQuasicoherent := hK
  have : Mono s := hs
  have hKj : affineLocallyFiniteType U (K.restrict j) :=
    (affineLocallyFiniteType U).prop_of_iso e.symm A.property
  let er : Scheme.Modules.restrictFunctor j ⋙
      Scheme.Modules.restrictFunctor j.isoOpensRange.inv ≅
      Scheme.Modules.restrictFunctor j.opensRange.ι :=
    (Scheme.Modules.restrictFunctorComp j.isoOpensRange.inv j).symm ≪≫
      Scheme.Modules.restrictFunctorCongr j.isoOpensRange_inv_comp
  have hKr : affineLocallyFiniteType j.opensRange.toScheme (K.restrict j.opensRange.ι) :=
    (affineLocallyFiniteType j.opensRange.toScheme).prop_of_iso (er.app K)
      (affineLocallyFiniteType_restrict j.isoOpensRange.inv hKj)
  obtain ⟨B, t, ht, htr⟩ := exists_finiteType_subsheaf_restrict_isIso R K j.opensRange
    (NoetherianSpace.isCompact _) hKr
  have : Mono t := ht
  have : IsIso ((Scheme.Modules.restrictFunctor j.opensRange.ι).map t) := htr
  have hj : j.isoOpensRange.hom ≫ j.opensRange.ι = j := by
    apply (cancel_epi j.isoOpensRange.inv).mp
    simp [j.isoOpensRange_inv_comp]
  let er' : Scheme.Modules.restrictFunctor j.opensRange.ι ⋙
      Scheme.Modules.restrictFunctor j.isoOpensRange.hom ≅
      Scheme.Modules.restrictFunctor j :=
    (Scheme.Modules.restrictFunctorComp j.isoOpensRange.hom j.opensRange.ι).symm ≪≫
      Scheme.Modules.restrictFunctorCongr hj
  have htj : IsIso ((Scheme.Modules.restrictFunctor j).map t) := by
    apply (NatIso.isIso_map_iff er' t).mp
    exact (Scheme.Modules.restrictFunctor j.isoOpensRange.hom).map_isIso
      ((Scheme.Modules.restrictFunctor j.opensRange.ι).map t)
  let e' : B.obj.restrict j ≅ A.obj :=
    asIso ((Scheme.Modules.restrictFunctor j).map t) ≪≫ e
  refine ⟨B, t ≫ s, inferInstance, e', ?_⟩
  rw [Functor.map_comp, he]
  rfl

/-- A global quasicoherent sheaf coherent on `W` has a quasicoherent
subsheaf equal to it on `W` and coherent on the union of `W` with one affine
chart. This is the actual finite-cover induction step. -/
theorem affineLocallyFiniteType_affine_enlargement
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    (N : X.Modules) [N.IsQuasicoherent] (W : X.Opens)
    (hW : affineLocallyFiniteType W.toScheme (N.restrict W.ι))
    (R : CommRingCat.{u}) [IsNoetherianRing R]
    (a : Spec R ⟶ X) [IsOpenImmersion a] :
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
    affineLocallyFiniteType_subobject_extension_affine R q (N.restrict a) Ap i
  have : Mono b := hb
  have he : (Scheme.Modules.restrictFunctor p).map (𝟙 (N.restrict W.ι)) ≫
      E.hom.app N = eB.inv ≫ (Scheme.Modules.restrictFunctor q).map b := by
    rw [heB]
    simp [i]
  obtain ⟨N', s, hN', hs, eW, ea, hsW, hsa⟩ :=
    exists_quasicoherent_glued_subobject W.ι a (𝟙 (N.restrict W.ι)) b eB.symm he
  have hN'W : affineLocallyFiniteType W.toScheme (N'.restrict W.ι) :=
    (affineLocallyFiniteType W.toScheme).prop_of_iso eW.symm hW
  have hN'a : affineLocallyFiniteType (Spec R) (N'.restrict a) :=
    (affineLocallyFiniteType (Spec R)).prop_of_iso ea.symm B.property
  refine ⟨N', s, hN', hs, ?_, ?_⟩
  · rw [hsW, Category.comp_id]
    infer_instance
  · exact affineLocallyFiniteType_restrict_sup N' W a.opensRange hN'W
      (affineLocallyFiniteType_restrict_opensRange a N' hN'a)

end AlgebraicGeometry.Scheme.Modules.Coherent
