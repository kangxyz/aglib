/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Coherent.Extension.Affine
public import Aglib.AlgebraicGeometry.Modules.Coherent.Extension.CompactOpen
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Subobjects.Preimage
public import Aglib.AlgebraicGeometry.Modules.Restriction.Isomorphisms
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Restriction.Comparison
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Localization.AffineSectionsGlobal

/-!
# Coherent extension on Noetherian schemes

On a Noetherian scheme a quasicoherent sheaf finite type on an open has a finite-type subsheaf
with the same restriction. Open finite-type subobjects extend with their commuting inclusions;
coherent restriction is essentially surjective.
-/

/-!
Source: frozen dirty Quillen `6db56ddd3fdb898ef5de29d5fe51a0c61f9ba116`.
`Quillen/AlgebraicGeometry/Scheme/Coherent/Localization/ObjectExtension.lean`.
SHA-256: `54358cfc29fc5c287bddf7c306be5c8fb02192b5fb1850efce36d5a5924d1ca5`.
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

/-- A quasicoherent sheaf coherent on an open of a noetherian scheme has an
actual coherent subsheaf whose restriction to that open is unchanged. -/
theorem exists_coherent_subsheaf_restrict_isIso_noetherian
    {X : Scheme.{u}} [IsNoetherian X]
    (M : X.Modules) [M.IsQuasicoherent]
    (W : X.Opens) (hW : affineLocallyFiniteType W.toScheme (M.restrict W.ι)) :
    ∃ (N : FiniteTypeSheaves X) (s : N.obj ⟶ M), Mono s ∧
      IsIso ((restrictFunctor W.ι).map s) :=
  affineLocallyFiniteType_subobject_extension_of_affine_enlargement
    (fun N _ W hW R _ a _ => affineLocallyFiniteType_affine_enlargement N W hW R a) M W hW

/-- A coherent open subsheaf extends inside any actual quasicoherent
ambient sheaf on a noetherian scheme. The restriction isomorphism commutes
with the given inclusion. -/
theorem affineLocallyFiniteType_subobject_extension_noetherian
    {U X : Scheme.{u}} [IsNoetherian X] [IsLocallyNoetherian U]
    (j : U ⟶ X) [IsOpenImmersion j]
    (M : X.Modules) [M.IsQuasicoherent]
    (A : FiniteTypeSheaves U) (i : A.obj ⟶ M.restrict j) [Mono i] :
    ∃ (B : FiniteTypeSheaves X) (b : B.obj ⟶ M), Mono b ∧
      ∃ (e : B.obj.restrict j ≅ A.obj),
        (restrictFunctor j).map b = e.hom ≫ i := by
  obtain ⟨K, s, hK, hs, e, he⟩ := quasicoherent_subobject_preimage j M A i
  have : K.IsQuasicoherent := hK
  have : Mono s := hs
  have hKj : affineLocallyFiniteType U (K.restrict j) :=
    (affineLocallyFiniteType U).prop_of_iso e.symm A.property
  obtain ⟨B, t, ht, htW⟩ := exists_coherent_subsheaf_restrict_isIso_noetherian
    K j.opensRange (affineLocallyFiniteType_restrict_opensRange j K hKj)
  have : Mono t := ht
  have : IsIso ((restrictFunctor j.opensRange.ι).map t) := htW
  have : IsIso ((restrictFunctor j).map t) := isIso_restrict_map_of_opensRange j t
  let e' : B.obj.restrict j ≅ A.obj := asIso ((restrictFunctor j).map t) ≪≫ e
  refine ⟨B, t ≫ s, inferInstance, e', ?_⟩
  rw [Functor.map_comp, he]
  rfl

/-- Every coherent sheaf on an open subscheme of a noetherian scheme is
the actual restriction of a coherent sheaf on that scheme. -/
theorem affineLocallyFiniteType_extension
    {U X : Scheme.{u}} [IsNoetherian X] [IsLocallyNoetherian U]
    (j : U ⟶ X) [IsOpenImmersion j] (A : FiniteTypeSheaves U) :
    ∃ B : FiniteTypeSheaves X, Nonempty ((finiteTypeSheavesRestriction j).obj B ≅ A) := by
  let M := (pushforward j).obj A.obj
  have : M.IsQuasicoherent := quasicoherent_pushforward_open_of_locallyNoetherian j A.obj
  let e : M.restrict j ≅ A.obj := (restrictFunctorAdjCounitIso j).app A.obj
  obtain ⟨B, b, hb, eB, hB⟩ := affineLocallyFiniteType_subobject_extension_noetherian j M A e.inv
  exact ⟨B, ⟨(affineLocallyFiniteType U).fullyFaithfulι.preimageIso eB⟩⟩

/-- Actual coherent restriction along every open immersion into a
noetherian scheme is essentially surjective. -/
instance finiteTypeSheavesRestriction_essSurj
    {U X : Scheme.{u}} [IsNoetherian X] [IsLocallyNoetherian U]
    (j : U ⟶ X) [IsOpenImmersion j] : (finiteTypeSheavesRestriction j).EssSurj where
  mem_essImage A := affineLocallyFiniteType_extension j A

end AlgebraicGeometry.Scheme.Modules.Coherent
