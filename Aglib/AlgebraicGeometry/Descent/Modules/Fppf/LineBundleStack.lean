/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Descent.Modules.Fppf.Stack
public import Aglib.AlgebraicGeometry.Descent.Modules.Fppf.Locality
public import Aglib.AlgebraicGeometry.Descent.Modules.Substack
public import Aglib.AlgebraicGeometry.Modules.Invertible.Affine
public import Aglib.RingTheory.Descent.Invertible

/-!
# Line bundles form an fppf stack

The nested substack criterion `ObjectProperty.isStack_fullsubcategory_of_le` of
[Substack](../Substack.lean) is applied with `P := isLocallyRankOne`, `Q := isQuasicoherent`
(line bundles are quasi-coherent, `Invertible.lineBundle_isQuasicoherent`) and
`F := pullbackPseudofunctor`; the ambient stack is the fppf stack of quasi-coherent sheaves.

* `isLocallyRankOne_of_pullback_specMap_of_faithfullyFlat`: local rank one descends along
  `Spec.map φ` for faithfully flat `φ`, on quasi-coherent sheaves (faithfully flat descent of
  invertibility, `Module.Invertible.of_invertible_tensorProduct_of_faithfullyFlat`, through
  `tildePullbackIso` and `Invertible.invertible_globalSections`);
* `isLocallyRankOne_of_mem_fppfTopology`: local rank one is local for fppf covering sieves on
  quasi-coherent sheaves, by the property-level reduction `prop_of_mem_fppfTopology` of
  [Locality](Locality.lean);
* the instance `isStack_lineBundlePseudofunctor_fppfTopology`: `lineBundlePseudofunctor` is an
  fppf stack, from the fppf stack of quasi-coherent sheaves
  (`isStack_quasicoherentPseudofunctor_fppfTopology` of [Stack](Stack.lean)) and the nested
  substack criterion.
-/

@[expose] public section

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

open CategoryTheory Pseudofunctor

-- `isIso_fromTildeΓ_of_isQuasicoherent` and the global sections of `tilde` are stated for
-- `(Spec R).Modules`; matching them with the quasicoherence instance needs relaxed instance
-- transparency, as in `Invertible.tildeGlobalSectionsIso`.
set_option backward.isDefEq.respectTransparency false in
/-- **Affine faithfully flat descent of local rank one.** For a faithfully flat `φ : A ⟶ B` and a
quasi-coherent `M` on `Spec A`, if the pullback of `M` along `Spec.map φ` is locally rank one, so
is `M`: the global sections `N` of `M` satisfy `B ⊗[A] N ≅ Γ(Spec.map φ ^* M)`
(`tildePullbackIso`), which is invertible (`Invertible.invertible_globalSections`); invertibility
descends (`Module.Invertible.of_invertible_tensorProduct_of_faithfullyFlat`), and `M ≅ tilde N`
is locally rank one (`Invertible.tilde_isLocallyRankOne`). -/
theorem isLocallyRankOne_of_pullback_specMap_of_faithfullyFlat {A B : CommRingCat.{u}} (φ : A ⟶ B)
    (hφ : φ.hom.FaithfullyFlat) (M : (Spec A).Modules) (hM : M.IsQuasicoherent)
    (h : Invertible.IsLocallyRankOne _ ((pullback (Spec.map φ)).obj M)) :
    Invertible.IsLocallyRankOne _ M := by
  let := φ.hom.toAlgebra
  have : Module.FaithfullyFlat A B := hφ
  have : IsIso M.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M
  let N := moduleSpecΓFunctor.obj M
  let e : tilde N ≅ M := asIso M.fromTildeΓ
  let e' : (pullback (Spec.map φ)).obj M ≅ tilde ((ModuleCat.extendScalars φ.hom).obj N) :=
    (pullback (Spec.map φ)).mapIso e.symm ≪≫ (tildePullbackIso φ).app N
  let L : Invertible.LineBundle (Spec B) := ⟨_, Invertible.isLocallyRankOne_of_iso _ e' h⟩
  have h₁ : Module.Invertible B (moduleSpecΓFunctor.obj L.val) :=
    Invertible.invertible_globalSections L
  have h₂ : Module.Invertible B (TensorProduct A B N) :=
    Module.Invertible.congr (R := B) (M := moduleSpecΓFunctor.obj L.val)
      ((tilde.toTildeΓNatIso.app ((ModuleCat.extendScalars φ.hom).obj N)).symm.toLinearEquiv ≪≫ₗ
        LinearEquiv.refl B (TensorProduct A B N))
  have h₃ : Module.Invertible A N :=
    Module.Invertible.of_invertible_tensorProduct_of_faithfullyFlat A B N
  exact Invertible.isLocallyRankOne_of_iso _ e (Invertible.tilde_isLocallyRankOne N)

/-- Local rank one is local for fppf covering sieves on quasi-coherent sheaves:
`prop_of_mem_fppfTopology` with Zariski locality `isLocallyRankOne_of_mem_zariskiTopology` and
affine faithfully flat descent `isLocallyRankOne_of_pullback_specMap_of_faithfullyFlat`. -/
theorem isLocallyRankOne_of_mem_fppfTopology {S : Scheme.{u}} (R : Sieve S)
    (hR : R ∈ Scheme.fppfTopology S) (M : S.Modules) [M.IsQuasicoherent]
    (hM : ∀ ⦃Y : Scheme.{u}⦄ (g : Y ⟶ S), R g →
      Invertible.IsLocallyRankOne Y ((pullback g).obj M)) :
    Invertible.IsLocallyRankOne S M :=
  prop_of_mem_fppfTopology (fun X M ↦ Invertible.IsLocallyRankOne X M)
    (fun X _ _ e h ↦ Invertible.isLocallyRankOne_of_iso X e h)
    (fun _ _ f M h ↦ Invertible.pullback_locallyRankOne f M h)
    (fun _ _ hR M h ↦ isLocallyRankOne_of_mem_zariskiTopology hR M h)
    (fun _ _ φ hφ M hM h ↦ isLocallyRankOne_of_pullback_specMap_of_faithfullyFlat φ hφ M hM h)
    R hR M hM

/-- **Line bundles form an fppf stack**: the nested substack criterion
`ObjectProperty.isStack_fullsubcategory_of_le` inside the fppf stack of quasi-coherent sheaves. -/
instance isStack_lineBundlePseudofunctor_fppfTopology :
    lineBundlePseudofunctor.{u}.IsStack Scheme.fppfTopology :=
  ObjectProperty.isStack_fullsubcategory_of_le pullbackPseudofunctor.isLocallyRankOne
    pullbackPseudofunctor.isQuasicoherent
    (fun X M hM ↦ Invertible.lineBundle_isQuasicoherent (X := X.as.unop) ⟨M, hM⟩)
    (fun _ R hR M hQ hM ↦
      have : M.IsQuasicoherent := hQ
      isLocallyRankOne_of_mem_fppfTopology R hR M hM)

end AlgebraicGeometry.Scheme.Modules
