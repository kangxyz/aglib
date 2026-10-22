/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Restriction.Comparison
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Limits
public import Mathlib.RingTheory.Localization.Finiteness

/-!
# Locality of finite-type quasicoherence on arbitrary schemes

Finite type is detected on an open-immersion cover. The proof restricts to arbitrary affine
charts, refines the given cover by principal opens, and applies the algebraic finite-generation
localization criterion. No finite generation of kernels or Noetherian hypothesis is used.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open scoped ModuleCat.Algebra
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules.QuasiCoherent

/-- The affine-chart finite-type condition includes genuine global quasicoherence. -/
theorem quasicoherent_of_affineLocallyFiniteType {X : Scheme.{u}} {M : X.Modules}
    (hM : affineLocallyFiniteType X M) : M.IsQuasicoherent :=
  quasicoherent_of_affineCharts M (fun R j _ => (hM R j).1)

/-- Finite type on an open supplies finite sections on each principal affine chart
whose image lies in that open, with the actual restriction-composition comparison. -/
theorem finite_restrictPrincipal_of_affineLocallyFiniteType
    {X : Scheme.{u}} (M : X.Modules) (W : X.Opens)
    (hW : affineLocallyFiniteType W.toScheme (M.restrict W.ι))
    (R : CommRingCat.{u}) (j : Spec R ⟶ X) [IsOpenImmersion j]
    (r : R) (h : PrimeSpectrum.basicOpen r ≤ j ⁻¹ᵁ W) :
    Module.Finite (Localization.Away r)
      (moduleSpecΓFunctor.obj ((M.restrict j).restrict (principalOpen R r))) := by
  let k := (basicOpenIsoSpecAway r).inv ≫ j.resLE W (PrimeSpectrum.basicOpen r) h
  have : IsOpenImmersion k := by
    dsimp [k, Scheme.Hom.resLE]
    infer_instance
  have hk : k ≫ W.ι = principalOpen R r ≫ j := by
    simp [k, Category.assoc, basicOpenIsoSpecAway]
  let e : (M.restrict W.ι).restrict k ≅ (M.restrict j).restrict (principalOpen R r) :=
    ((restrictFunctorComp k W.ι).app M).symm ≪≫
      (restrictFunctorCongr hk).app M ≪≫ (restrictFunctorComp (principalOpen R r) j).app M
  exact ((affineFiniteSheaf (CommRingCat.of (Localization.Away r))).prop_of_iso e
    (hW _ k)).2

/-- Finite type is local for a jointly surjective family of actual open immersions. -/
theorem affineLocallyFiniteType_of_openImmersionCover {X : Scheme.{u}}
    (M : X.Modules) [M.IsQuasicoherent] {ι : Type v} (U : ι → Scheme.{u})
    (a : ∀ i, U i ⟶ X) [∀ i, IsOpenImmersion (a i)]
    (hcover : ∀ x : X, ∃ i, x ∈ (a i).opensRange)
    (hU : ∀ i, affineLocallyFiniteType (U i) (M.restrict (a i))) :
    affineLocallyFiniteType X M := by
  intro R j _
  let N := moduleSpecΓFunctor.obj (M.restrict j)
  let T : Set R := {r | Module.Finite (Localization.Away r)
    (restrictionGlobalSections R r N)}
  have hT : Ideal.span T = ⊤ := by
    apply PrimeSpectrum.iSup_basicOpen_eq_top_iff'.mp
    apply top_unique
    intro x hx
    obtain ⟨i, hi⟩ := hcover (j x)
    have hxi : x ∈ j ⁻¹ᵁ (a i).opensRange := hi
    obtain ⟨_, ⟨_, ⟨r, rfl⟩, rfl⟩, hxr, hr⟩ :=
      PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hxi
        (j ⁻¹ᵁ (a i).opensRange).isOpen
    have hfin := finite_restrictPrincipal_of_affineLocallyFiniteType M (a i).opensRange
      (affineLocallyFiniteType_restrict_opensRange (a i) M (hU i)) R j r hr
    have hrT : r ∈ T := by
      let e' := moduleSpecΓFunctor.mapIso
        ((restrictFunctor (principalOpen R r)).mapIso (asIso (M.restrict j).fromTildeΓ))
      exact Module.Finite.of_surjective e'.inv.hom
        (ConcreteCategory.bijective_of_isIso e'.inv).surjective
    exact Opens.mem_iSup.mpr ⟨r, Opens.mem_iSup.mpr ⟨hrT, hxr⟩⟩
  refine ⟨inferInstance, ?_⟩
  exact Module.Finite.of_localizationSpan' T hT
    (Rₚ := fun r => Localization.Away r.val)
    (fun r => toRestrictionGlobalSections R r.val N) (fun r => r.property)

/-- Finite type is local for two actual open immersions covering the scheme. -/
theorem affineLocallyFiniteType_of_binary_openImmersionCover
    {U V X : Scheme.{u}} (j : U ⟶ X) (a : V ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion a]
    (hcover : j.opensRange ⊔ a.opensRange = ⊤) (M : X.Modules) [M.IsQuasicoherent]
    (hU : affineLocallyFiniteType U (M.restrict j))
    (hV : affineLocallyFiniteType V (M.restrict a)) : affineLocallyFiniteType X M := by
  let Z : Bool → Scheme.{u} := fun b => if b then U else V
  let f : ∀ b, Z b ⟶ X := fun b => by cases b <;> first | exact a | exact j
  have hf (b : Bool) : IsOpenImmersion (f b) := by cases b <;> assumption
  apply affineLocallyFiniteType_of_openImmersionCover M Z f
  · intro x
    have hx : x ∈ j.opensRange ⊔ a.opensRange := by rw [hcover]; trivial
    rcases hx with hx | hx
    · exact ⟨true, hx⟩
    · exact ⟨false, hx⟩
  · intro b
    cases b
    · exact hV
    · exact hU

/-- Finite type on two opens gives finite type on their union over an arbitrary base. -/
theorem affineLocallyFiniteType_restrict_sup
    {X : Scheme.{u}} (M : X.Modules) [M.IsQuasicoherent] (W V : X.Opens)
    (hW : affineLocallyFiniteType W.toScheme (M.restrict W.ι))
    (hV : affineLocallyFiniteType V.toScheme (M.restrict V.ι)) :
    affineLocallyFiniteType (W ⊔ V).toScheme (M.restrict (W ⊔ V).ι) := by
  let T : X.Opens := W ⊔ V
  let j : W.toScheme ⟶ T.toScheme := X.homOfLE (show W ≤ T from le_sup_left)
  let a : V.toScheme ⟶ T.toScheme := X.homOfLE (show V ≤ T from le_sup_right)
  have hc : j.opensRange ⊔ a.opensRange = ⊤ := by
    dsimp [j, a]
    rw [Scheme.opensRange_homOfLE, Scheme.opensRange_homOfLE,
      ← Scheme.Hom.preimage_sup]
    exact T.ι_preimage_self
  let eW : (M.restrict T.ι).restrict j ≅ M.restrict W.ι :=
    ((restrictFunctorComp j T.ι).app M).symm ≪≫
      (restrictFunctorCongr (X.homOfLE_ι _)).app M
  let eV : (M.restrict T.ι).restrict a ≅ M.restrict V.ι :=
    ((restrictFunctorComp a T.ι).app M).symm ≪≫
      (restrictFunctorCongr (X.homOfLE_ι _)).app M
  exact affineLocallyFiniteType_of_binary_openImmersionCover j a hc (M.restrict T.ι)
    ((affineLocallyFiniteType W.toScheme).prop_of_iso eW.symm hW)
    ((affineLocallyFiniteType V.toScheme).prop_of_iso eV.symm hV)

/-- Binary locality on opens for a quasicoherent ambient module. -/
theorem affineLocallyFiniteType_of_binary_openCover_of_quasicoherent
    {X : Scheme.{u}} (M : X.Modules) [M.IsQuasicoherent]
    (W V : X.Opens) (hWV : W ⊔ V = ⊤)
    (hW : affineLocallyFiniteType W.toScheme (M.restrict W.ι))
    (hV : affineLocallyFiniteType V.toScheme (M.restrict V.ι)) :
    affineLocallyFiniteType X M :=
  affineLocallyFiniteType_of_binary_openImmersionCover W.ι V.ι (by simpa using hWV) M hW hV

/-- Binary locality with the ambient module before the open immersions. -/
theorem affineLocallyFiniteType_of_binary_openImmersionCover_of_quasicoherent
    {U V X : Scheme.{u}} (M : X.Modules) [M.IsQuasicoherent]
    (j : U ⟶ X) (a : V ⟶ X) [IsOpenImmersion j] [IsOpenImmersion a]
    (hcover : j.opensRange ⊔ a.opensRange = ⊤)
    (hU : affineLocallyFiniteType U (M.restrict j))
    (hV : affineLocallyFiniteType V (M.restrict a)) :
    affineLocallyFiniteType X M :=
  affineLocallyFiniteType_of_binary_openImmersionCover j a hcover M hU hV

/-- The union restriction of a quasicoherent module is finite type when both
open restrictions are finite type. -/
theorem affineLocallyFiniteType_restrict_sup_of_quasicoherent
    {X : Scheme.{u}} (M : X.Modules) [M.IsQuasicoherent] (W V : X.Opens)
    (hW : affineLocallyFiniteType W.toScheme (M.restrict W.ι))
    (hV : affineLocallyFiniteType V.toScheme (M.restrict V.ι)) :
    affineLocallyFiniteType (W ⊔ V).toScheme (M.restrict (W ⊔ V).ι) :=
  affineLocallyFiniteType_restrict_sup M W V hW hV

end AlgebraicGeometry.Scheme.Modules.QuasiCoherent
