/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Flat.Generic.Spec
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Generic flatness over an integral Noetherian base

Let `S` be an integral locally Noetherian scheme, `f : X ⟶ S` locally of finite type and
quasi-compact, and `F` an affine-locally finite-type quasicoherent `X`-module. Then there is a
nonempty open `U ⊆ S` such that at every `x` with `f x ∈ U` the actual stalk of `F` is flat
over `𝒪_{S, f x}` through `f.stalkMap x` (Nitsure, arXiv:math/0504590v1, Thm 4.2, p. 19).
The statements assert only some nonempty open; the proof constructs it as a basic open
`S.basicOpen a` of a nonempty affine open `V` of `S`, with `a ≠ 0` in the Noetherian domain
`Γ(S, V)`. Only local Noetherianity of `S` is used (Nitsure assumes `S` Noetherian), and
coherence is encoded as `QuasiCoherent.affineLocallyFiniteType`.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

/-- Flatness over the stalk of an open target gives flatness over the ambient stalk, through
the actual stalk-ring isomorphism of the open immersion: the pointwise converse of
`relativeFlat_of_comp_isOpenImmersion`. -/
theorem flat_stalk_comp_of_flat_stalk_of_isOpenImmersion {W V Y : Scheme.{u}} (b : W ⟶ V)
    (j : V ⟶ Y) [IsOpenImmersion j] (N : W.Modules) (x : W)
    (h : Module.Flat (V.presheaf.stalk (b x))
      ((ModuleCat.restrictScalars (b.stalkMap x).hom).obj ((moduleStalk W x).obj N))) :
    Module.Flat (Y.presheaf.stalk ((b ≫ j) x))
      ((ModuleCat.restrictScalars ((b ≫ j).stalkMap x).hom).obj ((moduleStalk W x).obj N)) := by
  let T := (moduleStalk W x).obj N
  have hc : ((b ≫ j).stalkMap x).hom =
      (b.stalkMap x).hom.comp (j.stalkMap (b x)).hom :=
    congrArg CommRingCat.Hom.hom (Scheme.Hom.stalkMap_comp b j x)
  let E := (ModuleCat.restrictScalarsComp' (j.stalkMap (b x)).hom (b.stalkMap x).hom
    ((b ≫ j).stalkMap x).hom hc).app T
  have : Module.Flat (Y.presheaf.stalk (j (b x)))
      ((ModuleCat.restrictScalars (j.stalkMap (b x)).hom).obj
        ((ModuleCat.restrictScalars (b.stalkMap x).hom).obj T)) :=
    flat_restrictScalars (j.stalkMap (b x)).hom
      (RingHom.Flat.of_bijective (asIso (j.stalkMap (b x))).commRingCatIsoToRingEquiv.bijective)
      ((ModuleCat.restrictScalars (b.stalkMap x).hom).obj T)
  exact (Module.Flat.equiv_iff E.toLinearEquiv).mpr this

-- The `Module` instances on the carriers of `ModuleCat.restrictScalars` objects are identified
-- with those of the original modules only by unfolding below instance transparency.
set_option backward.isDefEq.respectTransparency false in
/-- **Generic flatness** (Nitsure, arXiv:math/0504590v1, Thm 4.2, p. 19). Let `S` be an
integral locally Noetherian scheme, `f : X ⟶ S` locally of finite type and quasi-compact, and
`F` an affine-locally finite-type quasicoherent `X`-module. Then there is a nonempty open
`U ⊆ S` such that, at every `x : X` with `f x ∈ U`, the actual stalk of `F` is flat over the
base local ring `𝒪_{S, f x}` through `f.stalkMap x`. -/
theorem exists_nonempty_open_flat_stalk_of_isIntegral {X S : Scheme.{u}} (f : X ⟶ S)
    [IsIntegral S] [IsLocallyNoetherian S] [LocallyOfFiniteType f] [QuasiCompact f]
    (F : X.Modules) (hF : QuasiCoherent.affineLocallyFiniteType X F) :
    ∃ U : S.Opens, (U : Set S).Nonempty ∧ ∀ x : X, f x ∈ U →
      Module.Flat (S.presheaf.stalk (f x))
        ((ModuleCat.restrictScalars (f.stalkMap x).hom).obj ((moduleStalk X x).obj F)) := by
  classical
  obtain ⟨s⟩ : Nonempty S := inferInstance
  obtain ⟨_, ⟨V, hV, rfl⟩, hsV, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ s) isOpen_univ
  have hV' : IsAffineOpen V := hV
  have : Nonempty V := ⟨⟨s, hsV⟩⟩
  have : IsDomain Γ(S, V) := IsIntegral.component_integral V
  have : IsNoetherianRing Γ(S, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  -- the ring map attached to an affine open over `V` and generic freeness of its sections
  have key : ∀ W : X.Opens, ∃ a : Γ(S, V), a ≠ 0 ∧ ∀ (hW : IsAffineOpen W)
      (hle : W ≤ f ⁻¹ᵁ V), Module.Free (Localization.Away a) (LocalizedModule.Away a
        ((ModuleCat.restrictScalars (f.appLE V W hle).hom).obj
          (moduleSpecΓFunctor.obj (F.restrict hW.fromSpec)))) := by
    intro W
    by_cases hW : IsAffineOpen W ∧ W ≤ f ⁻¹ᵁ V
    · obtain ⟨hW, hle⟩ := hW
      let φ : Γ(S, V) ⟶ Γ(X, W) := f.appLE V W hle
      let := φ.hom.toAlgebra
      have : Algebra.FiniteType Γ(S, V) Γ(X, W) :=
        HasRingHomProperty.appLE @LocallyOfFiniteType f inferInstance ⟨V, hV⟩ ⟨W, hW⟩ hle
      let E := moduleSpecΓFunctor.obj (F.restrict hW.fromSpec)
      have : Module.Finite Γ(X, W) E := (hF Γ(X, W) hW.fromSpec).2
      let : IsScalarTower Γ(S, V) Γ(X, W) ((ModuleCat.restrictScalars φ.hom).obj E) :=
        IsScalarTower.of_algebraMap_smul fun _ _ => rfl
      have : Module.Finite Γ(X, W) ((ModuleCat.restrictScalars φ.hom).obj E) :=
        inferInstanceAs (Module.Finite Γ(X, W) E)
      obtain ⟨a, ha, hfree⟩ := Module.Finite.exists_ne_zero_free_localizedModule_away
        (A := Γ(S, V)) (B := Γ(X, W)) ((ModuleCat.restrictScalars φ.hom).obj E)
      exact ⟨a, ha, fun _ _ => hfree⟩
    · exact ⟨1, one_ne_zero, fun h h' => absurd ⟨h, h'⟩ hW⟩
  choose aW haW hfreeW using key
  -- finitely many affine opens cover `f ⁻¹ V`
  obtain ⟨Us, hUsB, hUsfin, hUs⟩ := X.isBasis_affineOpens.exists_finite_of_isCompact
    (U := f ⁻¹ᵁ V) (QuasiCompact.isCompact_preimage _ V.2 hV'.isCompact)
  have ha : ∏ W ∈ hUsfin.toFinset, aW W ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun W _ => haW W
  refine ⟨S.basicOpen (∏ W ∈ hUsfin.toFinset, aW W), ?_, fun x hx => ?_⟩
  · refine ⟨hV'.fromSpec ⟨⊥, Ideal.isPrime_bot⟩, ?_⟩
    have h : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum Γ(S, V)) ∈
        PrimeSpectrum.basicOpen (∏ W ∈ hUsfin.toFinset, aW W) := by
      rw [PrimeSpectrum.mem_basicOpen]
      simpa using ha
    rw [← hV'.fromSpec_preimage_basicOpen] at h
    exact h
  · have hxV : x ∈ f ⁻¹ᵁ V := S.basicOpen_le _ hx
    rw [hUs] at hxV
    obtain ⟨W, hWUs, hxW⟩ := TopologicalSpace.Opens.mem_sSup.mp hxV
    have hW : IsAffineOpen W := hUsB hWUs
    have hle : W ≤ f ⁻¹ᵁ V := hUs ▸ le_sSup hWUs
    obtain ⟨y, rfl⟩ : x ∈ Set.range hW.fromSpec := hW.range_fromSpec.symm ▸ hxW
    let φ : Γ(S, V) ⟶ Γ(X, W) := f.appLE V W hle
    have := hfreeW W hW hle
    have : Module.Free (Localization.Away (∏ W ∈ hUsfin.toFinset, aW W))
        (LocalizedModule.Away (∏ W ∈ hUsfin.toFinset, aW W)
          ((ModuleCat.restrictScalars φ.hom).obj
            (moduleSpecΓFunctor.obj (F.restrict hW.fromSpec)))) :=
      Module.free_localizedModule_away_of_dvd
        (Finset.dvd_prod_of_mem aW (hUsfin.mem_toFinset.mpr hWUs))
    have hSpec : Spec.map φ ≫ hV'.fromSpec = hW.fromSpec ≫ f :=
      IsAffineOpen.SpecMap_appLE_fromSpec f hV' hW hle
    have hy : φ.hom (∏ W ∈ hUsfin.toFinset, aW W) ∉ y.asIdeal := by
      have h1 : hV'.fromSpec ((Spec.map φ) y) = f (hW.fromSpec y) := by
        change (Spec.map φ ≫ hV'.fromSpec) y = (hW.fromSpec ≫ f) y
        rw [hSpec]
      have h2 : (Spec.map φ) y ∈ hV'.fromSpec ⁻¹ᵁ S.basicOpen (∏ W ∈ hUsfin.toFinset, aW W) := by
        change hV'.fromSpec ((Spec.map φ) y) ∈ S.basicOpen (∏ W ∈ hUsfin.toFinset, aW W)
        rw [h1]
        exact hx
      rw [hV'.fromSpec_preimage_basicOpen, PrimeSpectrum.mem_basicOpen] at h2
      exact h2
    have : (F.restrict hW.fromSpec).IsQuasicoherent := (hF Γ(X, W) hW.fromSpec).1
    have H := flat_stalk_specMap_of_flat_localizedModule_away φ (F.restrict hW.fromSpec)
      (∏ W ∈ hUsfin.toFinset, aW W) y hy
    have H2 := flat_stalk_comp_of_flat_stalk_of_isOpenImmersion (Spec.map φ) hV'.fromSpec
      (F.restrict hW.fromSpec) y H
    rw [hSpec] at H2
    exact flat_stalk_of_flat_stalk_restrict hW.fromSpec f F y H2

/-- Flatness of an actual stalk over the base local ring gives flatness of the restricted
stalk along an open immersion of sources: the pointwise form of `relativeFlat_restrict`. -/
theorem flat_stalk_restrict_of_flat_stalk {U X Y : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (f : X ⟶ Y) (M : X.Modules) (x : U)
    (h : Module.Flat (Y.presheaf.stalk (f (j x)))
      ((ModuleCat.restrictScalars (f.stalkMap (j x)).hom).obj ((moduleStalk X (j x)).obj M))) :
    Module.Flat (Y.presheaf.stalk ((j ≫ f) x))
      ((ModuleCat.restrictScalars ((j ≫ f).stalkMap x).hom).obj
        ((moduleStalk U x).obj (M.restrict j))) := by
  let T := (moduleStalk U x).obj (M.restrict j)
  have he : ((j ≫ f).stalkMap x).hom =
      (j.stalkMap x).hom.comp (f.stalkMap (j x)).hom :=
    congrArg CommRingCat.Hom.hom (Scheme.Hom.stalkMap_comp j f x)
  let e := (ModuleCat.restrictScalarsComp' (f.stalkMap (j x)).hom (j.stalkMap x).hom
      ((j ≫ f).stalkMap x).hom he).app T ≪≫
    (ModuleCat.restrictScalars (f.stalkMap (j x)).hom).mapIso
      ((restrictModuleStalkIso j x).app M)
  exact (Module.Flat.equiv_iff e.toLinearEquiv).mpr h

/-- **Generic flatness** in `relativeFlat` form (Nitsure, arXiv:math/0504590v1, Thm 4.2,
p. 19): over a nonempty open `U ⊆ S`, the restriction of `F` to `f ⁻¹ U` is relatively flat
for the restricted morphism `f ∣_ U`. -/
theorem exists_nonempty_open_relativeFlat_of_isIntegral {X S : Scheme.{u}} (f : X ⟶ S)
    [IsIntegral S] [IsLocallyNoetherian S] [LocallyOfFiniteType f] [QuasiCompact f]
    (F : X.Modules) (hF : QuasiCoherent.affineLocallyFiniteType X F) :
    ∃ U : S.Opens, (U : Set S).Nonempty ∧ relativeFlat (f ∣_ U) (F.restrict (f ⁻¹ᵁ U).ι) := by
  obtain ⟨U, hU, h⟩ := exists_nonempty_open_flat_stalk_of_isIntegral f F hF
  refine ⟨U, hU, relativeFlat_of_comp_isOpenImmersion (f ∣_ U) U.ι ?_⟩
  rw [morphismRestrict_ι]
  intro x
  exact flat_stalk_restrict_of_flat_stalk (f ⁻¹ᵁ U).ι f F x (h _ x.2)

end AlgebraicGeometry.Scheme.Modules
