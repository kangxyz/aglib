/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.FittingIdeal.Pullback
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Rank
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Restriction
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Affine.Projective
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Affine.Flat
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Locality
public import Aglib.RingTheory.FittingIdeal.Stratification
public import Mathlib.AlgebraicGeometry.ResidueField

/-!
# Fitting ideal sheaves, fibre ranks and finite local freeness

Let `G` be a quasi-coherent `𝒪_T`-module of finite type
(`QuasiCoherent.affineLocallyFiniteType`). The results on fibre ranks also assume finite
presentation (`[G.IsFinitePresentation]`); see each statement.

* `Scheme.Modules.sheafRank_le_iff_notMem_support`: the fibre rank `sheafRank G y` (the dimension of
  the fibre of `G` over the residue field at `y`) is at most `k` if and only if `y` lies outside
  `V(Fitt_k(G))` (Stacks Project, Tag 07ZC, (1) ⇔ (2), through the pullback
  `fittingIdealSheaf_comap` along `Spec κ(y) ⟶ T`). Consequently `Fitt_k(G) = 𝒪_T` when every
  fibre has dimension at most `k` (`fittingIdealSheaf_eq_top_of_sheafRank_le`), and the points of
  fibre dimension at least `r` form a closed set (`isClosed_setOf_le_sheafRank`).
  On `Spec A` the criterion reads off the global sections:
  `sheafRank_le_iff_fittingIdeal_moduleSpecΓFunctor`, `sheafRank G y ≤ k` if and only if
  `Fitt_k(Γ(G)) ⊄ y`.
* `Scheme.Modules.sheafRank_eq_of_fittingIdealSheaf`: if `Fitt_k(G) = 0` for `k < r` and
  `Fitt_r(G) = 𝒪_T`, every fibre has dimension `r`; `sheafRank_pullback`: fibre ranks are
  compatible with arbitrary pullback.
* `Scheme.Modules.isFiniteLocallyFree_of_fittingIdealSheaf`: these Fitting conditions give finite
  local freeness (Stacks, Tag 0C3G, (2) ⇒ (1)); only finite type is used.
* `Scheme.Modules.fittingIdealSheaf_eq_of_sheafHasRank`: conversely, a finite locally free sheaf
  of constant rank `r` (`SheafHasRank G r`) has `Fitt_k(G) = 0` for `k < r` and `Fitt_r(G) = 𝒪_T`;
  `fittingIdealSheaf_eq_bot_and_eq_top_iff_sheafHasRank` is the equivalence (Stacks, Tag 0C3G),
  for `G` of finite type.
  On an affine open the sections are finitely presented and projective
  (`projective_globalSections_of_finiteLocallyFree`), every stalk rank is the fibre rank `r`, and
  the algebraic criterion `Module.fittingIdeal_eq_bot_and_eq_top_iff_projective` applies
  (Stacks, Tag 07ZD).

The algebraic inputs live at their algebraic owners: `Module.fittingIdeal_compHom_of_bijective`
(Fitting ideals along a ring isomorphism), `Module.Finite.compHom_of_surjective`,
`Module.finitePresentation_and_flat_of_forall_free` (Stacks, Tag 00NX) and Mathlib's
`Module.rankAtStalk_eq` (stalk rank as a fibre dimension). The support criterion on affine charts
is `IdealSheafData.fromSpec_mem_support_iff`.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Opposite TopologicalSpace
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

variable {T : Scheme.{u}} (G : T.Modules)

/-- **Fibre ranks and Fitting ideal sheaves** (Stacks Project, Tag 07ZC, (1) ⇔ (2)): for a finitely
presented `G`, the fibre of `G` at `y` has dimension at most `k` if and only if `y` lies outside the
support of `Fitt_k(G)`. -/
theorem sheafRank_le_iff_notMem_support [G.IsFinitePresentation]
    (hG : QuasiCoherent.affineLocallyFiniteType T G) (y : T) (k : ℕ) :
    sheafRank G y ≤ k ↔ y ∉ (fittingIdealSheaf G hG k).support := by
  have hpt := QuasiCoherent.affineLocallyFiniteType_pullback_of_finitePresentation
    (T.fromSpecResidueField y) G
  have h1 : y ∉ (fittingIdealSheaf G hG k).support ↔
      fittingIdealSheaf ((pullback (T.fromSpecResidueField y)).obj G) hpt k = ⊤ := by
    rw [← fittingIdealSheaf_comap (T.fromSpecResidueField y) G hG hpt k,
      ← IdealSheafData.range_subset_compl_support_iff, Scheme.range_fromSpecResidueField,
      Set.singleton_subset_iff]
    rfl
  rw [h1]
  have h2 : fittingIdealSheaf ((pullback (T.fromSpecResidueField y)).obj G) hpt k = ⊤ ↔
      Module.fittingIdeal Γ(Spec (T.residueField y), ⊤)
        Γ((pullback (T.fromSpecResidueField y)).obj G, ⊤) k = ⊤ := by
    constructor
    · intro h
      exact (congrArg (fun I => I.ideal ⟨⊤, isAffineOpen_top _⟩) h).trans rfl
    · intro h
      exact IdealSheafData.ext_of_isAffine (h.trans rfl)
  rw [h2]
  have hfin : Module.Finite Γ(Spec (T.residueField y), ⊤)
      Γ((pullback (T.fromSpecResidueField y)).obj G, ⊤) :=
    QuasiCoherent.finite_sections_of_affineLocallyFiniteType _ hpt ⟨⊤, isAffineOpen_top _⟩
  have hb : Function.Bijective
      (Scheme.ΓSpecIso (CommRingCat.of (T.residueField y))).inv.hom :=
    ConcreteCategory.bijective_of_isIso _
  have : Module.Finite (T.residueField y)
      (moduleFibre (T.residueField y) G (T.fromSpecResidueField y)) :=
    Module.Finite.compHom_of_surjective (M := Γ((pullback (T.fromSpecResidueField y)).obj G, ⊤)) _
      hb.2
  have h3 := Module.fittingIdeal_compHom_of_bijective
    (M := Γ((pullback (T.fromSpecResidueField y)).obj G, ⊤)) _ hb k
  rw [sheafRank, ← Module.fittingIdeal_eq_top_iff_finrank_le]
  exact (iff_of_eq (congrArg (· = ⊤) h3)).trans Ideal.comap_eq_top_iff

/-- Fibre ranks are compatible with pullback: for a finitely presented `G` on `T` and
`f : T' ⟶ T`, the fibre of `f^* G` at `t` has the dimension of the fibre of `G` at `f t`. -/
theorem sheafRank_pullback {T' : Scheme.{u}} (f : T' ⟶ T) [G.IsFinitePresentation] (t : T') :
    sheafRank ((pullback f).obj G) t = sheafRank G (f t) := by
  have hG := QuasiCoherent.affineLocallyFiniteType_of_finitePresentation G
  have hfG := QuasiCoherent.affineLocallyFiniteType_pullback_of_finitePresentation f G
  have key : ∀ k, sheafRank ((pullback f).obj G) t ≤ k ↔ sheafRank G (f t) ≤ k := fun k => by
    rw [sheafRank_le_iff_notMem_support _ hfG, sheafRank_le_iff_notMem_support G hG,
      ← fittingIdealSheaf_comap f G hG hfG, IdealSheafData.support_comap]
    exact Iff.rfl
  exact le_antisymm ((key _).mpr le_rfl) ((key _).mp le_rfl)

/-- If `Fitt_k(G) = 0` for `k < r` and `Fitt_r(G) = 𝒪_T`, every fibre of `G` has dimension `r`. -/
theorem sheafRank_eq_of_fittingIdealSheaf [G.IsFinitePresentation]
    (hG : QuasiCoherent.affineLocallyFiniteType T G) {r : ℕ}
    (h0 : ∀ k < r, fittingIdealSheaf G hG k = ⊥) (h1 : fittingIdealSheaf G hG r = ⊤) (y : T) :
    sheafRank G y = r := by
  have hle : sheafRank G y ≤ r := by
    rw [sheafRank_le_iff_notMem_support G hG y r, h1, IdealSheafData.support_top]
    exact id
  cases r with
  | zero => omega
  | succ r =>
    have : ¬sheafRank G y ≤ r := by
      rw [sheafRank_le_iff_notMem_support G hG y r, h0 r r.lt_succ_self,
        IdealSheafData.support_bot, not_not]
      exact Set.mem_univ y
    omega

/-- **Fitting ideals of a finite locally free sheaf of constant rank** (Stacks Project, Tag 0C3G,
(1) ⇒ (2)):
if `G` has a finite local basis of rank `r`, then `Fitt_k(G) = 0` for `k < r` and
`Fitt_r(G) = 𝒪_T`. -/
theorem fittingIdealSheaf_eq_of_sheafHasRank (hG : QuasiCoherent.affineLocallyFiniteType T G)
    {r : ℕ} (h : SheafHasRank G r) :
    (∀ k < r, fittingIdealSheaf G hG k = ⊥) ∧ fittingIdealSheaf G hG r = ⊤ := by
  have : IsFiniteLocallyFree T G := h.isFiniteLocallyFree
  have hrank := (sheafHasRank_iff_rank_eq G r).mp h
  have key : ∀ V : T.affineOpens,
      (∀ k < r, Module.fittingIdeal Γ(T, V) Γ(G, V) k = ⊥) ∧
        Module.fittingIdeal Γ(T, V) Γ(G, V) r = ⊤ := by
    intro V
    have hV : IsAffineOpen V.1 := V.2
    let e := QuasiCoherent.AffineOpenSections.toSpecTopSectionsLinearEquiv G hV
    have : Module.FinitePresentation Γ(T, V) Γ(G.restrict hV.fromSpec, ⊤) :=
      finitePresentation_globalSections_of_finiteLocallyFree Γ(T, V) (G.restrict hV.fromSpec)
    have : Module.Projective Γ(T, V) Γ(G.restrict hV.fromSpec, ⊤) :=
      projective_globalSections_of_finiteLocallyFree Γ(T, V) (G.restrict hV.fromSpec)
    have : Module.FinitePresentation Γ(T, V) Γ(G, V) := Module.FinitePresentation.of_equiv e.symm
    have : Module.Projective Γ(T, V) Γ(G, V) := Module.Projective.of_equiv e.symm
    refine Module.fittingIdeal_eq_bot_and_eq_top_iff_projective.mpr ⟨inferInstance, fun p => ?_⟩
    rw [Module.rankAtStalk_eq]
    have hk : ∀ k, Module.finrank p.asIdeal.ResidueField
        (p.asIdeal.ResidueField ⊗[Γ(T, V)] Γ(G, V)) ≤ k ↔ r ≤ k := fun k => by
      rw [Module.finrank_residueField_tensor_le_iff, ← ideal_fittingIdealSheaf G hG k V,
        ← IdealSheafData.fromSpec_mem_support_iff, ← sheafRank_le_iff_notMem_support G hG, hrank]
    exact le_antisymm ((hk r).mpr le_rfl) ((hk _).mp le_rfl)
  refine ⟨fun k hk => IdealSheafData.ext (funext fun V => (key V).1 k hk), ?_⟩
  exact IdealSheafData.ext (funext fun V => (key V).2)

/-- **Fitting conditions give finite local freeness** (Stacks Project, Tag 0C3G, (2) ⇒ (1)): a
quasi-coherent sheaf of finite type with `Fitt_k(G) = 0` for `k < r` and `Fitt_r(G) = 𝒪_T` is
finite locally free. On each affine chart the sections are stalkwise free of rank `r`, hence
finitely presented and flat (`Module.finitePresentation_and_flat_of_forall_free`), and
`affineFinitePresentationFlatSheaf_locallyFree` applies. -/
theorem isFiniteLocallyFree_of_fittingIdealSheaf (hG : QuasiCoherent.affineLocallyFiniteType T G)
    {r : ℕ} (h0 : ∀ k < r, fittingIdealSheaf G hG k = ⊥) (h1 : fittingIdealSheaf G hG r = ⊤) :
    IsFiniteLocallyFree T G := by
  let j : ∀ V : T.affineOpens, Spec Γ(T, V) ⟶ T := fun V => IsAffineOpen.fromSpec (U := V.1) V.2
  have : ∀ V : T.affineOpens, IsOpenImmersion (j V) := fun V =>
    IsAffineOpen.isOpenImmersion_fromSpec (U := V.1) V.2
  refine finiteLocallyFree_of_affineCharts G (fun V : T.affineOpens => Γ(T, V)) j ?_ fun V => ?_
  · intro x
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
      T.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    have hV' : IsAffineOpen V := hV
    obtain ⟨y, hy⟩ : x ∈ Set.range hV'.fromSpec := by
      rw [hV'.range_fromSpec]
      exact hxV
    exact ⟨⟨V, hV⟩, y, hy⟩
  · have hV : IsAffineOpen V.1 := V.2
    have : (G.restrict hV.fromSpec).IsQuasicoherent := (hG Γ(T, V) hV.fromSpec).1
    have : Module.Finite Γ(T, V) (moduleSpecΓFunctor.obj (G.restrict hV.fromSpec)) :=
      (hG Γ(T, V) hV.fromSpec).2
    let e := QuasiCoherent.AffineOpenSections.toSpecTopSectionsLinearEquiv G hV
    have hfit : (∀ k < r, Module.fittingIdeal Γ(T, V)
          (moduleSpecΓFunctor.obj (G.restrict hV.fromSpec)) k = ⊥) ∧
        Module.fittingIdeal Γ(T, V) (moduleSpecΓFunctor.obj (G.restrict hV.fromSpec)) r = ⊤ :=
      ⟨fun k hk => (Module.fittingIdeal_congr e k).symm.trans
          (congrArg (fun I => I.ideal V) (h0 k hk)),
        (Module.fittingIdeal_congr e r).symm.trans (congrArg (fun I => I.ideal V) h1)⟩
    obtain ⟨hfp, hflat⟩ := Module.finitePresentation_and_flat_of_forall_free
      (Module.fittingIdeal_eq_bot_and_eq_top_iff.mp hfit)
    exact affineFinitePresentationFlatSheaf_locallyFree (G.restrict hV.fromSpec)

/-- **Fitting ideal sheaves detect finite local freeness of constant rank** (Stacks Project,
Tag 0C3G, (1) ⇔ (2)): for `G` of finite type, `Fitt_k(G) = 0` for `k < r` and
`Fitt_r(G) = 𝒪_T` if and only if `G` has a finite local basis of rank `r`. -/
theorem fittingIdealSheaf_eq_bot_and_eq_top_iff_sheafHasRank
    (hG : QuasiCoherent.affineLocallyFiniteType T G) (r : ℕ) :
    ((∀ k < r, fittingIdealSheaf G hG k = ⊥) ∧ fittingIdealSheaf G hG r = ⊤) ↔
      SheafHasRank G r := by
  refine ⟨fun ⟨h0, h1⟩ => ?_, fittingIdealSheaf_eq_of_sheafHasRank G hG⟩
  have := isFiniteLocallyFree_of_fittingIdealSheaf G hG h0 h1
  exact (sheafHasRank_iff_rank_eq G r).mpr (sheafRank_eq_of_fittingIdealSheaf G hG h0 h1)

/-- If every fibre of `F` has dimension at most `k`, the Fitting ideal sheaf `Fitt_k(F)` is the unit
ideal sheaf. -/
theorem fittingIdealSheaf_eq_top_of_sheafRank_le (F : T.Modules)
    (hF : QuasiCoherent.affineLocallyFiniteType T F) [F.IsFinitePresentation] (k : ℕ)
    (h : ∀ y, sheafRank F y ≤ k) : fittingIdealSheaf F hF k = ⊤ := by
  rw [← IdealSheafData.support_eq_bot_iff]
  exact eq_bot_iff.mpr fun y hy => absurd hy ((sheafRank_le_iff_notMem_support F hF y k).mp (h y))

/-- The points of fibre dimension at least `r` form a closed set. -/
theorem isClosed_setOf_le_sheafRank (F : T.Modules)
    (hF : QuasiCoherent.affineLocallyFiniteType T F) [F.IsFinitePresentation] (r : ℕ) :
    IsClosed {y : T | r ≤ sheafRank F y} := by
  cases r with
  | zero => simp
  | succ k =>
    have : {y : T | k + 1 ≤ sheafRank F y} = (fittingIdealSheaf F hF k).support := by
      ext y
      simp only [Set.mem_ofPred_eq, SetLike.mem_coe]
      rw [← not_iff_not, not_le, Nat.lt_succ_iff]
      exact sheafRank_le_iff_notMem_support F hF y k
    rw [this]
    exact (fittingIdealSheaf F hF k).support.isClosed

/-- **Fibre ranks on an affine scheme through the Fitting ideals of global sections**: for a
finitely presented `G` on `Spec A` and a point `y`, the fibre of `G` at `y` has dimension at most
`k` if and only if `Fitt_k(Γ(G)) ⊄ y`, with `Γ(G)` the `A`-module `moduleSpecΓFunctor.obj G`. -/
theorem sheafRank_le_iff_fittingIdeal_moduleSpecΓFunctor {A : Type u} [CommRing A]
    (G : (Spec (CommRingCat.of A)).Modules) [G.IsFinitePresentation]
    (hG : QuasiCoherent.affineLocallyFiniteType _ G) (y : PrimeSpectrum A) (k : ℕ) :
    sheafRank G y ≤ k ↔ ¬Module.fittingIdeal A (moduleSpecΓFunctor.obj G) k ≤ y.asIdeal := by
  let V : (Spec (CommRingCat.of A)).affineOpens := ⟨⊤, isAffineOpen_top _⟩
  have htop : (⊤ : (Spec (CommRingCat.of A)).Opens).leTop = 𝟙 _ := Subsingleton.elim _ _
  let ψ : A →+* Γ(Spec (CommRingCat.of A), ⊤) :=
    ((Spec (CommRingCat.of A)).presheaf.map (⊤ : (Spec (CommRingCat.of A)).Opens).leTop.op).hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  have hψ : ψ = (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom := by
    simp only [ψ, htop, op_id, CategoryTheory.Functor.map_id]
    rfl
  have hψb : Function.Bijective ψ := by
    rw [hψ]
    exact ConcreteCategory.bijective_of_isIso _
  have hfin : Module.Finite Γ(Spec (CommRingCat.of A), ⊤) Γ(G, ⊤) :=
    QuasiCoherent.finite_sections_of_affineLocallyFiniteType G hG V
  have hfit : Module.fittingIdeal A (moduleSpecΓFunctor.obj G) k =
      (Module.fittingIdeal Γ(Spec (CommRingCat.of A), ⊤) Γ(G, ⊤) k).comap ψ :=
    Module.fittingIdeal_compHom_of_bijective (M := Γ(G, ⊤)) ψ hψb k
  let p : PrimeSpectrum Γ(Spec (CommRingCat.of A), ⊤) :=
    PrimeSpectrum.comap (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom y
  have hy : (show IsAffineOpen V.1 from V.2).fromSpec p = y := by
    change (isAffineOpen_top (Spec (CommRingCat.of A))).fromSpec p = y
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv]
    change PrimeSpectrum.comap (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom p = y
    ext1
    change Ideal.comap _ (Ideal.comap _ y.asIdeal) = y.asIdeal
    rw [Ideal.comap_comap, ← CommRingCat.hom_comp, Iso.inv_hom_id, CommRingCat.hom_id,
      Ideal.comap_id]
  have hp : y.asIdeal = p.asIdeal.comap ψ := by
    rw [hψ]
    change y.asIdeal = Ideal.comap _ (Ideal.comap _ y.asIdeal)
    rw [Ideal.comap_comap, ← CommRingCat.hom_comp, Iso.inv_hom_id, CommRingCat.hom_id,
      Ideal.comap_id]
  have key : y ∈ (fittingIdealSheaf G hG k).support ↔
      Module.fittingIdeal Γ(Spec (CommRingCat.of A), ⊤) Γ(G, ⊤) k ≤ p.asIdeal := by
    rw [← hy]
    exact IdealSheafData.fromSpec_mem_support_iff _ V p
  rw [sheafRank_le_iff_notMem_support G hG y k]
  refine not_congr (key.trans ?_)
  rw [hfit, hp, Ideal.comap_le_comap_iff_of_surjective ψ hψb.2]

end AlgebraicGeometry.Scheme.Modules
