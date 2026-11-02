/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Normalization.BaseChange.AffineLocalization
public import Aglib.AlgebraicGeometry.Stalk.FlatBaseChange
public import Aglib.AlgebraicGeometry.Normalization.BaseChange.Composition

/-!
# Normalization over an affine base and its actual stalk

The localization structure is derived from the affine stalk theorem using
the original germ. The comparison remains the native normalization pullback.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- On an affine base, normalization commutes with its actual stalk morphism.
No localization, normality or completion comparison is a caller premise. -/
theorem normalizationPullback_isIso_fromSpecStalk_of_isAffine
    {X S : Scheme.{u}} [IsAffine S] (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] (s : S) :
    IsIso (f.normalizationPullback (S.fromSpecStalk s)) := by
  let g := S.fromSpecStalk s
  let M := ((isAffineOpen_top S).primeIdealOf ⟨s, trivial⟩).asIdeal.primeCompl
  let : Flat g := Scheme.fromSpecStalk_flat S s
  apply normalizationPullback_isIso_of_affineLocalization f g M
  let := (g.appLE ⊤ ⊤ (by simp)).hom.toAlgebra
  let : Algebra Γ(S, ⊤) (S.presheaf.stalk s) :=
    (S.presheaf.germ ⊤ s trivial).hom.toAlgebra
  let : IsLocalization M (S.presheaf.stalk s) :=
    (isAffineOpen_top S).isLocalization_stalk ⟨s, trivial⟩
  have hg : g.appLE ⊤ ⊤ (by simp) =
      S.presheaf.germ ⊤ s trivial ≫ (Scheme.ΓSpecIso (S.presheaf.stalk s)).inv := by
    apply (cancel_mono (Scheme.ΓSpecIso (S.presheaf.stalk s)).hom).mp
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    change (S.fromSpecStalk s).appLE ⊤ ⊤ _ ≫ _ = _
    rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app (show s ∈ (⊤ : S.Opens) from trivial)]
    have hcomp : (homOfLE (show (S.fromSpecStalk s) ⁻¹ᵁ ⊤ ≤ ⊤ from le_top)).op ≫
        (homOfLE (show (⊤ : (Spec (S.presheaf.stalk s)).Opens) ≤
          (S.fromSpecStalk s) ⁻¹ᵁ ⊤ from by simp)).op =
          𝟙 (op (⊤ : (Spec (S.presheaf.stalk s)).Opens)) := Subsingleton.elim _ _
    simp only [Category.assoc, ← Functor.map_comp, hcomp]
    rw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id, Category.comp_id]
  let e : S.presheaf.stalk s ≃ₐ[Γ(S, ⊤)] Γ(Spec (S.presheaf.stalk s), ⊤) :=
    { (Scheme.ΓSpecIso (S.presheaf.stalk s)).symm.commRingCatIsoToRingEquiv with
      commutes' r := by
        change (Scheme.ΓSpecIso (S.presheaf.stalk s)).inv
          (S.presheaf.germ ⊤ s trivial r) = g.appLE ⊤ ⊤ (by simp) r
        exact congr($(hg) r).symm }
  exact IsLocalization.isLocalization_of_algEquiv M e

/-- Relative normalization commutes with the original stalk map on any base.
An affine neighbourhood is used only in the proof, not in the statement. -/
theorem normalizationPullback_isIso_fromSpecStalk
    {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f] (s : S) :
    IsIso (f.normalizationPullback (S.fromSpecStalk s)) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hsU, _⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ s) isOpen_univ
  let V : S.Opens := U
  have hV : IsAffineOpen V := hU
  let : IsAffine V.toScheme := hV
  let p := pullback.snd f V.ι
  let k := V.toScheme.fromSpecStalk ⟨s, hsU⟩
  let e := Spec.map (inv (V.ι.stalkMap ⟨s, hsU⟩))
  let : IsIso (p.normalizationPullback k) :=
    normalizationPullback_isIso_fromSpecStalk_of_isAffine p ⟨s, hsU⟩
  let : IsIso e := inferInstance
  let : IsIso ((pullback.snd p k).normalizationPullback e) := inferInstance
  have hk : IsIso (p.normalizationPullback (V.fromSpecStalkOfMem s hsU)) :=
    normalizationPullback_isIso_comp p k e
  let := hk
  have hfull : IsIso (f.normalizationPullback (V.fromSpecStalkOfMem s hsU ≫ V.ι)) :=
    normalizationPullback_isIso_comp f V.ι (V.fromSpecStalkOfMem s hsU)
  have hc : V.fromSpecStalkOfMem s hsU ≫ V.ι = S.fromSpecStalk s :=
    Scheme.Opens.fromSpecStalkOfMem_ι V s hsU
  rw [hc] at hfull
  exact hfull

end AlgebraicGeometry.Scheme.Hom
