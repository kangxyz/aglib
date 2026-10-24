/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Nonvanishing.Pullback
public import Aglib.AlgebraicGeometry.Modules.Invertible.FieldMaps
public import Aglib.AlgebraicGeometry.Modules.Invertible.FibrewiseIsomorphism
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed

/-! # Actual trivializations from nowhere-vanishing sections

The actual unit-module map associated to a nowhere-vanishing section is an
isomorphism. The proof retains the native pullback-adjunction section and
tests the original line-bundle map at geometric points. Consequently a
section nonvanishing on one fibre of a universally closed morphism trivializes
the actual bundle after shrinking the base around that fibre.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.Modules.Invertible.Nonvanishing

variable {X Y : Scheme.{u}}

/-- The literal unit-module map of a nowhere-vanishing actual section is an
isomorphism. No reducedness or Noetherian hypothesis is needed. -/
theorem section_isIso_of_nonvanishingOpen_eq_top (L : LineBundle X)
    (s : Γ(L.val, ⊤)) (hs : nonvanishingOpen L s = ⊤) :
    IsIso ((unitHomGlobalSectionsEquiv X L.val).symm s) := by
  let O : LineBundle X := ⟨SheafOfModules.unit X.ringCatSheaf, by
    rw [isLocallyRankOne_iff_local_unit]
    intro x
    exact ⟨⊤, trivial, ⟨Iso.refl _⟩⟩⟩
  let φ : O.val ⟶ L.val := (unitHomGlobalSectionsEquiv X L.val).symm s
  apply lineBundleMap_isIso_of_geometricPullback_isIso O L φ
  intro K _ _ t
  apply fieldLineBundleMap_isIso_of_ne_zero K (pullbackLineBundle t O)
    (pullbackLineBundle t L) ((Scheme.Modules.pullback t).map φ)
  intro hz
  have hn := (pullbackPushforwardAdjunction t).unit.naturality φ
  have he := congrArg (fun q => q.val.app (op ⊤) (1 : Γ(X, ⊤))) hn
  change pullbackSection t L.val (φ.val.app (op ⊤) (1 : Γ(X, ⊤))) =
    ((Scheme.Modules.pullback t).map φ).val.app (op ⊤)
      (pullbackSection t O.val (1 : Γ(X, ⊤))) at he
  have hφ : φ.val.app (op ⊤) (1 : Γ(X, ⊤)) = s :=
    (unitHomGlobalSectionsEquiv X L.val).apply_symm_apply s
  have hzero : pullbackSection t L.val s = 0 := by
    rw [hφ, hz] at he
    exact he
  have htop : nonvanishingOpen (pullbackLineBundle t L)
      (pullbackSection t L.val s) = ⊤ := by
    rw [nonvanishingOpen_pullback, hs]
    rfl
  rw [hzero, nonvanishingOpen_zero] at htop
  have hmem : (IsLocalRing.closedPoint K : Spec (.of K)) ∈
      (⊥ : (Spec (.of K)).Opens) := by
    rw [htop]
    trivial
  exact hmem

/-- A nowhere-vanishing actual section supplies an actual unit isomorphism. -/
theorem trivial_of_nonvanishingOpen_eq_top (L : LineBundle X)
    (s : Γ(L.val, ⊤)) (hs : nonvanishingOpen L s = ⊤) :
    Nonempty (L.val ≅ SheafOfModules.unit X.ringCatSheaf) := by
  let := section_isIso_of_nonvanishingOpen_eq_top L s hs
  exact ⟨(asIso ((unitHomGlobalSectionsEquiv X L.val).symm s)).symm⟩

/-- Restricting to any open contained in the actual nonvanishing open gives
an actual trivialization of the pulled line bundle. -/
theorem trivial_on_open_of_le_nonvanishingOpen (L : LineBundle X)
    (s : Γ(L.val, ⊤)) (U : X.Opens) (hU : U ≤ nonvanishingOpen L s) :
    Nonempty (((Scheme.Modules.pullback U.ι).obj L.val) ≅
      SheafOfModules.unit U.toScheme.ringCatSheaf) := by
  apply trivial_of_nonvanishingOpen_eq_top (pullbackLineBundle U.ι L)
    (pullbackSection U.ι L.val s)
  rw [nonvanishingOpen_pullback]
  ext x
  exact ⟨fun _ => trivial, fun _ => hU x.property⟩

/-- A section nonvanishing on a whole fibre of a universally closed morphism
trivializes the actual bundle above some open neighbourhood of that point. -/
theorem exists_trivial_on_base_open_of_nonvanishing_on_fibre
    (f : X ⟶ Y) [UniversallyClosed f] (L : LineBundle X) (s : Γ(L.val, ⊤))
    (y : Y) (hy : ∀ x : X, f x = y → x ∈ nonvanishingOpen L s) :
    ∃ U : Y.Opens, y ∈ U ∧
      Nonempty (((Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj L.val) ≅
        SheafOfModules.unit (f ⁻¹ᵁ U).toScheme.ringCatSheaf) := by
  let U : Y.Opens := ⟨(f '' (nonvanishingOpen L s : Set X)ᶜ)ᶜ,
    (f.isClosedMap _ (nonvanishingOpen L s).isOpen.isClosed_compl).isOpen_compl⟩
  have hyU : y ∈ U := by
    rintro ⟨x, hx, hxy⟩
    exact hx (hy x hxy)
  refine ⟨U, hyU, trivial_on_open_of_le_nonvanishingOpen L s (f ⁻¹ᵁ U) ?_⟩
  intro x hx
  by_contra hn
  exact hx ⟨x, hn, rfl⟩

end AlgebraicGeometry.Scheme.Modules.Invertible.Nonvanishing
