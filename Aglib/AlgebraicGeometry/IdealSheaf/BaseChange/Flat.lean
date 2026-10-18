/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.IdealSheaf.BaseChange.Affine
public import Aglib.AlgebraicGeometry.IdealSheaf.Restriction
public import Aglib.AlgebraicGeometry.IdealSheaf.BaseChange.Isomorphism
public import Aglib.AlgebraicGeometry.Modules.Invertible.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Quotient-flat base change of actual scheme ideals

## Extraction basis

Existing proofs transferred from frozen dirty R5 revision
`79307ff88f07d34fd5c3edb859f799c55e38f290`. Source identities:

- `R5Lab/AlgebraicGeometry/Curves/RelativeDivisors/FlatIdealBaseChange.lean`, SHA-256
  `52ad81197b39689c02c7f936d7b8987c9dac2695568d56796cdb1c43743a6864`.

Actual objects, maps, universes and stated conditions are retained.
Native validation coverage is recorded separately in `docs/WORK_PLAN.md` and
the migration records; the source hashes above identify extraction inputs.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w t

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Modules
open LinearMap
open AlgebraicGeometry.Scheme.Modules.Invertible

section
namespace AlgebraicGeometry.Scheme.Hom

theorem flatQuotient_affine_idealPullbackMap_isIso
    {S T X Y D D' : Scheme.{u}}
    [IsAffine S] [IsAffine T] [IsAffine X] [IsAffine Y] [IsAffine D] [IsAffine D']
    (p : X ⟶ S) (q : T ⟶ S) (p' : Y ⟶ T) (b : Y ⟶ X)
    (i : D ⟶ X) (i' : D' ⟶ Y) (a : D' ⟶ D) (h : a ≫ i = i' ≫ b)
    (H : IsPullback b p' p q) (H' : IsPullback a i' i b)
    [IsClosedImmersion i] [Flat (i ≫ p)]
 :
    IsIso (idealPullbackMap i i' b a h) := by
  have hs : Spec.map a.appTop ≫ Spec.map i.appTop =
      Spec.map i'.appTop ≫ Spec.map b.appTop := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← Scheme.Hom.comp_appTop,
      ← Scheme.Hom.comp_appTop, h]
  have hflat : (p.appTop ≫ i.appTop).hom.Flat := by
    rw [← Scheme.Hom.comp_appTop]
    exact (i ≫ p).flat_appTop
  have : IsIso (idealPullbackMap (Spec.map i.appTop) (Spec.map i'.appTop)
      (Spec.map b.appTop) (Spec.map a.appTop) hs) :=
    flatQuotient_categorical_spectralIdealPullbackMap_isIso
      p.appTop i.appTop q.appTop b.appTop p'.appTop a.appTop i'.appTop
      (isPushout_appTop_of_isPullback H) (isPushout_appTop_of_isPullback H') hs
      (i.app_surjective ⊤ (isAffineOpen_top X)) hflat
  have := idealPullbackMap_isIso_of_iso_square
    (Spec.map i.appTop) i X.isoSpec.hom D.isoSpec.hom (Scheme.isoSpec_hom_naturality i)
  have := idealPullbackMap_isIso_of_iso_square
    (Spec.map i'.appTop) i' Y.isoSpec.hom D'.isoSpec.hom (Scheme.isoSpec_hom_naturality i')
  exact idealPullbackMap_isIso_of_isoSquares i i' b a h
    (Spec.map i.appTop) (Spec.map i'.appTop) (Spec.map b.appTop) (Spec.map a.appTop) hs
    X.isoSpec D.isoSpec Y.isoSpec D'.isoSpec
    (Scheme.isoSpec_hom_naturality i) (Scheme.isoSpec_hom_naturality i')
    (Scheme.isoSpec_hom_naturality b)

end AlgebraicGeometry.Scheme.Hom
end

section
namespace AlgebraicGeometry.Scheme.Hom

variable {X Y D D' S T : Scheme.{u}}

theorem restrictedSquareSourceMap_isPullback
    (i : D ⟶ X) (i' : D' ⟶ Y) (b : Y ⟶ X) (a : D' ⟶ D)
    (h : a ≫ i = i' ≫ b) (H : IsPullback a i' i b)
    (V : X.Opens) (W : Y.Opens) (hWV : W ≤ b ⁻¹ᵁ V) :
    IsPullback (restrictedSquareSourceMap i i' b a h V W hWV)
      (i' ∣_ W) (i ∣_ V) (b.resLE V W hWV) := by
  have heq : i' ⁻¹ᵁ W = a ⁻¹ᵁ (i ⁻¹ᵁ V) ⊓ i' ⁻¹ᵁ W := by
    apply le_antisymm
    · apply le_inf _ le_rfl
      rw [← Scheme.Hom.comp_preimage, h, Scheme.Hom.comp_preimage]
      exact i'.preimage_mono hWV
    · exact inf_le_right
  simpa only [restrictedSquareSourceMap, Scheme.Hom.resLE_eq_morphismRestrict] using
    (Scheme.Hom.isPullback_resLE H hWV le_rfl heq)

theorem restrictedIdealProjection_flat
    (p : X ⟶ S) (i : D ⟶ X) [Flat (i ≫ p)]
    (U : S.Opens) (V : X.Opens) (hVU : V ≤ p ⁻¹ᵁ U) :
    Flat ((i ∣_ V) ≫ p.resLE U V hVU) := by
  rw [← Scheme.Hom.resLE_eq_morphismRestrict, Scheme.Hom.resLE_comp_resLE]
  infer_instance

/-- Quotient-flat closed ideals commute with arbitrary cartesian base change. -/
theorem flatQuotient_idealPullbackMap_isIso
    {S T X Y D D' : Scheme.{u}}
    (p : X ⟶ S) (q : T ⟶ S) (p' : Y ⟶ T) (b : Y ⟶ X)
    (i : D ⟶ X) (i' : D' ⟶ Y) (a : D' ⟶ D) (h : a ≫ i = i' ≫ b)
    (H : IsPullback b p' p q) (H' : IsPullback a i' i b)
    [IsClosedImmersion i] [Flat (i ≫ p)] :
    IsIso (idealPullbackMap i i' b a h) := by
  have : IsClosedImmersion i' := MorphismProperty.of_isPullback H' inferInstance
  apply idealPullbackMap_isIso_of_local i i' b a h
  intro y
  obtain ⟨U, hU, hyU, _⟩ := exists_isAffineOpen_mem_and_subset
    (show p (b y) ∈ (⊤ : S.Opens) from trivial)
  obtain ⟨V, hV, hyV, hVU⟩ := exists_isAffineOpen_mem_and_subset
    (show b y ∈ p ⁻¹ᵁ U from hyU)
  have hyq : p' y ∈ q ⁻¹ᵁ U := by
    have he := congrArg (fun f : Y ⟶ S ↦ f y) H.w
    change p (b y) = q (p' y) at he
    change q (p' y) ∈ U
    rw [← he]
    exact hyU
  obtain ⟨W, hW, hyW, hWU⟩ := exists_isAffineOpen_mem_and_subset hyq
  let Z : Y.Opens := b ⁻¹ᵁ V ⊓ p' ⁻¹ᵁ W
  have hZV : Z ≤ b ⁻¹ᵁ V := inf_le_left
  have hZW : Z ≤ p' ⁻¹ᵁ W := inf_le_right
  have hPB := Scheme.Hom.isPullback_resLE H hWU hVU (show Z = _ from rfl)
  have : IsAffine U.toScheme := hU
  have : IsAffine V.toScheme := hV
  have : IsAffine W.toScheme := hW
  have : IsAffine Z.toScheme := IsAffine.of_isPullback hPB
  have : IsAffine (i ⁻¹ᵁ V).toScheme := hV.preimage i
  have : IsAffine (i' ⁻¹ᵁ Z).toScheme := (show IsAffineOpen Z from ‹IsAffine Z.toScheme›).preimage
    i'
  refine ⟨V, Z, hZV, ⟨hyV, hyW⟩, ?_⟩
  have : Flat ((i ∣_ V) ≫ p.resLE U V hVU) := restrictedIdealProjection_flat p i U V hVU
  exact flatQuotient_affine_idealPullbackMap_isIso (p.resLE U V hVU) (q.resLE U W hWU) (p'.resLE W Z
    hZW)
    (b.resLE V Z hZV) (i ∣_ V) (i' ∣_ Z)
    (restrictedSquareSourceMap i i' b a h V Z hZV)
    (restrictedSquareSourceMap_comm i i' b a h V Z hZV)
    hPB (restrictedSquareSourceMap_isPullback i i' b a h H' V Z hZV)

/-- The unchanged relative Cartier ideal base-change interface, with no extra premises. -/
theorem idealPullbackMap_isIso_of_relativeCartier : (∀ (S T X Y D D' : Scheme.{u}) (p : X ⟶ S) (q :
  T ⟶ S) (p' : Y ⟶ T)
    (b : Y ⟶ X) (i : D ⟶ X) (i' : D' ⟶ Y) (a : D' ⟶ D)
    (h : a ≫ i = i' ≫ b),
    IsPullback b p' p q → IsPullback a i' i b → IsClosedImmersion i →
      IsLocallyRankOne X (idealModule i) → Flat (i ≫ p) →
        IsIso (idealPullbackMap i i' b a h)) := by
  intro S T X Y D D' p q p' b i i' a h H H' hi _hI hflat
  let := hi
  let := hflat
  exact flatQuotient_idealPullbackMap_isIso p q p' b i i' a h H H'

end AlgebraicGeometry.Scheme.Hom
end
