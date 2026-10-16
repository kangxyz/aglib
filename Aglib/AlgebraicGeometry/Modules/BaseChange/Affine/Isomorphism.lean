/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.BaseChange.Affine.Locality

/-!
# Arbitrary base change of affine module direct image

The native canonical moduleBaseChangeMap is invertible for affine f and
quasicoherent coefficients after arbitrary base change. The auxiliary affine
square hypothesis is internal and proved by the preceding leaf; it is not
added as a new public theorem-family input.

Source: `R5Lab/AlgebraicGeometry/Curves/Degree/AffineModuleBaseChange.lean`, frozen R5 integration
`79307ff88f07d34fd5c3edb859f799c55e38f290`, SHA-256
`0739a4c1e7297a8f1dec99f8f53914339710e9240fa56c70a90ae2127581ed06`. Selected original ranges:
[[1510, 1613]].
-/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

open CategoryTheory Limits AlgebraicGeometry Opposite Module TopologicalSpace


namespace AlgebraicGeometry.Scheme.Modules.BaseChange.Affine.Square
universe u


variable {P X Y T : Scheme.{u}}

theorem moduleSquareBaseChangeMap_isIso_congr {a a' : P ⟶ X} (b : P ⟶ T)
    (f : X ⟶ Y) {g g' : T ⟶ Y} (ha : a = a') (hg : g = g')
    (h : a ≫ f = b ≫ g) (h' : a' ≫ f = b ≫ g') (M : X.Modules) :
    IsIso (moduleSquareBaseChangeMap a b f g h M) ↔
      IsIso (moduleSquareBaseChangeMap a' b f g' h' M) := by
  subst a'
  subst g'
  rfl

private theorem squareBaseChange_on_affine_test_open (hAff : (∀ (P X Y T : Scheme.{u}) [IsAffine
  P] [IsAffine X] [IsAffine Y] [IsAffine T]
      (a : P ⟶ X) (b : P ⟶ T) (f : X ⟶ Y) (g : T ⟶ Y)
      (H : IsPullback a b f g) (M : X.Modules), M.IsQuasicoherent →
        IsIso (moduleSquareBaseChangeMap a b f g H.w M)))
    (a : P ⟶ X) (b : P ⟶ T) (f : X ⟶ Y) (g : T ⟶ Y) (H : IsPullback a b f g)
    [IsAffineHom f] (M : X.Modules) [M.IsQuasicoherent]
    (V : Y.Opens) (hV : IsAffineOpen V) (W : T.Opens) (hW : IsAffineOpen W)
    (hWV : W ≤ g ⁻¹ᵁ V) :
    IsIso ((Scheme.Modules.restrictFunctor W.ι).map (moduleSquareBaseChangeMap a b f g H.w M)) := by
  let P₀ := (b ⁻¹ᵁ W).toScheme
  let a₀ : P₀ ⟶ X := (b ⁻¹ᵁ W).ι ≫ a
  let b₀ : P₀ ⟶ W.toScheme := b ∣_ W
  let g₀ : W.toScheme ⟶ Y := W.ι ≫ g
  have H₀ : IsPullback a₀ b₀ f g₀ := (isPullback_morphismRestrict b W).flip.paste_horiz H
  let e : W.toScheme ⟶ V.toScheme := g.resLE V W hWV
  have he : e ≫ V.ι = g₀ := Scheme.Hom.resLE_comp_ι g hWV
  have ha_range : Set.range a₀ ⊆ Set.range (f ⁻¹ᵁ V).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨p, rfl⟩
    change f (a₀ p) ∈ V
    have hp := congrArg (fun k : P₀ ⟶ Y => k p) H₀.w
    change f (a₀ p) = g ((b₀ p).1) at hp
    rw [hp]
    exact hWV (b₀ p).2
  let a' : P₀ ⟶ (f ⁻¹ᵁ V).toScheme := IsOpenImmersion.lift (f ⁻¹ᵁ V).ι a₀ ha_range
  have ha : a' ≫ (f ⁻¹ᵁ V).ι = a₀ := IsOpenImmersion.lift_fac _ _ _
  have h' : a' ≫ (f ∣_ V) = b₀ ≫ e := by
    apply (cancel_mono V.ι).mp
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, ha]
    calc a₀ ≫ f = b₀ ≫ g₀ := H₀.w
      _ = (b₀ ≫ e) ≫ V.ι := by rw [Category.assoc, he]
  have H' : IsPullback a' b₀ (f ∣_ V) e := by
    apply IsPullback.of_right (t := (isPullback_morphismRestrict f V).flip) (p := h')
    simpa only [ha, he] using H₀
  letI : IsAffine V.toScheme := hV
  letI : IsAffine W.toScheme := hW
  letI : IsAffine (f ⁻¹ᵁ V).toScheme := hV.preimage f
  letI : IsAffine P₀ := IsAffine.of_isIso H'.isoPullback.hom
  let N := (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj M
  haveI : N.IsQuasicoherent := by dsimp [N]; infer_instance
  haveI : IsIso (moduleSquareBaseChangeMap a' b₀ (f ∣_ V) e h' N) :=
    hAff P₀ (f ⁻¹ᵁ V).toScheme V.toScheme W.toScheme a' b₀ (f ∣_ V) e H' N inferInstance
  have hlocal := moduleSquareBaseChangeMap_baseOpen_isIso f V a' b₀ e h' M
  have hnative : IsIso (moduleSquareBaseChangeMap a₀ b₀ f g₀ H₀.w M) := by
    exact (moduleSquareBaseChangeMap_isIso_congr b₀ f ha he
      (baseOpenCondition f V a' b₀ e h') H₀.w M).mp hlocal
  exact moduleSquareBaseChangeMap_testOpen_isIso a b f g H.w W M hnative

private theorem moduleSquareBaseChangeMap_isIso_of_affine_square
    (hAff : (∀ (P X Y T : Scheme.{u}) [IsAffine P] [IsAffine X] [IsAffine Y] [IsAffine T]
      (a : P ⟶ X) (b : P ⟶ T) (f : X ⟶ Y) (g : T ⟶ Y)
      (H : IsPullback a b f g) (M : X.Modules), M.IsQuasicoherent →
        IsIso (moduleSquareBaseChangeMap a b f g H.w M)))
    (a : P ⟶ X) (b : P ⟶ T) (f : X ⟶ Y) (g : T ⟶ Y) (H : IsPullback a b f g)
    [IsAffineHom f] (M : X.Modules) [M.IsQuasicoherent] :
    IsIso (moduleSquareBaseChangeMap a b f g H.w M) := by
  apply Scheme.Modules.Pullback.OpenRestriction.isIso_of_local_restrict
  intro t
  obtain ⟨_, ⟨V : Y.Opens, hV, rfl⟩, htV, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (g t)) isOpen_univ
  obtain ⟨_, ⟨W : T.Opens, hW, rfl⟩, htW, hWV : W ≤ g ⁻¹ᵁ V⟩ :=
    T.isBasis_affineOpens.exists_subset_of_mem_open htV (g ⁻¹ᵁ V).isOpen
  exact ⟨W, htW, squareBaseChange_on_affine_test_open hAff a b f g H M V hV W hW hWV⟩

private theorem affineModuleBaseChange_of_affine_square
    (hAff : (∀ (P X Y T : Scheme.{u}) [IsAffine P] [IsAffine X] [IsAffine Y] [IsAffine T]
      (a : P ⟶ X) (b : P ⟶ T) (f : X ⟶ Y) (g : T ⟶ Y)
      (H : IsPullback a b f g) (M : X.Modules), M.IsQuasicoherent →
        IsIso (moduleSquareBaseChangeMap a b f g H.w M))) : AffineModuleBaseChange.{u} := by
  intro X Y T f g M hf hM
  letI := hf
  letI := hM
  exact moduleSquareBaseChangeMap_isIso_of_affine_square hAff (pullback.fst f g)
    (pullback.snd f g) f g (IsPullback.of_hasPullback f g) M

end AlgebraicGeometry.Scheme.Modules.BaseChange.Affine.Square



namespace AlgebraicGeometry.Scheme.Modules.BaseChange.Affine
universe u

/-- Arbitrary base change of a quasi-coherent module along an affine morphism,
for the unchanged native scheme-module adjunction mate. -/
theorem affineModuleBaseChange : AffineModuleBaseChange.{u} := by
  apply Square.affineModuleBaseChange_of_affine_square
  intro P X Y T _ _ _ _ a b f g H M hM
  letI := hM
  exact Square.moduleSquareBaseChangeMap_isIso_affine a b f g H M

end AlgebraicGeometry.Scheme.Modules.BaseChange.Affine
