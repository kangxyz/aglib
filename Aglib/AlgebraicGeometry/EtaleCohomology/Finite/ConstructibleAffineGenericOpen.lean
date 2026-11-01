/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.ConstructibleGenericOpen
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Noetherian

/-! # A genuine constructible generic open for an original finite morphism

The original global-section rings and affine spectrum isomorphisms supply the
finite algebra. Its two genuine principal restrictions give a nonempty open
of the original base. Pasting the two native tensor spectrum squares with the
original affine isomorphism square gives the actual Cartesian square used by
the original finite base-change mate. The conclusion concerns the inverse
image of the original direct image, not a separately selected coefficient.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Finite

universe u

attribute [local instance] hasSheafifyLarge

/-- On a genuine nonempty open of an integral affine Noetherian base, the
original direct image of an original constructible abelian sheaf is
constructible. Local constancy and global stratification are not asserted. -/
theorem exists_nonempty_constructible_open_of_finite
    {Y X : Scheme.{u}} [IsAffine X] [IsIntegral X] [IsNoetherian X]
    (f : Y ⟶ X) [IsFinite f]
    {F : AbelianSheaf.{u, u + 1} Y} (hF : Constructible.IsConstructible F) :
    ∃ (S : Scheme.{u}) (j : S ⟶ X), IsOpenImmersion j ∧ Nonempty S ∧
      Constructible.IsConstructible ((inverseImage j).obj ((directImage f).obj F)) := by
  have : IsAffine Y := isAffine_of_isAffineHom f
  let R := Γ(X, ⊤)
  let A := Γ(Y, ⊤)
  let : Algebra R A := f.appTop.hom.toAlgebra
  have : Module.Finite R A := f.finite_appTop
  have : IsNoetherianRing R :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top X⟩
  obtain ⟨a, ha, b, hb, hImage⟩ := exists_noetherianGeneric_constructibleFiniteImage R A
  let R₁ := Localization.Away a
  let A₁ := R₁ ⊗[R] A
  let R₂ := Localization.Away b
  let A₂ := R₂ ⊗[R₁] A₁
  have : IsDomain R₁ := Localization.Away.isDomain ha
  have : IsDomain R₂ := Localization.Away.isDomain hb
  let f₀ := Spec.algebraMap R A
  let f₁ := Spec.algebraMap R₁ A₁
  let f₂ := Spec.algebraMap R₂ A₂
  let p₁ := Spec.algebraMap R R₁
  let p₂ := Spec.algebraMap R₁ R₂
  let t₁ : Spec (.of A₁) ⟶ Spec (.of A) :=
    Spec.map (CommRingCat.ofHom (R := A) (S := A₁)
    (Algebra.TensorProduct.includeRight : A →ₐ[R] R₁ ⊗[R] A).toRingHom)
  let t₂ : Spec (.of A₂) ⟶ Spec (.of A₁) :=
    Spec.map (CommRingCat.ofHom (R := A₁) (S := A₂)
    (Algebra.TensorProduct.includeRight : A₁ →ₐ[R₁] R₂ ⊗[R₁] A₁).toRingHom)
  have H₀ : IsPullback Y.isoSpec.inv f₀ f X.isoSpec.inv :=
    IsPullback.of_horiz_isIso ⟨(Scheme.isoSpec_inv_naturality f).symm⟩
  have H₁ : IsPullback t₁ f₁ f₀ p₁ :=
    (isPullback_SpecMap_of_isPushout _ _ _ _
      (CommRingCat.isPushout_tensorProduct R R₁ A)).flip
  have H₂ : IsPullback t₂ f₂ f₁ p₂ :=
    (isPullback_SpecMap_of_isPushout _ _ _ _
      (CommRingCat.isPushout_tensorProduct R₁ R₂ A₁)).flip
  let j := p₂ ≫ p₁ ≫ X.isoSpec.inv
  let k := t₂ ≫ t₁ ≫ Y.isoSpec.inv
  have H : IsPullback k f₂ f j := H₂.paste_horiz (H₁.paste_horiz H₀)
  have hFk : Constructible.IsConstructible ((inverseImage k).obj F) :=
    Constructible.isConstructible_pullback_of_isAffine k hF
  have hImage' : Constructible.IsConstructible
      ((directImage f₂).obj ((inverseImage k).obj F)) := hImage _ hFk
  have : IsIso ((baseChangeMap f f₂ j k H.w.symm).app F) :=
    finiteBaseChange_app_isIso f f₂ j k H F
  refine ⟨Spec (.of R₂), j, inferInstance, inferInstance, ?_⟩
  exact (Constructible.isConstructible_iff_of_iso
    (asIso ((baseChangeMap f f₂ j k H.w.symm).app F))).mpr hImage'

end AlgebraicGeometry.Scheme.EtaleCohomology.Finite
