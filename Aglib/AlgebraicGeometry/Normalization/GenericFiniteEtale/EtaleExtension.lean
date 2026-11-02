/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.GenericPullback
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.BaseChange

/-! # The original normalization as a finite etale extension

Once its original structural map is etale, the unchanged native normalization
is an object of the original finite-etale category. Its restriction is exactly
the original open cover, via the already constructed open-recovery isomorphism.
No new scheme or normalization is selected.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery

universe u

variable {X U : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
  [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)] [Nonempty U]
  (j : U ⟶ X) [IsOpenImmersion j] (Y : FiniteEtale U)
  [Etale (genericMap j Y.obj.hom).fromNormalization]

/-- The original normalization, merely equipped with its proved finite-etale property. -/
def normalizationFiniteEtale : FiniteEtale X :=
  ⟨Over.mk (genericMap j Y.obj.hom).fromNormalization,
    ⟨fromNormalization_isFinite j Y.obj.hom,
      inferInstanceAs (Etale (genericMap j Y.obj.hom).fromNormalization)⟩⟩

/-- Restriction of that same object recovers the unchanged original cover. -/
def normalizationFiniteEtaleRestrictionIso :
    Y ≅ (baseChange j).obj (normalizationFiniteEtale j Y) :=
  ObjectProperty.isoMk _ (Over.isoMk (iso j Y.obj.hom) (iso_hom_snd j Y.obj.hom))

@[simp]
theorem normalizationFiniteEtale_restrictionIso_hom_left :
    (normalizationFiniteEtaleRestrictionIso j Y).hom.hom.left =
      (iso j Y.obj.hom).hom := rfl

@[simp]
theorem normalizationFiniteEtale_restrictionIso_inv_left :
    (normalizationFiniteEtaleRestrictionIso j Y).inv.hom.left =
      (iso j Y.obj.hom).inv := rfl

@[reassoc]
theorem normalizationFiniteEtale_restrictionIso_hom_fst :
    (normalizationFiniteEtaleRestrictionIso j Y).hom.hom.left ≫
      pullback.fst (normalizationFiniteEtale j Y).obj.hom j = inclusion j Y.obj.hom := rfl

/-- An integral original cover gives the same integral normalization source. -/
theorem normalizationFiniteEtale_isIntegral [IsIntegral Y.obj.left] :
    IsIntegral (normalizationFiniteEtale j Y).obj.left := by
  let : IsIntegral U := isIntegral_of_isOpenImmersion j
  let : IsIntegral (genericCover j Y.obj.hom).obj.left :=
    IsIntegral.of_isIso (originalFieldSpectrumIso j Y).hom
  exact inferInstanceAs (IsIntegral (genericMap j Y.obj.hom).normalization)

end AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery
