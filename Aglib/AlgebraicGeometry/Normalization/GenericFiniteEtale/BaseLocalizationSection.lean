/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.BaseLocalization

/-! # The prescribed normalization section after base localization

The whole section on the original base constructs both localized sections.
Their original projection equations and selected closed-point comparison are
retained; no point or commuting square is supplied as a new hypothesis.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery

universe u

variable (A : Type u) [CommRing A] {X U : Scheme.{u}}
  (p : X ⟶ Spec (.of A)) (q : PrimeSpectrum A) (j : U ⟶ X)

local notation "L" => Localization.AtPrime q.asIdeal
local notation "l" => Spec.algebraMap A L
local notation "T" => pullback p l
local notation "b" => pullback.fst p l
local notation "V" => pullback j b
local notation "jR" => pullback.snd j b
local notation "g" => pullback.fst j b

/-- The original whole section determines the literal pullback section. -/
def baseLocalizationSection (s : Spec (.of A) ⟶ X) (hs : s ≫ p = 𝟙 _) :
    Spec (.of L) ⟶ T :=
  pullback.lift (l ≫ s) (𝟙 _) (by simp only [Category.assoc, hs, Category.comp_id,
    Category.id_comp])

@[reassoc (attr := simp)] theorem baseLocalizationSection_fst
    (s : Spec (.of A) ⟶ X) (hs : s ≫ p = 𝟙 _) :
    baseLocalizationSection A p q s hs ≫ b = l ≫ s := pullback.lift_fst ..

@[reassoc (attr := simp)] theorem baseLocalizationSection_snd
    (s : Spec (.of A) ⟶ X) (hs : s ≫ p = 𝟙 _) :
    baseLocalizationSection A p q s hs ≫ pullback.snd p l = 𝟙 _ := pullback.lift_snd ..

variable [IsDomain A] [IsIntegral X] [IsIntegral U] [IsDominant p] [IsOpenImmersion j]

local instance : IsIntegral T := baseLocalization_integral A p q
local instance : IsIntegral V := baseLocalization_openIntegral A p q j

variable [IsLocallyNoetherian X] [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)]
  (Y : FiniteEtale U) [IsIntegral Y.obj.left]

local notation "Q" => genericMap j Y.obj.hom
local notation "pR" => pullback.snd Y.obj.hom g

/-- Localize the prescribed original normalization section, including its
whole projection triangle and original selected point. -/
theorem exists_baseLocalizationNormalizationSection
    (s : Spec (.of A) ⟶ X) (hs : s ≫ p = 𝟙 _)
    (a : Spec (.of A) ⟶ (Q).normalization) (ha : a ≫ (Q).fromNormalization = s) :
    ∃ aR : Spec (.of L) ⟶ (genericMap jR pR).normalization,
      aR ≫ (genericMap jR pR).fromNormalization = baseLocalizationSection A p q s hs ∧
      aR ≫ (baseLocalizationIso A p q j Y).hom ≫ pullback.fst (Q).fromNormalization b =
        l ≫ a ∧
      ((baseLocalizationIso A p q j Y).hom ≫ pullback.fst (Q).fromNormalization b)
        (aR (IsLocalRing.closedPoint L)) = a q := by
  have he : (l ≫ a) ≫ (Q).fromNormalization = baseLocalizationSection A p q s hs ≫ b := by
    rw [Category.assoc, ha, baseLocalizationSection_fst]
  obtain ⟨aR, hR, hproj, hpoint⟩ := exists_baseLocalizationSection A p q j Y
    (l ≫ a) (baseLocalizationSection A p q s hs) he
  refine ⟨aR, hR, hproj, ?_⟩
  have hl : l (IsLocalRing.closedPoint L) = q := by
    apply PrimeSpectrum.ext
    exact Localization.AtPrime.under_maximalIdeal
  exact hpoint.trans (congrArg a hl)

end AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery
