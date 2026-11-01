/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.FlatPreimmersionBaseChange
public import Aglib.AlgebraicGeometry.Spec.LocalizationIntegralBaseChange

/-! # Original normalization after localization of the base

Only the literal pullback along `Spec A_q → Spec A` is used. The restricted
open and finite-etale cover are their native pullbacks. The flat-preimmersion
comparison retains their original maps, whole sections, and deck order.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery

universe u

variable (A : Type u) [CommRing A] [IsDomain A]
  {X U : Scheme.{u}} [IsIntegral X] [IsIntegral U]
  (p : X ⟶ Spec (.of A)) [IsDominant p] (q : PrimeSpectrum A)
  (j : U ⟶ X) [IsOpenImmersion j]

local notation "L" => Localization.AtPrime q.asIdeal
local notation "a" => Spec.algebraMap A L
local notation "T" => pullback p a
local notation "b" => pullback.fst p a
local notation "V" => pullback j b
local notation "jR" => pullback.snd j b
local notation "g" => pullback.fst j b
local notation "H" => IsPullback.of_hasPullback j b

local instance baseLocalization_flat : Flat a :=
  Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr
    (IsLocalization.flat L q.asIdeal.primeCompl))

local instance baseLocalization_preimmersion : IsPreimmersion a :=
  IsPreimmersion.of_isLocalization q.asIdeal.primeCompl

/-- The original generic point lifts to the actual base-localization pullback. -/
theorem baseLocalization_generic_mem_range : genericPoint X ∈ Set.range b := by
  obtain ⟨t, ht⟩ := genericPoint_mem_range_localization A L q.asIdeal.primeCompl
    q.asIdeal.primeCompl_le_nonZeroDivisors
  obtain ⟨z, hz, _⟩ := Scheme.Pullback.exists_preimage_pullback
    (genericPoint X) t ((map_genericPoint_of_isDominant X p).trans ht.symm)
  exact ⟨z, hz⟩

/-- The literal ambient base-localization pullback is integral. -/
theorem baseLocalization_integral : IsIntegral T :=
  isIntegral_pullback_localization A L q.asIdeal.primeCompl
    q.asIdeal.primeCompl_le_nonZeroDivisors p

attribute [local instance] baseLocalization_integral

/-- The literal base-localization of the original nonempty open is integral. -/
theorem baseLocalization_openIntegral : IsIntegral V := by
  let : IsDominant j := Scheme.isDominant_of_isOpenImmersion j
  exact isIntegral_pullback_of_flat_preimmersion j b
    (baseLocalization_generic_mem_range A p q)

attribute [local instance] baseLocalization_openIntegral

variable [IsLocallyNoetherian X] [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)]
  (Y : FiniteEtale U) [IsIntegral Y.obj.left]

local notation "Q" => genericMap j Y.obj.hom
local notation "pR" => pullback.snd Y.obj.hom g

local instance baseLocalization_normal :
    ∀ z : (T : Scheme.{u}), IsIntegrallyClosed ((T).presheaf.stalk z) :=
  fun z => (normalStalks_pullback_localization A L q.asIdeal.primeCompl p
    (fun _ => ⟨inferInstance, inferInstance⟩) z).2

/-- The comparison uses the same original normalization and literal pullbacks. -/
def baseLocalizationIso :
    (genericMap jR pR).normalization ≅ pullback (Q).fromNormalization b :=
  flatPreimmersionBaseChangeIso j b (baseLocalization_generic_mem_range A p q) jR g H Y

@[reassoc (attr := simp)] theorem baseLocalizationIso_hom_over :
    (baseLocalizationIso A p q j Y).hom ≫ pullback.snd (Q).fromNormalization b =
      (genericMap jR pR).fromNormalization :=
  flatPreimmersionBaseChangeIso_hom_over j b
    (baseLocalization_generic_mem_range A p q) jR g H Y

@[reassoc (attr := simp)] theorem baseLocalizationIso_hom_generic :
    (genericMap jR pR).toNormalization ≫ (baseLocalizationIso A p q j Y).hom =
      genericToCover jR pR ≫ flatPreimmersionBaseChangeInclusion j b jR g H Y :=
  flatPreimmersionBaseChangeIso_hom_generic j b
    (baseLocalization_generic_mem_range A p q) jR g H Y

@[reassoc (attr := simp)] theorem inclusion_baseLocalizationIso_hom :
    inclusion jR pR ≫ (baseLocalizationIso A p q j Y).hom =
      flatPreimmersionBaseChangeInclusion j b jR g H Y :=
  inclusion_flatPreimmersionBaseChangeIso_hom j b
    (baseLocalization_generic_mem_range A p q) jR g H Y

omit [IsLocallyNoetherian X] [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)] in
/-- The actual restricted Galois cover retains its original deck order. -/
theorem baseLocalization_galois_card [CategoryTheory.PreGaloisCategory.IsGalois Y] :
    CategoryTheory.PreGaloisCategory.IsGalois ((FiniteEtale.baseChange g).obj Y) ∧
      Nat.card (Aut ((FiniteEtale.baseChange g).obj Y)) = Nat.card (Aut Y) :=
  flatPreimmersionBaseChange_galois_card j b
    (baseLocalization_generic_mem_range A p q) jR g H Y

/-- The prescribed whole section is lifted, retaining its original closed point. -/
theorem exists_baseLocalizationSection {D : Type u} [CommRing D] [IsLocalRing D]
    (s : Spec (.of D) ⟶ (Q).normalization) (r : Spec (.of D) ⟶ T)
    (hs : s ≫ (Q).fromNormalization = r ≫ b) :
    ∃ sR : Spec (.of D) ⟶ (genericMap jR pR).normalization,
      sR ≫ (genericMap jR pR).fromNormalization = r ∧
      sR ≫ (baseLocalizationIso A p q j Y).hom ≫
        pullback.fst (Q).fromNormalization b = s ∧
      ((baseLocalizationIso A p q j Y).hom ≫ pullback.fst (Q).fromNormalization b)
        (sR (IsLocalRing.closedPoint D)) = s (IsLocalRing.closedPoint D) :=
  exists_flatPreimmersionBaseChangeSection j b
    (baseLocalization_generic_mem_range A p q) jR g H Y s r hs

end AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery
