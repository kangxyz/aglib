/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.MarkedPrincipalTargetReconstruction
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.GenericCoefficientZeroSpreading
public import Aglib.AlgebraicGeometry.Spec.Localization
public import Aglib.RingTheory.Localization.AwayChosenFraction

/-! # Original coefficient zero on a principal target refinement

The actual target denominator is inverted on the coefficient base through its
original map. The same whole generic cover is reconstructed using the actual
Cartesian square, without replacing it by a second generic cover. Fraction
continuity then spreads the original class zero on that same coefficient
cover. Generic zero is an internal stage input; the final effacement producer
must supply it, and no specified point is asserted to lie in the resulting open.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open IsLocalization.PrincipalDiagram
open AlgebraicGeometry.Scheme.PrincipalNeighborhoodLimit
open AlgebraicGeometry.Scheme.FiniteEtale
open AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery
open scoped nonZeroDivisors

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity

universe u eX
attribute [local instance] hasSheafifyLarge HasExt.standard

variable (A B F E : Type u) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
  [Field F] [Field E] [Algebra A B] [Algebra A F] [IsFractionRing A F]
  [Algebra A E] [Algebra B E] [IsScalarTower A B E] [IsFractionRing B E]
  (a : F →ₐ[A] E) (q : PrimeSpectrum A) (s : Finset q.asIdeal.primeCompl)

local notation "d" => denominator q.asIdeal.primeCompl s
local notation "As" => stage q.asIdeal.primeCompl s
local notation "dB" => algebraMap A B d
local notation "Bs" => Localization.Away dB

include a in
omit [IsDomain B] [IsFractionRing B E] in
/-- The actual target denominator stays nonzero in the coefficient domain. -/
theorem principalCoefficient_denominator_ne_zero : dB ≠ 0 := by
  have hd : d ≠ 0 := nonZeroDivisors.ne_zero
    (q.asIdeal.primeCompl_le_nonZeroDivisors
      (denominator_mem q.asIdeal.primeCompl s))
  intro hz
  have hE : algebraMap A E d = 0 := by
    rw [IsScalarTower.algebraMap_apply A B E, hz, map_zero]
  have ha : a (algebraMap A F d) = 0 := (a.commutes d).trans hE
  have hzF : algebraMap A F d = 0 := a.injective (ha.trans (map_zero a).symm)
  exact hd ((IsFractionRing.injective A F) (hzF.trans (map_zero (algebraMap A F)).symm))

/-- The original coefficient fraction arrow is specified directly by its
canonical ring map. Geometry does not infer an auxiliary algebra action. -/
def principalCoefficientFractionMap : Spec (.of E) ⟶ Spec (.of Bs) := by
  letI : NeZero dB := ⟨principalCoefficient_denominator_ne_zero A B F E a q s⟩
  exact Spec.map (CommRingCat.ofHom (Localization.AwayChosenFraction.map B E dB).toRingHom)

/-- The actual local coefficient map, not a map from the target localization
into the unlocalized coefficient base. -/
def principalCoefficientBaseMap : Spec (.of Bs) ⟶ Spec (.of As) :=
  Spec.map (CommRingCat.ofHom
    (IsLocalization.Away.map As Bs (algebraMap A B) d))

omit [IsDomain A] [IsDomain B] in
@[reassoc] theorem principalCoefficientBaseMap_original :
    principalCoefficientBaseMap A B q s ≫ Spec.algebraMap A As =
      Spec.algebraMap B Bs ≫ Spec.algebraMap A B :=
  (isPullback_specMap_localizationAway
    (CommRingCat.ofHom (algebraMap A B)) d).w

/-- The original fraction field has its original coefficient structural map. -/
@[reassoc] theorem principalCoefficientFraction_original :
    principalCoefficientFractionMap A B F E a q s ≫ Spec.algebraMap B Bs =
      Spec.algebraMap B E := by
  let : NeZero dB := ⟨principalCoefficient_denominator_ne_zero A B F E a q s⟩
  exact Spec.map_algHom_algebraMap (Localization.AwayChosenFraction.map B E dB)

/-- The actual coefficient-localization and source-fraction arrows commute.
Cancellation uses the original principal open immersion. -/
theorem principalCoefficient_generic_square :
    principalCoefficientFractionMap A B F E a q s ≫ principalCoefficientBaseMap A B q s =
      Spec.map (CommRingCat.ofHom a.toRingHom) ≫ principalFractionBaseMap A F q s := by
  apply (cancel_mono (Spec.algebraMap A As)).mp
  simp only [Category.assoc, principalCoefficientBaseMap_original,
    principalFractionBaseMap_original]
  rw [← Category.assoc, principalCoefficientFraction_original]
  rw [Spec.map_algHom_algebraMap]
  simp only [Spec.algebraMap, ← Spec.map_comp]
  exact congrArg Spec.map (CommRingCat.hom_ext
    (IsScalarTower.algebraMap_eq A B E).symm)

variable {X : Scheme.{u}} (p : X ⟶ Spec (.of A))
local notation "Xs" => Over.left (Functor.obj (schemeDiagram q.asIdeal.primeCompl p) (op s))
local notation "xs" => Over.hom (Functor.obj (schemeDiagram q.asIdeal.primeCompl p) (op s))
local notation "ps" => pullback.fst (Spec.algebraMap A As) p
local notation "β" => principalCoefficientBaseMap A B q s
local notation "Y" => pullback p (Spec.algebraMap A B)
local notation "Ys" => pullback ps β
local notation "bs" => pullback.snd ps β
local notation "hs" => pullback.fst ps β
local notation "D" => pullback bs (principalCoefficientFractionMap A B F E a q s)
local notation "δ" => pullback.fst bs (principalCoefficientFractionMap A B F E a q s)

/-- The unchanged coefficient-stage source maps to the original family. -/
def principalCoefficientFamilyMap : Ys ⟶ Y :=
  pullback.lift (hs ≫ xs) (bs ≫ Spec.algebraMap B Bs) (by
    calc
      (hs ≫ xs) ≫ p = hs ≫ (xs ≫ p) := Category.assoc ..
      _ = hs ≫ (ps ≫ Spec.algebraMap A As) :=
        congrArg (fun m => hs ≫ m) (pullback.condition (f := Spec.algebraMap A As)
          (g := p)).symm
      _ = (hs ≫ ps) ≫ Spec.algebraMap A As := (Category.assoc ..).symm
      _ = (bs ≫ β) ≫ Spec.algebraMap A As :=
        congrArg (fun m => m ≫ Spec.algebraMap A As) (pullback.condition (f := ps) (g := β))
      _ = bs ≫ (Spec.algebraMap B Bs ≫ Spec.algebraMap A B) := by
        rw [Category.assoc, principalCoefficientBaseMap_original]
      _ = (bs ≫ Spec.algebraMap B Bs) ≫ Spec.algebraMap A B :=
        (Category.assoc ..).symm)

/-- Lift directly to the original generic fibre through its actual square. -/
def principalCoefficientGenericMap : D ⟶ pullback p (Spec.algebraMap A F) :=
  (principalFractionTargetMap_isPullback A F q p s).lift
    (δ ≫ hs)
    (pullback.snd bs (principalCoefficientFractionMap A B F E a q s) ≫
      Spec.map (CommRingCat.ofHom a.toRingHom)) (by
      calc
        (δ ≫ hs) ≫ ps = δ ≫ (hs ≫ ps) := Category.assoc ..
        _ = δ ≫ (bs ≫ β) :=
          congrArg (fun m => δ ≫ m) (pullback.condition (f := ps) (g := β))
        _ = (δ ≫ bs) ≫ β := (Category.assoc ..).symm
        _ = (pullback.snd bs (principalCoefficientFractionMap A B F E a q s) ≫
            principalCoefficientFractionMap A B F E a q s) ≫ β :=
          congrArg (fun m => m ≫ β)
            (pullback.condition (f := bs) (g := principalCoefficientFractionMap A B F E a q s))
        _ = pullback.snd bs (principalCoefficientFractionMap A B F E a q s) ≫
            (Spec.map (CommRingCat.ofHom a.toRingHom) ≫ principalFractionBaseMap A F q s) := by
          rw [Category.assoc, principalCoefficient_generic_square A B F E a q s]
        _ = (pullback.snd bs (principalCoefficientFractionMap A B F E a q s) ≫
            Spec.map (CommRingCat.ofHom a.toRingHom)) ≫ principalFractionBaseMap A F q s :=
          (Category.assoc ..).symm)

@[reassoc] theorem principalCoefficientGenericMap_target :
    principalCoefficientGenericMap A B F E a q s p ≫ principalFractionTargetMap A F q p s =
      δ ≫ hs := (principalFractionTargetMap_isPullback A F q p s).lift_fst _ _ _

variable (Gs : FiniteEtale
    ((schemeDiagram q.asIdeal.primeCompl p).obj (op s)).left)
  (Z : FiniteEtale (pullback p (Spec.algebraMap A F)))
  (r : (baseChange (principalFractionTargetMap A F q p s)).obj Gs ≅ Z)

local notation "C" => Functor.obj (baseChange hs) Gs
local notation "ZE" =>
  Functor.obj (baseChange (principalCoefficientGenericMap A B F E a q s p)) Z

/-- The same cover is reconstructed over the coefficient generic fibre. -/
def principalCoefficientCoverReconstruction :
    (baseChange δ).obj C ≅ ZE :=
  (baseChangeComp hs δ).symm.app Gs ≪≫
    eqToIso (congrArg (fun m => (baseChange m).obj Gs)
      (principalCoefficientGenericMap_target A B F E a q s p).symm) ≪≫
    (baseChangeComp (principalFractionTargetMap A F q p s)
      (principalCoefficientGenericMap A B F E a q s p)).app Gs ≪≫
    (baseChange (principalCoefficientGenericMap A B F E a q s p)).mapIso r

include r in
/-- Generic zero on the original marked cover gives a nonempty principal
coefficient-open zero on the actual descended target cover. The original class
is not relabelled on a new coefficient scheme. -/
theorem exists_principalTarget_coefficient_open_zero
    [QuasiCompact p] [QuasiSeparated p]
    {T : Scheme.{u}} (h : Y ⟶ T)
    [HasExt.{eX} (AbelianSheaf.{u, u + 1} T)]
    (M : AbelianSheaf.{u, u + 1} T) (degree : ℕ) (c : Sheaf.H.{eX} M degree)
    (hc : cohomologyPullback.{u, eX, u + 2}
      ((ZE).obj.hom ≫ δ ≫ (principalCoefficientFamilyMap A B q s p ≫ h)) M degree c = 0) :
    ∃ t : Finset Bs⁰, denominator Bs⁰ t ≠ 0 ∧ Nonempty (stageBaseOpen Bs⁰ t) ∧
      cohomologyPullback.{u, eX, u + 2}
        ((stageSourceOpen Bs⁰ ((C).obj.hom ≫ bs) t).ι ≫
          (C).obj.hom ≫ (principalCoefficientFamilyMap A B q s p ≫ h)) M degree c = 0 := by
  let : NeZero dB := ⟨principalCoefficient_denominator_ne_zero A B F E a q s⟩
  let : Algebra Bs E := Localization.AwayChosenFraction.algebra B E dB
  let : IsScalarTower B Bs E := Localization.AwayChosenFraction.tower B E dB
  let : IsDomain Bs := Localization.AwayChosenFraction.domain B dB
  let : IsFractionRing Bs E := Localization.AwayChosenFraction.fractionRing B E dB
  let eR := principalCoefficientCoverReconstruction A B F E a q s p Gs Z r
  let : QuasiSeparatedSpace (Ys : Scheme.{u}) :=
    quasiSeparatedSpace_of_quasiSeparated bs
  let : QuasiSeparatedSpace (C).obj.left :=
    quasiSeparatedSpace_of_quasiSeparated ((C).obj.hom ≫ bs)
  let : CompactSpace (C).obj.left :=
    QuasiCompact.compactSpace_of_compactSpace ((C).obj.hom ≫ bs)
  have hz : eR.hom.hom.left ≫
      ((ZE).obj.hom ≫ δ ≫ (principalCoefficientFamilyMap A B q s p ≫ h)) =
      pullback.fst (C).obj.hom δ ≫
        ((C).obj.hom ≫ (principalCoefficientFamilyMap A B q s p ≫ h)) := by
    have ho := Over.w eR.hom.hom
    have hc := pullback.condition (f := (C).obj.hom) (g := δ)
    have hc' := congrArg
      (fun m => m ≫ (principalCoefficientFamilyMap A B q s p ≫ h)) hc.symm
    exact (Category.assoc ..).symm.trans
      ((congrArg (fun m => m ≫ (δ ≫ (principalCoefficientFamilyMap A B q s p ≫ h))) ho).trans
        ((Category.assoc ..).symm.trans (hc'.trans (Category.assoc ..))))
  exact exists_fraction_principalOpen_composite_zero_of_reconstruction.{u, eX, u + 2, u + 2}
    Bs E ((C).obj.hom ≫ bs) ((C).obj.hom ≫ (principalCoefficientFamilyMap A B q s p ≫ h))
    (pullback.fst (C).obj.hom δ)
    (pullback.snd (C).obj.hom δ ≫ pullback.snd bs (principalCoefficientFractionMap A B F E a q s))
    ((IsPullback.of_hasPullback (C).obj.hom δ).paste_vert
      (IsPullback.of_hasPullback bs (principalCoefficientFractionMap A B F E a q s)))
    eR.hom.hom.left ((ZE).obj.hom ≫ δ ≫ (principalCoefficientFamilyMap A B q s p ≫ h))
    hz M degree c hc

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
