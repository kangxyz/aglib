/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.TwoFieldEffacement.GenericH1ClassEffacement
public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.TwoFieldEffacement.OriginalClassZeroTransport
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.PrincipalTargetCoefficientZeroSpreading
public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.SeparableBaseSquare

/-! # Complete transport of the original marked cover to finite normal models

The generic producer retains its actual source cover, full point and original
class. The two canonical generic-fibre presentations are compared through their
original pullback maps, before the same cover is extended and its original class
zero is spread on the coefficient model. No arbitrary coefficient-field
separability is asserted.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory Opposite
open AlgebraicGeometry.Scheme.FiniteEtale
open AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery
open AlgebraicGeometry.Scheme.PrincipalNeighborhoodLimit
open IsLocalization.PrincipalDiagram
open scoped nonZeroDivisors

namespace AlgebraicGeometry.Scheme.EtaleCohomology.TwoFieldEffacement

universe u eX
attribute [local instance] hasSheafifyLarge HasExt.standard

section OriginalFibreTransport

variable {X S K R F : Scheme.{u}} (p : X ⟶ S) (k : K ⟶ S) (r : R ⟶ S)
  (a : F ⟶ K) (b : F ⟶ R) (hab : b ≫ r = a ≫ k)

/-- The original two iterated fibres are compared using only pullback pasting. -/
def normalGenericFibreIso :
    pullback (pullback.snd p r) b ≅ pullback (pullback.snd p k) a :=
  pullbackLeftPullbackSndIso p r b ≪≫ pullback.congrHom rfl hab ≪≫
    (pullbackLeftPullbackSndIso p k a).symm

@[reassoc] theorem normalGenericFibreIso_source :
    (normalGenericFibreIso p k r a b hab).hom ≫
        pullback.fst (pullback.snd p k) a ≫ pullback.fst p k =
      pullback.fst (pullback.snd p r) b ≫ pullback.fst p r := by
  simp only [normalGenericFibreIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    pullbackLeftPullbackSndIso_inv_fst, pullback.congrHom_hom, pullback.map,
    pullback.lift_fst, Category.comp_id, pullbackLeftPullbackSndIso_hom_fst]

@[reassoc] theorem normalGenericFibreIso_field :
    (normalGenericFibreIso p k r a b hab).hom ≫ pullback.snd (pullback.snd p k) a =
      pullback.snd (pullback.snd p r) b := by
  simp only [normalGenericFibreIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    pullbackLeftPullbackSndIso_inv_snd_snd, pullback.congrHom_hom, pullback.map,
    pullback.lift_snd, Category.comp_id, pullbackLeftPullbackSndIso_hom_snd]

/-- The transported generic point is determined by its original scheme and
field projections; no new geometric point is selected. -/
theorem normalGenericFibreIso_point
    (xK : F ⟶ pullback (pullback.snd p k) a)
    (xR : F ⟶ pullback (pullback.snd p r) b)
    (hX : xR ≫ pullback.fst (pullback.snd p r) b ≫ pullback.fst p r =
      xK ≫ pullback.fst (pullback.snd p k) a ≫ pullback.fst p k)
    (hF : xR ≫ pullback.snd (pullback.snd p r) b =
      xK ≫ pullback.snd (pullback.snd p k) a) :
    xR ≫ (normalGenericFibreIso p k r a b hab).hom = xK := by
  have H := (IsPullback.of_hasPullback (pullback.snd p k) a).paste_horiz
    (IsPullback.of_hasPullback p k)
  apply H.hom_ext
  · exact (Category.assoc ..).trans
      ((congrArg (fun m => xR ≫ m) (normalGenericFibreIso_source p k r a b hab)).trans hX)
  · exact (Category.assoc ..).trans
      ((congrArg (fun m => xR ≫ m) (normalGenericFibreIso_field p k r a b hab)).trans hF)

end OriginalFibreTransport

section WholeCoverTransport

variable {U V T : Scheme.{u}} {Q : Type u} [Field Q]
  (i : V ≅ U) (Z : FiniteEtale U)
  (x : Spec (.of Q) ⟶ U) (y : Spec (.of Q) ⟶ V) (hy : y ≫ i.hom = x) (z : Fiber x Z)

/-- The same full point on the pulled-back cover, with its original cover leg. -/
def normalGenericCoverPoint :
    Fiber y ((baseChange i.hom).obj Z) :=
  Over.homMk (pullback.lift z.left y ((Over.w z).trans hy.symm)) (pullback.lift_snd ..)

@[reassoc] theorem normalGenericCoverPoint_original :
    (normalGenericCoverPoint i Z x y hy z).left ≫ pullback.fst Z.obj.hom i.hom = z.left :=
  pullback.lift_fst ..

/-- A reconstruction morphism transports zero of the original class by the
original inverse-image composition law, without a new class representative. -/
theorem original_class_zero_of_composite
    [HasExt.{eX} (AbelianSheaf.{u, u + 1} T)]
    {W W' : Scheme.{u}} (v : W' ⟶ W) (h : W ⟶ T)
    (M : AbelianSheaf.{u, u + 1} T) (q : ℕ) (c : Sheaf.H.{eX} M q)
    (hc : cohomologyPullback.{u, eX, u + 2} h M q c = 0) :
    cohomologyPullback.{u, eX, u + 2} (v ≫ h) M q c = 0 := by
  apply (cohomologyMapIso_bijective ((inverseImageComp h v).app M) q).injective
  have hcomp := cohomologyPullback_comp.{u, eX, u + 2, u + 2} h v M q c
  rw [hc, map_zero] at hcomp
  exact hcomp.trans (map_zero _).symm

end WholeCoverTransport

section ActualCoefficientFamily

open Continuity

variable (A B F E : Type u) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
  [Field F] [Field E] [Algebra A B] [Algebra A F] [IsFractionRing A F]
  [Algebra A E] [Algebra B E] [IsScalarTower A B E] [IsFractionRing B E]
  (a : F →ₐ[A] E) {X : Scheme.{u}} (p : X ⟶ Spec (.of A))

local notation "pF" => pullback.snd p (Spec.algebraMap A F)
local notation "aE" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom a))
local notation "W" => pullback pF aE
local notation "Y" => pullback p (Spec.algebraMap A B)

/-- The generic coefficient family maps to the unchanged coefficient family
through its two original projections. -/
def genericCoefficientFamilyMap : W ⟶ Y :=
  pullback.lift (pullback.fst pF aE ≫ pullback.fst p (Spec.algebraMap A F))
    (pullback.snd pF aE ≫ Spec.algebraMap B E) (by
      have ha : aE ≫ Spec.algebraMap A F =
          Spec.algebraMap B E ≫ Spec.algebraMap A B := by
        rw [Spec.map_algHom_algebraMap]
        simp only [Spec.algebraMap, ← Spec.map_comp]
        exact congrArg Spec.map (CommRingCat.hom_ext
          (IsScalarTower.algebraMap_eq A B E))
      calc
        _ = pullback.fst pF aE ≫ (pF ≫ Spec.algebraMap A F) := by
          rw [Category.assoc, pullback.condition]
        _ = (pullback.snd pF aE ≫ aE) ≫ Spec.algebraMap A F := by
          rw [← Category.assoc, pullback.condition]
        _ = (pullback.snd pF aE ≫ Spec.algebraMap B E) ≫ Spec.algebraMap A B := by
          rw [Category.assoc, ha, Category.assoc])

variable (q : PrimeSpectrum A) (s : Finset q.asIdeal.primeCompl)
local notation "As" => stage q.asIdeal.primeCompl s
local notation "Bs" => Localization.Away (algebraMap A B (denominator q.asIdeal.primeCompl s))
local notation "ps" => pullback.fst (Spec.algebraMap A As) p
local notation "β" => principalCoefficientBaseMap A B q s
local notation "bs" => pullback.snd ps β
local notation "δ" => pullback.fst bs (principalCoefficientFractionMap A B F E a q s)
local notation "bD" => pullback.snd bs (principalCoefficientFractionMap A B F E a q s)
local notation "gD" => principalCoefficientGenericMap A B F E a q s p

/-- The generic lift also retains its actual field projection. -/
theorem principalGenericMap_field : gD ≫ pF = bD ≫ aE :=
  (principalFractionTargetMap_isPullback A F q p s).lift_snd _ _ _

/-- Compare the actual principal generic source to the original coefficient
generic source, without choosing a second cover or fraction field. -/
def principalGenericToOriginal :
    pullback bs (principalCoefficientFractionMap A B F E a q s) ⟶ W :=
  pullback.lift gD bD (principalGenericMap_field A B F E a p q s)

@[reassoc] theorem principalGenericToOriginal_fst :
    principalGenericToOriginal A B F E a p q s ≫ pullback.fst pF aE = gD :=
  pullback.lift_fst ..

@[reassoc] theorem principalGenericToOriginal_snd :
    principalGenericToOriginal A B F E a p q s ≫ pullback.snd pF aE = bD :=
  pullback.lift_snd ..

theorem principalGenericToOriginal_family :
    principalGenericToOriginal A B F E a p q s ≫ genericCoefficientFamilyMap A B F E a p =
      δ ≫ principalCoefficientFamilyMap A B q s p := by
  have hGfst : genericCoefficientFamilyMap A B F E a p ≫
      pullback.fst p (Spec.algebraMap A B) =
      pullback.fst pF aE ≫ pullback.fst p (Spec.algebraMap A F) := pullback.lift_fst ..
  have hPfst : principalCoefficientFamilyMap A B q s p ≫
      pullback.fst p (Spec.algebraMap A B) =
      pullback.fst ps β ≫ ((schemeDiagram q.asIdeal.primeCompl p).obj (op s)).hom :=
    pullback.lift_fst ..
  have hPsnd : principalCoefficientFamilyMap A B q s p ≫
      pullback.snd p (Spec.algebraMap A B) = bs ≫ Spec.algebraMap B Bs :=
    pullback.lift_snd ..
  apply pullback.hom_ext
  · have hg := congrArg
      (fun m => m ≫ ((schemeDiagram q.asIdeal.primeCompl p).obj (op s)).hom)
      (principalCoefficientGenericMap_target A B F E a q s p)
    have h := (Category.assoc ..).trans
      (congrArg (fun m => gD ≫ m) (principalFractionTargetMap_original A F q p s))
    have hgX := h.symm.trans hg
    have hl := (Category.assoc ..).trans
      ((congrArg (fun m => principalGenericToOriginal A B F E a p q s ≫ m) hGfst).trans
        ((Category.assoc ..).symm.trans
          (congrArg (fun m => m ≫ pullback.fst p (Spec.algebraMap A F))
            (principalGenericToOriginal_fst A B F E a p q s))))
    have hr := (Category.assoc ..).trans (congrArg (fun m => δ ≫ m) hPfst)
    exact hl.trans (hgX.trans ((Category.assoc ..).trans hr.symm))
  · have hGsnd' : genericCoefficientFamilyMap A B F E a p ≫
        pullback.snd p (Spec.algebraMap A B) = pullback.snd pF aE ≫ Spec.algebraMap B E :=
      pullback.lift_snd ..
    have hf := congrArg (fun m => m ≫ Spec.algebraMap B Bs)
      (pullback.condition (f := bs) («g» := principalCoefficientFractionMap A B F E a q s))
    have hf' := hf.trans ((Category.assoc ..).trans
      (congrArg (fun m => bD ≫ m) (principalCoefficientFraction_original A B F E a q s)))
    have hl := (Category.assoc ..).trans
      ((congrArg (fun m => principalGenericToOriginal A B F E a p q s ≫ m) hGsnd').trans
        ((Category.assoc ..).symm.trans
          (congrArg (fun m => m ≫ Spec.algebraMap B E)
            (principalGenericToOriginal_snd A B F E a p q s))))
    have hr := (Category.assoc ..).trans (congrArg (fun m => δ ≫ m) hPsnd)
    exact hl.trans (hf'.symm.trans ((Category.assoc ..).trans hr.symm))

variable (Z : FiniteEtale (pullback p (Spec.algebraMap A F)))

/-- Pull the unchanged generic cover along the actual source comparison. -/
def principalGenericCoverToOriginal :
    ((baseChange gD).obj Z).obj.left ⟶ ((baseChange (pullback.fst pF aE)).obj Z).obj.left :=
  pullback.lift (pullback.fst Z.obj.hom gD)
    (((baseChange gD).obj Z).obj.hom ≫ principalGenericToOriginal A B F E a p q s) (by
      have hv := principalGenericToOriginal_fst A B F E a p q s
      exact (pullback.condition (f := Z.obj.hom) («g» := gD)).trans
        ((congrArg (fun m => ((baseChange gD).obj Z).obj.hom ≫ m) hv).symm.trans
          (Category.assoc ..).symm))


theorem principalGenericCoverToOriginal_family {T : Scheme.{u}} (h : Y ⟶ T) :
    principalGenericCoverToOriginal A B F E a p q s Z ≫
        ((baseChange (pullback.fst pF aE)).obj Z).obj.hom ≫
          genericCoefficientFamilyMap A B F E a p ≫ h =
      ((baseChange gD).obj Z).obj.hom ≫ δ ≫ principalCoefficientFamilyMap A B q s p ≫ h := by
  have hl : principalGenericCoverToOriginal A B F E a p q s Z ≫
      ((baseChange (pullback.fst pF aE)).obj Z).obj.hom =
      ((baseChange gD).obj Z).obj.hom ≫ principalGenericToOriginal A B F E a p q s :=
    pullback.lift_snd ..
  have ht := principalGenericToOriginal_family A B F E a p q s
  exact (Category.assoc ..).symm.trans
    ((congrArg (fun m => m ≫ (genericCoefficientFamilyMap A B F E a p ≫ h)) hl).trans
      (by simpa only [Category.assoc] using
        congrArg (fun m => ((baseChange gD).obj Z).obj.hom ≫ m ≫ h) ht))

end ActualCoefficientFamily

section MarkedNormalOpenStage

open Continuity

variable (A B F E : Type u) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
  [Field F] [Field E] [Algebra A B] [Algebra A F] [IsFractionRing A F]
  [Algebra A E] [Algebra B E] [IsScalarTower A B E] [IsFractionRing B E]
  (a : F →ₐ[A] E) {X T : Scheme.{u}} (p : X ⟶ Spec (.of A))
  (σ : Spec (.of A) ⟶ X) (hσ : σ ≫ p = 𝟙 _)
  (Z : FiniteEtale (pullback p (Spec.algebraMap A F)))
  (z : Fiber (fractionSectionPoint A F p σ hσ) Z)
  (h : pullback p (Spec.algebraMap A B) ⟶ T)
  [HasExt.{eX} (AbelianSheaf.{u, u + 1} T)]
  (M : AbelianSheaf.{u, u + 1} T) (degree : ℕ) (c : Sheaf.H.{eX} M degree)

/-- The same whole marked cover over a principal target refinement, with the
original class zero on an actual nonempty coefficient principal open. -/
def MarkedNormalOpenClassZero (q : PrimeSpectrum A) : Prop :=
  ∃ (s : Finset q.asIdeal.primeCompl)
    (Gs : FiniteEtale ((schemeDiagram q.asIdeal.primeCompl p).obj (op s)).left)
    (r : (baseChange (principalFractionTargetMap A F q p s)).obj Gs ≅ Z),
    Etale (Gs.obj.hom ≫ ((schemeDiagram q.asIdeal.primeCompl p).obj (op s)).hom) ∧
    Surjective Gs.obj.hom ∧
    ∃ (w : Spec (.of F) ⟶
      ((baseChange (principalFractionTargetMap A F q p s)).obj Gs).obj.left),
      w ≫ r.hom.hom.left = z.left ∧
      w ≫ ((baseChange (principalFractionTargetMap A F q p s)).obj Gs).obj.hom =
        fractionSectionPoint A F p σ hσ ∧
      let Bs := Localization.Away (algebraMap A B (denominator q.asIdeal.primeCompl s))
      let ps := pullback.fst (Spec.algebraMap A (stage q.asIdeal.primeCompl s)) p
      let β := principalCoefficientBaseMap A B q s
      let bs := pullback.snd ps β
      let C := (baseChange (pullback.fst ps β)).obj Gs
      ∃ t : Finset Bs⁰, denominator Bs⁰ t ≠ 0 ∧ Nonempty (stageBaseOpen Bs⁰ t) ∧
        cohomologyPullback.{u, eX, u + 2}
          ((stageSourceOpen Bs⁰ (C.obj.hom ≫ bs) t).ι ≫ C.obj.hom ≫
            principalCoefficientFamilyMap A B q s p ≫ h) M degree c = 0

/-- The same original open-zero output also retains the actual source-local
section supplied by marked cover extension, before any rank-zero argument. -/
def MarkedNormalOpenClassZeroWithLocalMark (q : PrimeSpectrum A) : Prop :=
  ∃ (s : Finset q.asIdeal.primeCompl)
    (Gs : FiniteEtale ((schemeDiagram q.asIdeal.primeCompl p).obj (op s)).left)
    (r : (baseChange (principalFractionTargetMap A F q p s)).obj Gs ≅ Z),
    Etale (Gs.obj.hom ≫ ((schemeDiagram q.asIdeal.primeCompl p).obj (op s)).hom) ∧
    Surjective Gs.obj.hom ∧
    ∃ (ρ : Spec (.of (Localization.AtPrime q.asIdeal)) ⟶ Gs.obj.left),
      ρ ≫ Gs.obj.hom ≫ ((schemeDiagram q.asIdeal.primeCompl p).obj (op s)).hom =
        Spec.algebraMap A (Localization.AtPrime q.asIdeal) ≫ σ ∧
    ∃ (w : Spec (.of F) ⟶
      ((baseChange (principalFractionTargetMap A F q p s)).obj Gs).obj.left),
      w ≫ r.hom.hom.left = z.left ∧
      w ≫ ((baseChange (principalFractionTargetMap A F q p s)).obj Gs).obj.hom =
        fractionSectionPoint A F p σ hσ ∧
      let Bs := Localization.Away (algebraMap A B (denominator q.asIdeal.primeCompl s))
      let ps := pullback.fst (Spec.algebraMap A (stage q.asIdeal.primeCompl s)) p
      let β := principalCoefficientBaseMap A B q s
      let bs := pullback.snd ps β
      let C := (baseChange (pullback.fst ps β)).obj Gs
      ∃ t : Finset Bs⁰, denominator Bs⁰ t ≠ 0 ∧ Nonempty (stageBaseOpen Bs⁰ t) ∧
        cohomologyPullback.{u, eX, u + 2}
          ((stageSourceOpen Bs⁰ (C.obj.hom ≫ bs) t).ι ≫ C.obj.hom ≫
            principalCoefficientFamilyMap A B q s p ≫ h) M degree c = 0

omit [IsDomain B] in
/-- Forget only the additional source-local mark, keeping the same cover,
generic mark, coefficient principal open and original class-zero witness. -/
theorem MarkedNormalOpenClassZeroWithLocalMark.forget
    (q : PrimeSpectrum A)
    (H : MarkedNormalOpenClassZeroWithLocalMark A B F p σ hσ Z z h M degree c q) :
    MarkedNormalOpenClassZero A B F p σ hσ Z z h M degree c q := by
  obtain ⟨s, Gs, r, het, hsurj, ρ, hρ, w, hw, hwbase, t, ht, hne, hc⟩ := H
  exact ⟨s, Gs, r, het, hsurj, w, hw, hwbase, t, ht, hne, hc⟩

/-- Extend the original whole marked cover and spread the original class zero.
The supplied generic zero is used only at this internal stage. -/
theorem marked_normalOpen_class_zero_with_localMark
    [IsNoetherianRing A] [IsIntegrallyClosed A]
    [CompactSpace X] [QuasiSeparatedSpace X] [Smooth p] [GeometricallyConnected p]
    [QuasiCompact p] [QuasiSeparated p]
    [IsGalois Z]
    (q : PrimeSpectrum A) (N : ℕ) (hN : 0 < N) (hunit : IsUnit (N : A))
    (hcard : Nat.card (Aut Z) ∣ N)
    (hc : cohomologyPullback.{u, eX, u + 2}
      (((baseChange (pullback.fst (pullback.snd p (Spec.algebraMap A F))
        (Spec.map (CommRingCat.ofHom a.toRingHom)))).obj Z).obj.hom ≫
          genericCoefficientFamilyMap A B F E a p ≫ h) M degree c = 0) :
    MarkedNormalOpenClassZeroWithLocalMark A B F p σ hσ Z z h M degree c q := by
  obtain ⟨G, hGI, hGG, hGc, rG, hrG, rN, b, hb, hba, ⟨rO⟩,
      s, Gs, es, d, hd, H, het, hsurj, hmark⟩ :=
    exists_marked_fraction_target_extension A F q p σ hσ N hN hunit Z z hcard
  let r := principalTargetCoverReconstruction A F q p s G Gs Z es rO
  have hzero' : cohomologyPullback.{u, eX, u + 2}
      (((baseChange (principalCoefficientGenericMap A B F E a q s p)).obj Z).obj.hom ≫
        pullback.fst
          (pullback.snd (pullback.fst (Spec.algebraMap A (stage q.asIdeal.primeCompl s)) p)
            (principalCoefficientBaseMap A B q s))
          (principalCoefficientFractionMap A B F E a q s) ≫
        principalCoefficientFamilyMap A B q s p ≫ h) M degree c = 0 := by
    exact original_class_zero_of_map_law
      (principalGenericCoverToOriginal A B F E a p q s Z) _ _
      (principalGenericCoverToOriginal_family A B F E a p q s Z h) M degree c hc
  obtain ⟨t, ht, hne, hzeroOpen⟩ :=
    exists_principalTarget_coefficient_open_zero A B F E a q s p Gs Z r h M degree c hzero'
  refine ⟨s, Gs, r, het, hsurj, rG ≫ d, hmark,
    principalTargetCoverMark A F q p s G Gs Z es rO σ hσ z, ?_, ?_, t, ht, hne, ?_⟩
  · exact principalTargetCoverMark_original A F q p s G Gs Z es rO σ hσ z
  · exact principalTargetCoverMark_section A F q p s G Gs Z es rO σ hσ z
  · exact hzeroOpen

/-- The original interface is the forgetting projection of the same stronger
construction, so its original cover, maps and class-zero witness are unchanged. -/
theorem marked_normalOpen_class_zero
    [IsNoetherianRing A] [IsIntegrallyClosed A]
    [CompactSpace X] [QuasiSeparatedSpace X] [Smooth p] [GeometricallyConnected p]
    [QuasiCompact p] [QuasiSeparated p]
    [IsGalois Z]
    (q : PrimeSpectrum A) (N : ℕ) (hN : 0 < N) (hunit : IsUnit (N : A))
    (hcard : Nat.card (Aut Z) ∣ N)
    (hc : cohomologyPullback.{u, eX, u + 2}
      (((baseChange (pullback.fst (pullback.snd p (Spec.algebraMap A F))
        (Spec.map (CommRingCat.ofHom a.toRingHom)))).obj Z).obj.hom ≫
          genericCoefficientFamilyMap A B F E a p ≫ h) M degree c = 0) :
    MarkedNormalOpenClassZero A B F p σ hσ Z z h M degree c q := by
  exact (marked_normalOpen_class_zero_with_localMark A B F E a p σ hσ Z z h
    M degree c q N hN hunit hcard hc).forget

end MarkedNormalOpenStage

section OriginalGenericClassProjections

variable (B k K L : Type u) [CommRing B] [Field k] [Field K] [Field L]
  [Algebra B K] [Algebra k K] [Algebra K L] [Algebra k L] [IsScalarTower k K L]
  {Y U : Scheme.{u}} (e : Y ⟶ Spec (.of B)) [QuasiCompact e] [QuasiSeparated e]
  (p : U ⟶ Spec (.of k))
  (aη : pullback e (Spec.algebraMap B K) ⟶ U)
  (Hη : IsPullback aη (pullback.snd e (Spec.algebraMap B K)) p (Spec.algebraMap k K))

omit [QuasiCompact e] [QuasiSeparated e] in
include Hη in
theorem genericCoefficientStageSquare :
    IsPullback
      (pullback.fst (pullback.snd e (Spec.algebraMap B K)) (Spec.algebraMap K L) ≫ aη)
      (pullback.snd (pullback.snd e (Spec.algebraMap B K)) (Spec.algebraMap K L))
      p (Spec.algebraMap k L) := by
  have ht : Spec.algebraMap K L ≫ Spec.algebraMap k K = Spec.algebraMap k L := by
    rw [← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext
      (IsScalarTower.algebraMap_eq k K L).symm)
  have H := (IsPullback.of_hasPullback
    (pullback.snd e (Spec.algebraMap B K)) (Spec.algebraMap K L)).paste_horiz Hη
  simpa only [ht] using H

omit [QuasiCompact e] [QuasiSeparated e] in
/-- The existing generic comparison retains its original source projection. -/
@[reassoc] theorem genericCoefficientStageIso_inv_source :
    (genericCoefficientStageIso B k K e p aη Hη L).inv ≫
        pullback.fst (pullback.snd e (Spec.algebraMap B K)) (Spec.algebraMap K L) ≫ aη =
      pullback.fst p (Spec.algebraMap k L) :=
  (genericCoefficientStageSquare B k K L e p aη Hη).isoPullback_inv_fst

omit [QuasiCompact e] [QuasiSeparated e] in
/-- The existing generic comparison retains its actual coefficient projection. -/
@[reassoc] theorem genericCoefficientStageIso_inv_field :
    (genericCoefficientStageIso B k K e p aη Hη L).inv ≫
        pullback.snd (pullback.snd e (Spec.algebraMap B K)) (Spec.algebraMap K L) =
      pullback.snd p (Spec.algebraMap k L) :=
  (genericCoefficientStageSquare B k K L e p aη Hη).isoPullback_inv_snd

end OriginalGenericClassProjections

section ActualFamilyClassMap

variable (A B k K L F E : Type u) [CommRing A] [CommRing B]
  [Field k] [Field K] [Field L] [Field F] [Field E]
  [Algebra A B] [Algebra A k] [Algebra A K] [Algebra B K] [Algebra k K]
  [IsScalarTower A B K] [IsScalarTower A k K]
  [Algebra K L] [Algebra k L] [IsScalarTower k K L]
  [Algebra k F] [Algebra k E] [Algebra L E] [IsScalarTower k L E]
  {X : Scheme.{u}} (p : X ⟶ Spec (.of A)) [QuasiCompact p] [QuasiSeparated p]
  (a : F →ₐ[k] E)

local notation "U" => pullback p (Spec.algebraMap A k)
local notation "pU" => pullback.snd p (Spec.algebraMap A k)
local notation "Y" => pullback p (Spec.algebraMap A B)
local notation "e" => pullback.snd p (Spec.algebraMap A B)
local notation "F₀" => separableClosure k F
local notation "E₀" => separableClosure L E
local notation "a₀" => separableSourceMap k F L E a
local notation "g" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom a₀))
local notation "p₀" => pullback.snd pU (Spec.algebraMap k F₀)
local notation "I" => genericCoefficientStageIso B k K e pU
  (familyGenericMap A B k K p) (familyGenericSquare A B k K p) L

/-- This is exactly the map in the generic H1 conclusion, before its cover leg. -/
abbrev originalGenericH1ClassMap : pullback p₀ g ⟶ Y :=
  separableFieldClassMap k L pU F E a ≫ (I).inv ≫
    pullback.fst (pullback.snd e (Spec.algebraMap B K)) (Spec.algebraMap K L) ≫
      pullback.fst e (Spec.algebraMap B K)

omit [QuasiCompact p] [QuasiSeparated p] in
@[reassoc] theorem originalGenericH1ClassMap_source :
    originalGenericH1ClassMap A B k K L F E p a ≫ pullback.fst p (Spec.algebraMap A B) =
      pullback.fst p₀ g ≫ pullback.fst pU (Spec.algebraMap k F₀) ≫
        pullback.fst p (Spec.algebraMap A k) := by
  have hi := congrArg (fun m => m ≫ pullback.fst p (Spec.algebraMap A k))
    (genericCoefficientStageIso_inv_source B k K L e pU
      (familyGenericMap A B k K p) (familyGenericSquare A B k K p))
  have hi' : (I).inv ≫
      pullback.fst (pullback.snd e (Spec.algebraMap B K)) (Spec.algebraMap K L) ≫
        pullback.fst e (Spec.algebraMap B K) ≫ pullback.fst p (Spec.algebraMap A B) =
      pullback.fst pU (Spec.algebraMap k L) ≫ pullback.fst p (Spec.algebraMap A k) := by
    simpa only [familyGenericMap, Category.assoc, pullback.lift_fst] using hi
  have hs : separableFieldClassMap k L pU F E a ≫ pullback.fst pU
      (Spec.algebraMap k L) = pullback.fst p₀ g ≫
        pullback.fst pU (Spec.algebraMap k F₀) := pullback.lift_fst ..
  exact (Category.assoc ..).trans
    ((congrArg (fun m => separableFieldClassMap k L pU F E a ≫ m) hi').trans
      ((Category.assoc ..).symm.trans
        (by simpa only [Category.assoc] using
          congrArg (fun m => m ≫ pullback.fst p (Spec.algebraMap A k)) hs)))

omit [QuasiCompact p] [QuasiSeparated p] in
@[reassoc] theorem originalGenericH1ClassMap_coefficient :
    originalGenericH1ClassMap A B k K L F E p a ≫ e =
      pullback.snd p₀ g ≫ Spec.algebraMap L E₀ ≫
        Spec.algebraMap K L ≫ Spec.algebraMap B K := by
  have hi := genericCoefficientStageIso_inv_field B k K L e pU
    (familyGenericMap A B k K p) (familyGenericSquare A B k K p)
  have hs : separableFieldClassMap k L pU F E a ≫ pullback.snd pU
      (Spec.algebraMap k L) = pullback.snd p₀ g ≫ Spec.algebraMap L E₀ :=
    pullback.lift_snd ..
  have hp := pullback.condition (f := pullback.snd e (Spec.algebraMap B K))
    («g» := Spec.algebraMap K L)
  have hb := pullback.condition (f := e) («g» := Spec.algebraMap B K)
  calc
    _ = separableFieldClassMap k L pU F E a ≫ (I).inv ≫
        pullback.fst (pullback.snd e (Spec.algebraMap B K)) (Spec.algebraMap K L) ≫
          pullback.snd e (Spec.algebraMap B K) ≫ Spec.algebraMap B K := by
      simpa only [Category.assoc] using congrArg
        (fun m => separableFieldClassMap k L pU F E a ≫ (I).inv ≫
          pullback.fst (pullback.snd e (Spec.algebraMap B K)) (Spec.algebraMap K L) ≫ m) hb
    _ = separableFieldClassMap k L pU F E a ≫ (I).inv ≫
        pullback.snd (pullback.snd e (Spec.algebraMap B K)) (Spec.algebraMap K L) ≫
          Spec.algebraMap K L ≫ Spec.algebraMap B K := by
      simpa only [Category.assoc] using congrArg
        (fun m => separableFieldClassMap k L pU F E a ≫ (I).inv ≫ m ≫
          Spec.algebraMap B K) hp
    _ = separableFieldClassMap k L pU F E a ≫ pullback.snd pU
        (Spec.algebraMap k L) ≫ Spec.algebraMap K L ≫ Spec.algebraMap B K := by
      simpa only [Category.assoc] using congrArg
        (fun m => separableFieldClassMap k L pU F E a ≫ m ≫
          Spec.algebraMap K L ≫ Spec.algebraMap B K) hi
    _ = _ := by
      simpa only [Category.assoc] using congrArg
        (fun m => m ≫ Spec.algebraMap K L ≫ Spec.algebraMap B K) hs

end ActualFamilyClassMap

section NormalizationFamilyGeometry

variable {X S R B T F K : Scheme.{u}} (p : X ⟶ S)
  (σ : S ⟶ X) (hσ : σ ≫ p = 𝟙 _)

/-- The pullback of the original section along the base change. -/
def normalModelSection (r : R ⟶ S) : R ⟶ pullback p r :=
  pullback.lift (r ≫ σ) (𝟙 _) (by simp only [Category.assoc, hσ,
    Category.comp_id, Category.id_comp])

@[reassoc] theorem normalModelSection_source (r : R ⟶ S) :
    normalModelSection p σ hσ r ≫ pullback.fst p r = r ≫ σ := pullback.lift_fst ..

theorem normalModelSection_over (r : R ⟶ S) :
    normalModelSection p σ hσ r ≫ pullback.snd p r = 𝟙 _ := pullback.lift_snd ..

variable (r : R ⟶ S) (b : B ⟶ S) (t : T ⟶ B) (v : T ⟶ R)
  (hvb : v ≫ r = t ≫ b)

/-- The actual family over the coefficient normalization maps to the original
family through the original normalization square. -/
def normalizedFamilyMap : pullback (pullback.snd p r) v ⟶ pullback p b :=
  pullback.map (pullback.snd p r) v p b
    (pullback.fst p r) t r pullback.condition.symm hvb

@[reassoc] theorem normalizedFamilyMap_source :
    normalizedFamilyMap p r b t v hvb ≫ pullback.fst p b =
      pullback.fst (pullback.snd p r) v ≫ pullback.fst p r :=
  pullback.lift_fst ..

@[reassoc] theorem normalizedFamilyMap_coefficient :
    normalizedFamilyMap p r b t v hvb ≫ pullback.snd p b =
      pullback.snd (pullback.snd p r) v ≫ t := pullback.lift_snd ..

variable (k : K ⟶ S) (aF : F ⟶ K) (rF : F ⟶ R)
  (hF : rF ≫ r = aF ≫ k)

/-- The canonical comparison respects the original section over the whole field. -/
theorem normalGenericFibreIso_normalModelSection :
    normalModelSection (pullback.snd p r) (normalModelSection p σ hσ r)
        (normalModelSection_over p σ hσ r) rF ≫
        (normalGenericFibreIso p k r aF rF hF).hom =
      normalModelSection (pullback.snd p k) (normalModelSection p σ hσ k)
        (normalModelSection_over p σ hσ k) aF := by
  apply normalGenericFibreIso_point
  · simp only [normalModelSection_source_assoc, normalModelSection_source]
    exact (Category.assoc ..).symm.trans
      ((congrArg (fun m => m ≫ σ) hF).trans (Category.assoc ..))
  · simp only [normalModelSection_over]

end NormalizationFamilyGeometry

section LiteralNormalModels

variable (A B k K F E : Type u) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
  [IsNoetherianRing A] [IsIntegrallyClosed A] [IsNoetherianRing B] [IsIntegrallyClosed B]
  [Field k] [Field K] [Field F] [Field E]
  [Algebra A B] [Algebra A k] [IsFractionRing A k]
  [Algebra A K] [Algebra B K] [IsFractionRing B K] [Algebra k K]
  [IsScalarTower A B K] [IsScalarTower A k K]
  [Algebra k F] [Module.Finite k F] [Algebra.IsSeparable k F]
  [Algebra K E] [Module.Finite K E] [Algebra.IsSeparable K E]
  [Algebra k E] [IsScalarTower k K E]
  [Algebra A F] [IsScalarTower A k F]
  [Algebra A E] [Algebra B E] [IsScalarTower A k E]
  [IsScalarTower B K E] [IsScalarTower A B E]
  (a : F →ₐ[k] E)
  {X : Scheme.{u}} (p : X ⟶ Spec (.of A))
  (σ : Spec (.of A) ⟶ X) (hσ : σ ≫ p = 𝟙 _)

local notation "U" => pullback p (Spec.algebraMap A k)
local notation "pU" => pullback.snd p (Spec.algebraMap A k)
local notation "x" => normalModelSection p σ hσ (Spec.algebraMap A k)
local notation "hx" => normalModelSection_over p σ hσ (Spec.algebraMap A k)
local notation "xF" => normalModelSection pU x hx (Spec.algebraMap k F)
local notation "Y" => pullback p (Spec.algebraMap A B)

/-- The conclusion uses the two literal integral closures and their actual
normalization maps. The marked cover is transported only by the canonical
original generic-fibre isomorphism. Both principal opens are retained. -/
def LiteralNormalMarkedOpen
    (Z : FiniteEtale (pullback pU (Spec.algebraMap k F))) (z : Fiber xF Z)
    [HasExt.{eX} (AbelianSheaf.{u, u + 1} Y)]
    (M : AbelianSheaf.{u, u + 1} Y) (degree : ℕ) (c : Sheaf.H.{eX} M degree)
    (qB : PrimeSpectrum B) : Prop :=
  let R := integralClosure A F
  let S := integralClosure B E
  let hR := SeparableBaseSquare.normal_finite_model A k F
  let hS := SeparableBaseSquare.normal_finite_model B K E
  letI : IsNoetherianRing R := hR.2.1
  letI : IsIntegrallyClosed R := hR.2.2.1
  letI : IsFractionRing R F := hR.2.2.2.1
  letI : IsFractionRing S E := hS.2.2.2.1
  let φ := SeparableBaseSquare.closureMap A B k F E a
  letI : Algebra R S := φ.toRingHom.toAlgebra
  letI : Algebra R E := (a.toRingHom.comp (algebraMap R F)).toAlgebra
  letI : IsScalarTower R S E := IsScalarTower.of_algebraMap_eq' rfl
  let aR : F →ₐ[R] E := { a.toRingHom with commutes' := fun _ => rfl }
  let pR := pullback.snd p (Spec.algebraMap A R)
  let σR := normalModelSection p σ hσ (Spec.algebraMap A R)
  let hσR := normalModelSection_over p σ hσ (Spec.algebraMap A R)
  let ht : Spec.algebraMap R F ≫ Spec.algebraMap A R =
      Spec.algebraMap k F ≫ Spec.algebraMap A k := by
    simp only [Spec.algebraMap, ← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext
      ((IsScalarTower.algebraMap_eq A R F).symm.trans
        (IsScalarTower.algebraMap_eq A k F)))
  let i := normalGenericFibreIso p (Spec.algebraMap A k) (Spec.algebraMap A R)
    (Spec.algebraMap k F) (Spec.algebraMap R F) ht
  let ZR := (baseChange i.hom).obj Z
  let zR := normalGenericCoverPoint i Z xF
    (normalModelSection pR σR hσR (Spec.algebraMap R F))
    (normalGenericFibreIso_normalModelSection p σ hσ (Spec.algebraMap A R)
      (Spec.algebraMap A k) (Spec.algebraMap k F) (Spec.algebraMap R F) ht) z
  let hn := normalizedFamilyMap p (Spec.algebraMap A R) (Spec.algebraMap A B)
    (Spec.algebraMap B S) (Spec.map (CommRingCat.ofHom φ.toRingHom))
    (SeparableBaseSquare.spec_square A B k F E a)
  Module.Finite A R ∧ IsFinite (Spec.algebraMap A R) ∧
    Module.Finite B S ∧ IsNoetherianRing S ∧ IsIntegrallyClosed S ∧
    IsFinite (Spec.algebraMap B S) ∧
    ∃ qS : PrimeSpectrum S,
      PrimeSpectrum.comap (algebraMap B S) qS = qB ∧
      MarkedNormalOpenClassZero R S F pR σR hσR ZR zR hn M degree c
        (PrimeSpectrum.comap φ.toRingHom qS)

/-- The literal finite normal models with the same original generic mark and
coefficient-open zero also retain the actual source-local mark on the cover. -/
def LiteralNormalMarkedOpenWithLocalMark
    (Z : FiniteEtale (pullback pU (Spec.algebraMap k F))) (z : Fiber xF Z)
    [HasExt.{eX} (AbelianSheaf.{u, u + 1} Y)]
    (M : AbelianSheaf.{u, u + 1} Y) (degree : ℕ) (c : Sheaf.H.{eX} M degree)
    (qB : PrimeSpectrum B) : Prop :=
  let R := integralClosure A F
  let S := integralClosure B E
  let hR := SeparableBaseSquare.normal_finite_model A k F
  let hS := SeparableBaseSquare.normal_finite_model B K E
  letI : IsNoetherianRing R := hR.2.1
  letI : IsIntegrallyClosed R := hR.2.2.1
  letI : IsFractionRing R F := hR.2.2.2.1
  letI : IsFractionRing S E := hS.2.2.2.1
  let φ := SeparableBaseSquare.closureMap A B k F E a
  letI : Algebra R S := φ.toRingHom.toAlgebra
  letI : Algebra R E := (a.toRingHom.comp (algebraMap R F)).toAlgebra
  letI : IsScalarTower R S E := IsScalarTower.of_algebraMap_eq' rfl
  let aR : F →ₐ[R] E := { a.toRingHom with commutes' := fun _ => rfl }
  let pR := pullback.snd p (Spec.algebraMap A R)
  let σR := normalModelSection p σ hσ (Spec.algebraMap A R)
  let hσR := normalModelSection_over p σ hσ (Spec.algebraMap A R)
  let ht : Spec.algebraMap R F ≫ Spec.algebraMap A R =
      Spec.algebraMap k F ≫ Spec.algebraMap A k := by
    simp only [Spec.algebraMap, ← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext
      ((IsScalarTower.algebraMap_eq A R F).symm.trans
        (IsScalarTower.algebraMap_eq A k F)))
  let i := normalGenericFibreIso p (Spec.algebraMap A k) (Spec.algebraMap A R)
    (Spec.algebraMap k F) (Spec.algebraMap R F) ht
  let ZR := (baseChange i.hom).obj Z
  let zR := normalGenericCoverPoint i Z xF
    (normalModelSection pR σR hσR (Spec.algebraMap R F))
    (normalGenericFibreIso_normalModelSection p σ hσ (Spec.algebraMap A R)
      (Spec.algebraMap A k) (Spec.algebraMap k F) (Spec.algebraMap R F) ht) z
  let hn := normalizedFamilyMap p (Spec.algebraMap A R) (Spec.algebraMap A B)
    (Spec.algebraMap B S) (Spec.map (CommRingCat.ofHom φ.toRingHom))
    (SeparableBaseSquare.spec_square A B k F E a)
  Module.Finite A R ∧ IsFinite (Spec.algebraMap A R) ∧
    Module.Finite B S ∧ IsNoetherianRing S ∧ IsIntegrallyClosed S ∧
    IsFinite (Spec.algebraMap B S) ∧
    ∃ qS : PrimeSpectrum S,
      PrimeSpectrum.comap (algebraMap B S) qS = qB ∧
      MarkedNormalOpenClassZeroWithLocalMark R S F pR σR hσR ZR zR hn M degree c
        (PrimeSpectrum.comap φ.toRingHom qS)

omit [Algebra A K] [Algebra k K] [IsScalarTower A B K]
  [IsScalarTower A k K] [IsScalarTower k K E] in
/-- Forget the source-local mark without changing either literal normal
model, its chosen prime, the original cover, or the original class-zero data. -/
theorem LiteralNormalMarkedOpenWithLocalMark.forget
    (Z : FiniteEtale (pullback pU (Spec.algebraMap k F))) (z : Fiber xF Z)
    [HasExt.{eX} (AbelianSheaf.{u, u + 1} Y)]
    (M : AbelianSheaf.{u, u + 1} Y) (degree : ℕ) (c : Sheaf.H.{eX} M degree)
    (qB : PrimeSpectrum B)
    (H : LiteralNormalMarkedOpenWithLocalMark A B k K F E a p σ hσ Z z M degree c qB) :
    LiteralNormalMarkedOpen A B k K F E a p σ hσ Z z M degree c qB := by
  obtain ⟨hR, hfR, hS, hnoethS, hnormalS, hfS, qS, hqS, hmarked⟩ := H
  obtain ⟨s, Gs, r, het, hsurj, ρ, hρ, w, hw, hwbase, t, ht, hne, hc⟩ := hmarked
  exact ⟨hR, hfR, hS, hnoethS, hnormalS, hfS, qS, hqS,
    s, Gs, r, het, hsurj, w, hw, hwbase, t, ht, hne, hc⟩

omit [Algebra A K] [Algebra k K] [IsScalarTower A B K]
  [IsScalarTower A k K] [IsScalarTower k K E] in
/-- Normalize the actual two separable generic fields and transport the entire
original marked cover and class before applying marked open spreading. -/
theorem normalMarkedCoverTransport_of_generic_zero_with_localMark
    [QuasiCompact p] [QuasiSeparated p] [Smooth p] [GeometricallyConnected p]
    (Z : FiniteEtale (pullback pU (Spec.algebraMap k F))) [IsGalois Z]
    (z : Fiber xF Z) (qB : PrimeSpectrum B)
    [HasExt.{eX} (AbelianSheaf.{u, u + 1} Y)]
    (M : AbelianSheaf.{u, u + 1} Y) (degree : ℕ) (c : Sheaf.H.{eX} M degree)
    (N : ℕ) (hN : 0 < N) (hunit : IsUnit (N : A)) (hcard : Nat.card (Aut Z) ∣ N)
    (h0 : pullback (pullback.snd pU (Spec.algebraMap k F))
      (Spec.map (CommRingCat.ofHom a.toRingHom)) ⟶ Y)
    (h0X : h0 ≫ pullback.fst p (Spec.algebraMap A B) =
      pullback.fst (pullback.snd pU (Spec.algebraMap k F))
        (Spec.map (CommRingCat.ofHom a.toRingHom)) ≫
        pullback.fst pU (Spec.algebraMap k F) ≫ pullback.fst p (Spec.algebraMap A k))
    (h0B : h0 ≫ pullback.snd p (Spec.algebraMap A B) =
      pullback.snd (pullback.snd pU (Spec.algebraMap k F))
        (Spec.map (CommRingCat.ofHom a.toRingHom)) ≫ Spec.algebraMap B E)
    (hc : cohomologyPullback.{u, eX, u + 2}
      (((baseChange (pullback.fst (pullback.snd pU (Spec.algebraMap k F))
        (Spec.map (CommRingCat.ofHom a.toRingHom)))).obj Z).obj.hom ≫ h0)
      M degree c = 0) :
    LiteralNormalMarkedOpenWithLocalMark A B k K F E a p σ hσ Z z M degree c qB := by
  let R := integralClosure A F
  let S := integralClosure B E
  have hR := SeparableBaseSquare.normal_finite_model A k F
  have hS := SeparableBaseSquare.normal_finite_model B K E
  let : IsNoetherianRing R := hR.2.1
  let : IsIntegrallyClosed R := hR.2.2.1
  let : IsFractionRing R F := hR.2.2.2.1
  let : IsFractionRing S E := hS.2.2.2.1
  let φ := SeparableBaseSquare.closureMap A B k F E a
  let : Algebra R S := φ.toRingHom.toAlgebra
  let : Algebra R E := (a.toRingHom.comp (algebraMap R F)).toAlgebra
  let : IsScalarTower R S E := IsScalarTower.of_algebraMap_eq' rfl
  let aR : F →ₐ[R] E := { a.toRingHom with commutes' := fun _ => rfl }
  let pR := pullback.snd p (Spec.algebraMap A R)
  let σR := normalModelSection p σ hσ (Spec.algebraMap A R)
  let hσR := normalModelSection_over p σ hσ (Spec.algebraMap A R)
  have ht : Spec.algebraMap R F ≫ Spec.algebraMap A R =
      Spec.algebraMap k F ≫ Spec.algebraMap A k := by
    simp only [Spec.algebraMap, ← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext
      ((IsScalarTower.algebraMap_eq A R F).symm.trans
        (IsScalarTower.algebraMap_eq A k F)))
  let i := normalGenericFibreIso p (Spec.algebraMap A k) (Spec.algebraMap A R)
    (Spec.algebraMap k F) (Spec.algebraMap R F) ht
  let ZR := (baseChange i.hom).obj Z
  let zR := normalGenericCoverPoint i Z xF
    (normalModelSection pR σR hσR (Spec.algebraMap R F))
    (normalGenericFibreIso_normalModelSection p σ hσ (Spec.algebraMap A R)
      (Spec.algebraMap A k) (Spec.algebraMap k F) (Spec.algebraMap R F) ht) z
  let hn := normalizedFamilyMap p (Spec.algebraMap A R) (Spec.algebraMap A B)
    (Spec.algebraMap B S) (Spec.map (CommRingCat.ofHom φ.toRingHom))
    (SeparableBaseSquare.spec_square A B k F E a)
  let f0 := pullback.snd pU (Spec.algebraMap k F)
  let fR := pullback.snd pR (Spec.algebraMap R F)
  let g := Spec.map (CommRingCat.ofHom a.toRingHom)
  have hiF : i.hom ≫ f0 = fR := normalGenericFibreIso_field ..
  let v := pullback.map fR g f0 g i.hom (𝟙 _) (𝟙 _)
    (by simpa only [Category.comp_id] using hiF.symm) (by simp)
  let C0 := (baseChange (pullback.fst f0 g)).obj Z
  let CR := (baseChange (pullback.fst fR g)).obj ZR
  have hvX : v ≫ pullback.fst f0 g = pullback.fst fR g ≫ i.hom := pullback.lift_fst ..
  have hvE : v ≫ pullback.snd f0 g = pullback.snd fR g := by
    exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  let vC : CR.obj.left ⟶ C0.obj.left :=
    pullback.lift (pullback.fst ZR.obj.hom (pullback.fst fR g) ≫ pullback.fst Z.obj.hom i.hom)
      (CR.obj.hom ≫ v) (by
        have hZ := pullback.condition (f := Z.obj.hom) («g» := i.hom)
        have hR := pullback.condition (f := ZR.obj.hom) («g» := pullback.fst fR g)
        exact (Category.assoc ..).trans
          ((congrArg (fun m => pullback.fst ZR.obj.hom (pullback.fst fR g) ≫ m) hZ).trans
            ((Category.assoc ..).symm.trans
              ((congrArg (fun m => m ≫ i.hom) hR).trans
                ((Category.assoc ..).trans
                  (congrArg (fun m => CR.obj.hom ≫ m) hvX.symm))))))
  have hvC : vC ≫ C0.obj.hom = CR.obj.hom ≫ v := pullback.lift_snd ..
  have hGfst : genericCoefficientFamilyMap R S F E aR pR ≫
      pullback.fst pR (Spec.map (CommRingCat.ofHom φ.toRingHom)) =
      pullback.fst fR g ≫ pullback.fst pR (Spec.algebraMap R F) := pullback.lift_fst ..
  have hGsnd : genericCoefficientFamilyMap R S F E aR pR ≫
      pullback.snd pR (Spec.map (CommRingCat.ofHom φ.toRingHom)) =
      pullback.snd fR g ≫ Spec.algebraMap S E := pullback.lift_snd ..
  have hnX : hn ≫ pullback.fst p (Spec.algebraMap A B) =
      pullback.fst pR (Spec.map (CommRingCat.ofHom φ.toRingHom)) ≫
        pullback.fst p (Spec.algebraMap A R) := pullback.lift_fst ..
  have hnB : hn ≫ pullback.snd p (Spec.algebraMap A B) =
      pullback.snd pR (Spec.map (CommRingCat.ofHom φ.toRingHom)) ≫
        Spec.algebraMap B S := pullback.lift_snd ..
  have hfamily : v ≫ h0 = genericCoefficientFamilyMap R S F E aR pR ≫ hn := by
    apply pullback.hom_ext
    · have hiX := normalGenericFibreIso_source p (Spec.algebraMap A k)
        (Spec.algebraMap A R) (Spec.algebraMap k F) (Spec.algebraMap R F) ht
      calc
        _ = v ≫ pullback.fst f0 g ≫ pullback.fst pU (Spec.algebraMap k F) ≫
            pullback.fst p (Spec.algebraMap A k) := by
          simpa only [Category.assoc] using congrArg (fun m => v ≫ m) h0X
        _ = pullback.fst fR g ≫ i.hom ≫ pullback.fst pU (Spec.algebraMap k F) ≫
            pullback.fst p (Spec.algebraMap A k) := by
          simpa only [Category.assoc] using congrArg (fun m => m ≫
            pullback.fst pU (Spec.algebraMap k F) ≫ pullback.fst p (Spec.algebraMap A k)) hvX
        _ = pullback.fst fR g ≫ pullback.fst pR (Spec.algebraMap R F) ≫
            pullback.fst p (Spec.algebraMap A R) := congrArg (fun m => pullback.fst fR g ≫ m) hiX
        _ = _ := by
          simpa only [Category.assoc] using
            ((congrArg (fun m => genericCoefficientFamilyMap R S F E aR pR ≫ m) hnX).trans
              (by
                simpa only [Category.assoc] using congrArg
                  (fun m => m ≫ pullback.fst p (Spec.algebraMap A R)) hGfst)).symm
    · have hSE : Spec.algebraMap S E ≫ Spec.algebraMap B S = Spec.algebraMap B E := by
        simp only [Spec.algebraMap, ← Spec.map_comp]
        exact congrArg Spec.map (CommRingCat.hom_ext (IsScalarTower.algebraMap_eq B S E).symm)
      calc
        _ = v ≫ pullback.snd f0 g ≫ Spec.algebraMap B E := by
          simpa only [Category.assoc] using congrArg (fun m => v ≫ m) h0B
        _ = pullback.snd fR g ≫ Spec.algebraMap B E := by
          simpa only [Category.assoc] using congrArg (fun m => m ≫ Spec.algebraMap B E) hvE
        _ = pullback.snd fR g ≫ Spec.algebraMap S E ≫ Spec.algebraMap B S :=
          congrArg (fun m => pullback.snd fR g ≫ m) hSE.symm
        _ = _ := by
          simpa only [Category.assoc] using
            ((congrArg (fun m => genericCoefficientFamilyMap R S F E aR pR ≫ m) hnB).trans
              (by
                simpa only [Category.assoc] using congrArg
                  (fun m => m ≫ Spec.algebraMap B S) hGsnd)).symm
  have hcover : vC ≫ (C0.obj.hom ≫ h0) =
      CR.obj.hom ≫ genericCoefficientFamilyMap R S F E aR pR ≫ hn :=
    (Category.assoc ..).symm.trans ((congrArg (fun m => m ≫ h0) hvC).trans
      ((Category.assoc ..).trans (congrArg (fun m => CR.obj.hom ≫ m) hfamily)))
  have hcR : cohomologyPullback.{u, eX, u + 2}
      (CR.obj.hom ≫ genericCoefficientFamilyMap R S F E aR pR ≫ hn) M degree c = 0 := by
    exact original_class_zero_of_map_law vC (C0.obj.hom ≫ h0) _ hcover M degree c hc
  let : ConnectedSpace (pullback pU (Spec.algebraMap k F) : Scheme.{u}) :=
    GeometricallyConnected.connectedSpace_of_subsingleton f0
  let : ConnectedSpace Z.obj.left := Connectedness.connectedSpace_of_categoricalConnected Z
  let : ConnectedSpace ZR.obj.left :=
    (asIso (pullback.fst Z.obj.hom i.hom)).inv.homeomorph.connectedSpace_iff.mp inferInstance
  let : IsGalois ZR := baseChange_isGalois_of_connected i.hom Z
  have hcardR : Nat.card (Aut ZR) ∣ N :=
    (baseChange_card_aut_of_connected i.hom Z) ▸ hcard
  let : CompactSpace (pullback p (Spec.algebraMap A R) : Scheme.{u}) :=
    QuasiCompact.compactSpace_of_compactSpace pR
  let : QuasiSeparatedSpace (pullback p (Spec.algebraMap A R) : Scheme.{u}) :=
    quasiSeparatedSpace_of_quasiSeparated pR
  obtain ⟨qS, hqS⟩ := SeparableBaseSquare.exists_closure_prime B K E qB
  have hunitR : IsUnit (N : R) := by
    simpa only [map_natCast] using hunit.map (algebraMap A R)
  have hmarked := marked_normalOpen_class_zero_with_localMark R S F E aR pR σR hσR ZR zR hn
    M degree c (PrimeSpectrum.comap φ.toRingHom qS) N hN hunitR hcardR hcR
  exact ⟨hR.1, hR.2.2.2.2, hS.1, hS.2.1, hS.2.2.1, hS.2.2.2.2,
    qS, hqS, hmarked⟩

omit [Algebra A K] [Algebra k K] [IsScalarTower A B K]
  [IsScalarTower A k K] [IsScalarTower k K E] in
/-- The original literal-model endpoint forgets only the additional local
source mark of the same stronger transport construction. -/
theorem normalMarkedCoverTransport_of_generic_zero
    [QuasiCompact p] [QuasiSeparated p] [Smooth p] [GeometricallyConnected p]
    (Z : FiniteEtale (pullback pU (Spec.algebraMap k F))) [IsGalois Z]
    (z : Fiber xF Z) (qB : PrimeSpectrum B)
    [HasExt.{eX} (AbelianSheaf.{u, u + 1} Y)]
    (M : AbelianSheaf.{u, u + 1} Y) (degree : ℕ) (c : Sheaf.H.{eX} M degree)
    (N : ℕ) (hN : 0 < N) (hunit : IsUnit (N : A)) (hcard : Nat.card (Aut Z) ∣ N)
    (h0 : pullback (pullback.snd pU (Spec.algebraMap k F))
      (Spec.map (CommRingCat.ofHom a.toRingHom)) ⟶ Y)
    (h0X : h0 ≫ pullback.fst p (Spec.algebraMap A B) =
      pullback.fst (pullback.snd pU (Spec.algebraMap k F))
        (Spec.map (CommRingCat.ofHom a.toRingHom)) ≫
        pullback.fst pU (Spec.algebraMap k F) ≫ pullback.fst p (Spec.algebraMap A k))
    (h0B : h0 ≫ pullback.snd p (Spec.algebraMap A B) =
      pullback.snd (pullback.snd pU (Spec.algebraMap k F))
        (Spec.map (CommRingCat.ofHom a.toRingHom)) ≫ Spec.algebraMap B E)
    (hc : cohomologyPullback.{u, eX, u + 2}
      (((baseChange (pullback.fst (pullback.snd pU (Spec.algebraMap k F))
        (Spec.map (CommRingCat.ofHom a.toRingHom)))).obj Z).obj.hom ≫ h0)
      M degree c = 0) :
    LiteralNormalMarkedOpen A B k K F E a p σ hσ Z z M degree c qB := by
  exact (normalMarkedCoverTransport_of_generic_zero_with_localMark
    A B k K F E a p σ hσ Z z qB M degree c N hN hunit hcard h0 h0X h0B hc).forget

end LiteralNormalModels

end AlgebraicGeometry.Scheme.EtaleCohomology.TwoFieldEffacement
