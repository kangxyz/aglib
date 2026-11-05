/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.GenericWholePointedExtension
public import Mathlib.RingTheory.Localization.AsSubring

/-! # The original chosen fraction-field cover extends over the whole base

The specified fraction field is compared to the native function field by its
canonical localization equivalence. Both actual fibre projections and the
whole original generic cover are transported through the resulting scheme
isomorphisms. One invocation of whole pointed extension returns a single
global cover, with an actual Cartesian reconstruction of the original cover
and the original chosen-field marking triangles.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery

universe u

variable (A F : Type u) [CommRing A] [IsDomain A] [Field F]
    [Algebra A F] [IsFractionRing A F]

/-- The original coordinate ring acts on the function field of its spectrum. -/
local instance fractionWholeNativeAlgebra : Algebra A (Spec (.of A)).functionField :=
  AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (.of A)

local instance fractionWhole_nativeFractionRing :
    IsFractionRing A (Spec (.of A)).functionField :=
  functionField_isFractionRing_of_affine (.of A)

local notation "γ" => Scheme.fromSpecStalk (Spec (CommRingCat.of A))
  (genericPoint (Spec (CommRingCat.of A)))
local notation "sF" => Spec.algebraMap A F

/-- The canonical equivalence with the original specified fraction field. -/
def fractionFunctionFieldEquiv : (Spec (.of A)).functionField ≃ₐ[A] F :=
  IsLocalization.algEquiv (nonZeroDivisors A) _ F

/-- The actual spectrum isomorphism, in the contravariant direction. -/
def fractionGenericSpectrumIso : Spec (.of F) ≅ Spec (Spec (.of A)).functionField :=
  Scheme.Spec.mapIso (fractionFunctionFieldEquiv A F).toRingEquiv.toCommRingCatIso.op

@[reassoc (attr := simp)]
theorem fractionGenericSpectrumIso_hom_generic :
    (fractionGenericSpectrumIso A F).hom ≫ γ = sF := by
  rw [Spec.fromSpecStalk_eq']
  change Spec.map (CommRingCat.ofHom (fractionFunctionFieldEquiv A F).toRingHom) ≫
    Spec.algebraMap A (Spec (.of A)).functionField = _
  exact Spec.map_algHom_algebraMap (fractionFunctionFieldEquiv A F).toAlgHom

@[reassoc (attr := simp)]
theorem fractionGenericSpectrumIso_inv_fraction :
    (fractionGenericSpectrumIso A F).inv ≫ sF = γ := by
  rw [← fractionGenericSpectrumIso_hom_generic A F]
  simp only [Iso.inv_hom_id_assoc]

/-- Every original coefficient embedding is transported by the same actual
spectrum isomorphism, with its literal composed field homomorphism. -/
@[reassoc]
theorem fractionGenericSpectrumIso_embedding
    (E : Type u) [Field E] [Algebra A E] (a : F →ₐ[A] E) :
    Spec.map (CommRingCat.ofHom a.toRingHom) ≫ (fractionGenericSpectrumIso A F).hom =
      Spec.map (CommRingCat.ofHom
        (a.comp (fractionFunctionFieldEquiv A F).toAlgHom).toRingHom) := by
  change Spec.map (CommRingCat.ofHom a.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (fractionFunctionFieldEquiv A F).toRingHom) = _
  rw [← Spec.map_comp]
  rfl

variable {X : Scheme.{u}} (p : X ⟶ Spec (.of A))

local notation "πF" => pullback.fst p sF
local notation "πN" => pullback.fst p γ
local notation "eK" => fractionGenericSpectrumIso A F

/-- The original chosen-field fibre is canonically the native generic fibre. -/
def fractionGenericFiberIso : pullback p sF ≅ pullback p γ :=
  asIso (pullback.map p sF p γ (𝟙 _) (eK).hom (𝟙 _)
    (by simp) (by simp))

@[reassoc (attr := simp)]
theorem fractionGenericFiberIso_hom_fst :
    (fractionGenericFiberIso A F p).hom ≫ πN = πF := by
  simp only [fractionGenericFiberIso, asIso_hom, pullback.map, pullback.lift_fst,
    Category.comp_id]

@[reassoc (attr := simp)]
theorem fractionGenericFiberIso_hom_snd :
    (fractionGenericFiberIso A F p).hom ≫ pullback.snd p γ =
      pullback.snd p sF ≫ (eK).hom := by
  simp only [fractionGenericFiberIso, asIso_hom, pullback.map, pullback.lift_snd]

@[reassoc (attr := simp)]
theorem fractionGenericFiberIso_inv_fst :
    (fractionGenericFiberIso A F p).inv ≫ πF = πN := by
  rw [← fractionGenericFiberIso_hom_fst A F p]
  simp only [Iso.inv_hom_id_assoc]

variable (Z : FiniteEtale (pullback p (Spec.algebraMap A F)))
local notation "eX" => fractionGenericFiberIso A F p
local notation "ZN" => Functor.obj (baseChange (Iso.inv eX)) Z

/-- The native presentation is the actual pullback of the unchanged original cover. -/
def fractionGenericCoverOriginalIso :
    pullback Z.obj.hom (eX).inv ≅ Z.obj.left := by
  let : IsIso (eX).inv := (eX).isIso_inv
  let : IsIso (pullback.fst Z.obj.hom (eX).inv) :=
    (IsPullback.of_hasPullback Z.obj.hom (eX).inv).isIso_fst_of_isIso
  exact asIso (pullback.fst Z.obj.hom (eX).inv)

@[reassoc]
theorem fractionGenericCoverOriginalIso_inv_over :
    (fractionGenericCoverOriginalIso A F p Z).inv ≫ pullback.snd Z.obj.hom (eX).inv =
      Z.obj.hom ≫ (eX).hom := by
  apply (cancel_epi (fractionGenericCoverOriginalIso A F p Z).hom).mp
  rw [Iso.hom_inv_id_assoc]
  change pullback.snd Z.obj.hom (eX).inv =
    pullback.fst Z.obj.hom (eX).inv ≫ Z.obj.hom ≫ (eX).hom
  rw [pullback.condition_assoc]
  simp only [Iso.inv_hom_id, Category.comp_id]

variable [IsNoetherianRing A] [IsIntegrallyClosed A]
    [CompactSpace X] [QuasiSeparatedSpace X] [Smooth p] [GeometricallyConnected p]

local instance fractionWhole_originalConnected : ConnectedSpace (pullback p sF : Scheme.{u}) :=
  GeometricallyConnected.connectedSpace_of_subsingleton (pullback.snd p sF)

local instance fractionWhole_nativeConnected : ConnectedSpace (pullback p γ : Scheme.{u}) := by
  let : Subsingleton (Spec (Spec (.of A)).functionField) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum (Spec (.of A)).functionField))
  exact GeometricallyConnected.connectedSpace_of_subsingleton (pullback.snd p γ)

/-- Extend the actual cover over the specified fraction field once, retaining
its full original mark and an actual Cartesian reconstruction over that same
field. No source prime or source restriction is introduced. -/
theorem exists_fraction_whole_galoisPointedExtension
    (σ : Spec (.of A) ⟶ X) (hσ : σ ≫ p = 𝟙 _)
    (N : ℕ) (hN : 0 < N) (hunit : IsUnit (N : A)) [IsGalois Z]
    (hcard : Nat.card (Aut Z) ∣ N)
    (z : Spec (.of F) ⟶ Z.obj.left) (hz : z ≫ Z.obj.hom ≫ πF = sF ≫ σ) :
    letI : ConnectedSpace X := GeometricallyConnected.connectedSpace p p.isOpenMap
    ∃ (G : FiniteEtale X), IsIntegral G.obj.left ∧ IsGalois G ∧
      Nat.card (Aut G) = Nat.card (Aut Z) ∧
      ∃ (ρ : Spec (.of A) ⟶ G.obj.left), ρ ≫ G.obj.hom = σ ∧
      ∃ (r : (baseChange πF).obj G ≅ Z)
        (w : Spec (.of F) ⟶ ((baseChange πF).obj G).obj.left),
        w ≫ pullback.fst G.obj.hom πF = sF ≫ ρ ∧ w ≫ r.hom.hom.left = z := by
  let eZ : pullback Z.obj.hom (eX).inv ≅ Z.obj.left :=
    fractionGenericCoverOriginalIso A F p Z
  have heZ : eZ.inv ≫ pullback.snd Z.obj.hom (eX).inv = Z.obj.hom ≫ (eX).hom :=
    fractionGenericCoverOriginalIso_inv_over A F p Z
  let : ConnectedSpace Z.obj.left := Connectedness.connectedSpace_of_categoricalConnected Z
  let : ConnectedSpace (ZN).obj.left :=
    eZ.inv.homeomorph.connectedSpace_iff.mp inferInstance
  let : IsGalois ZN := baseChange_isGalois_of_connected (eX).inv Z
  have hcardN : Nat.card (Aut ZN) = Nat.card (Aut Z) :=
    baseChange_card_aut_of_connected (eX).inv Z
  let zN : Spec (Spec (.of A)).functionField ⟶ pullback Z.obj.hom (eX).inv :=
    (eK).inv ≫ z ≫ eZ.inv
  have hzN : zN ≫ pullback.snd Z.obj.hom (eX).inv ≫ πN = γ ≫ σ := by
    calc
      _ = (eK).inv ≫ z ≫ (eZ.inv ≫ pullback.snd Z.obj.hom (eX).inv) ≫ πN := by
        simp only [zN, Category.assoc]
      _ = (eK).inv ≫ z ≫ (Z.obj.hom ≫ (eX).hom) ≫ πN := by rw [heZ]
      _ = (eK).inv ≫ (z ≫ Z.obj.hom ≫ πF) := by
        simp only [Category.assoc, fractionGenericFiberIso_hom_fst]
      _ = (eK).inv ≫ sF ≫ σ := by rw [hz]
      _ = γ ≫ σ := fractionGenericSpectrumIso_inv_fraction_assoc A F σ
  obtain ⟨G, hGI, hGG, hGc, ρ, hρ, rN, bN, hbN, hbNz⟩ :=
    exists_generic_whole_galoisPointedExtension A p σ hσ N hN hunit ZN
      (hcardN ▸ hcard) zN hzN
  let eN : pullback G.obj.hom πN ≅ pullback Z.obj.hom (eX).inv :=
    (forgetToScheme (pullback p γ)).mapIso rN
  have heN : eN.inv ≫ pullback.snd G.obj.hom πN = pullback.snd Z.obj.hom (eX).inv :=
    Over.w rN.inv.hom
  let kN : pullback Z.obj.hom (eX).inv ⟶ G.obj.left :=
    eN.inv ≫ pullback.fst G.obj.hom πN
  have HN : IsPullback kN (pullback.snd Z.obj.hom (eX).inv) G.obj.hom πN := by
    refine IsPullback.of_iso_pullback ⟨?_⟩ eN.symm rfl heN
    calc
      kN ≫ G.obj.hom = eN.inv ≫ (pullback.fst G.obj.hom πN ≫ G.obj.hom) :=
        Category.assoc _ _ _
      _ = eN.inv ≫ (pullback.snd G.obj.hom πN ≫ πN) :=
        congrArg (fun f : pullback G.obj.hom πN ⟶ X => eN.inv ≫ f)
          (pullback.condition (f := G.obj.hom) (g := πN))
      _ = (eN.inv ≫ pullback.snd G.obj.hom πN) ≫ πN := (Category.assoc _ _ _).symm
      _ = pullback.snd Z.obj.hom (eX).inv ≫ πN :=
        congrArg (fun f : pullback Z.obj.hom (eX).inv ⟶ pullback p γ => f ≫ πN) heN
  let k : Z.obj.left ⟶ G.obj.left := eZ.inv ≫ kN
  have H : IsPullback k Z.obj.hom G.obj.hom πF := by
    apply HN.of_iso' eZ.symm (Iso.refl G.obj.left) eX (Iso.refl X)
    · simp only [k, Iso.symm_hom, Iso.refl_hom, Category.comp_id]
    · exact heZ
    · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    · exact (fractionGenericFiberIso_hom_fst A F p).trans (Category.comp_id πF).symm
  let b : Spec (Spec (.of A)).functionField ⟶ pullback G.obj.hom πN := bN
  have hb : b ≫ pullback.fst G.obj.hom πN = γ ≫ ρ := hbN
  have hbz : b ≫ eN.hom = zN := hbNz
  have hzG : z ≫ k = sF ≫ ρ := by
    have hn : zN ≫ kN = γ ≫ ρ := by
      calc
        _ = (b ≫ eN.hom) ≫ (eN.inv ≫ pullback.fst G.obj.hom πN) :=
          congrArg (fun f : Spec (Spec (.of A)).functionField ⟶
            pullback Z.obj.hom (eX).inv => f ≫ kN) hbz.symm
        _ = b ≫ pullback.fst G.obj.hom πN := by
          simp only [Category.assoc, Iso.hom_inv_id_assoc]
        _ = γ ≫ ρ := hb
    calc
      _ = (eK).hom ≫ (zN ≫ kN) := by
        simp only [zN, k, Category.assoc, Iso.hom_inv_id_assoc]
      _ = (eK).hom ≫ γ ≫ ρ := by rw [hn]
      _ = sF ≫ ρ := fractionGenericSpectrumIso_hom_generic_assoc A F ρ
  let r : (baseChange πF).obj G ≅ Z :=
    ObjectProperty.isoMk _ (Over.isoMk H.isoPullback.symm H.isoPullback_inv_snd)
  let w : Spec (.of F) ⟶ ((baseChange πF).obj G).obj.left := z ≫ H.isoPullback.hom
  refine ⟨G, hGI, hGG, hGc.trans hcardN, ρ, hρ, r, w, ?_, ?_⟩
  · change (z ≫ H.isoPullback.hom) ≫ pullback.fst G.obj.hom πF = sF ≫ ρ
    rw [Category.assoc, H.isoPullback_hom_fst]
    exact hzG
  · change (z ≫ H.isoPullback.hom) ≫ H.isoPullback.inv = z
    rw [Category.assoc, H.isoPullback.hom_inv_id, Category.comp_id]

end AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery
