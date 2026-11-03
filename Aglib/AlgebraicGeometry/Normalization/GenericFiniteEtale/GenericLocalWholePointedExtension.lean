/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.GenericBaseOpenGalois
public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.GaloisExtension
public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.SmoothLocalWholePurity
public import Aglib.AlgebraicGeometry.Stalk.GenericSection

/-! # The original generic pointed cover extends over the whole target

The single original normalization is equipped with its proved finite-etale
property. Its complete generic-fibre reconstruction retains the original
point and the original lifted-section triangle. No target-neighborhood
restriction or second cover model is introduced.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery

universe u

variable (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A]
  [IsNoetherianRing A] [IsIntegrallyClosed A]
  {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
  (p : X ⟶ Spec (.of A)) [Smooth p] [GeometricallyConnected p]

local instance genericWhole_generic_connected :
    ConnectedSpace (pullback p
      ((Spec (.of A)).fromSpecStalk (genericPoint (Spec (.of A)))) : Scheme.{u}) := by
  let : Subsingleton (Spec ((Spec (.of A)).presheaf.stalk
      (genericPoint (Spec (.of A))))) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum (Spec (.of A)).functionField))
  exact GeometricallyConnected.connectedSpace_of_subsingleton (pullback.snd p _)

/-- The prescribed original generic Galois cover extends to the entire smooth
target, with unchanged deck order, complete generic reconstruction and the
same original generic point. The base remains normal Noetherian local. -/
theorem exists_genericLocal_whole_galoisPointedExtension
    (s : Spec (.of A) ⟶ X) (hs : s ≫ p = 𝟙 _)
    (N : ℕ) (hN : 0 < N) (hunit : IsUnit (N : A))
    (Y : FiniteEtale (pullback p
      ((Spec (.of A)).fromSpecStalk (genericPoint (Spec (.of A)))))) [IsGalois Y]
    (hcard : Nat.card (Aut Y) ∣ N)
    (a : Spec (Spec (.of A)).functionField ⟶ Y.obj.left)
    (ha : a ≫ Y.obj.hom ≫ pullback.fst p _ =
      (Spec (.of A)).fromSpecStalk (genericPoint (Spec (.of A))) ≫ s) :
    letI : ConnectedSpace X := GeometricallyConnected.connectedSpace p p.isOpenMap
    ∃ G : FiniteEtale X, IsIntegral G.obj.left ∧ IsGalois G ∧
      Nat.card (Aut G) = Nat.card (Aut Y) ∧
      ∃ l : Spec (.of A) ⟶ G.obj.left, l ≫ G.obj.hom = s ∧
        ∃ e : (baseChange (pullback.fst p _)).obj G ≅ Y,
          ∃ b : Spec (Spec (.of A)).functionField ⟶
              ((baseChange (pullback.fst p _)).obj G).obj.left,
            b ≫ pullback.fst G.obj.hom (pullback.fst p _) =
              (Spec (.of A)).fromSpecStalk (genericPoint (Spec (.of A))) ≫ l ∧
            b ≫ e.hom.hom.left = a := by
  classical
  let γ := (Spec (.of A)).fromSpecStalk (genericPoint (Spec (.of A)))
  let B : Scheme.{u} := pullback p γ
  let π : B ⟶ X := pullback.fst p γ
  let : GeometricallyIntegral p := geometricallyIntegral_of_smooth_of_geometricallyConnected p
  let : IsIntegral X := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian p
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let (x : X) : IsIntegrallyClosed (X.presheaf.stalk x) :=
    (normalStalks_of_smooth_normalBase A p x).2
  obtain ⟨W, hW, E, g, hg, hI, hG, hc, e, aW, haW, haWbase⟩ :=
    LimitDescent.exists_generic_baseOpen_galois_point A p s Y a ha
  let := hW
  let U := p ⁻¹ᵁ W
  let j : U.toScheme ⟶ X := U.ι
  have hj : Set.range j = p ⁻¹' (W : Set (Spec (.of A))) := Scheme.Opens.range_ι U
  let : Nonempty U := section_baseOpen_nonempty p s hs W j hj
  let : IsIntegral U := isIntegral_of_isOpenImmersion j
  let := hI
  let := hG
  have hEcard : Nat.card (Aut E) ∣ N := hc ▸ hcard
  let f := (genericMap j E.obj.hom).fromNormalization
  let : IsFinite f := fromNormalization_isFinite j E.obj.hom
  have hnormal : NormalStalks (Spec (.of A)) := fun x =>
    ⟨(isIntegrallyClosed_and_isDomain_stalk_Spec A x).2,
      (isIntegrallyClosed_and_isDomain_stalk_Spec A x).1⟩
  have hgeneric : (aW ≫ inclusion j E.obj.hom) ≫ f = γ ≫ s := by
    rw [Category.assoc, inclusion_over]
    exact haWbase
  obtain ⟨l, hl, _⟩ := existsUnique_integralGenericLift
    (Spec (.of A)) hnormal s f (aW ≫ inclusion j E.obj.hom) hgeneric
  let : Etale f := etale_normalization_of_smooth_local_baseOpen_section
    A p s hs W j hj N hN hunit E hEcard l hl.1
  let G := normalizationFiniteEtale j E
  have hGI : IsIntegral G.obj.left := normalizationFiniteEtale_isIntegral j E
  have hGG : IsGalois G := normalizationFiniteEtale_isGalois j E
  have hGc : Nat.card (Aut G) = Nat.card (Aut Y) :=
    (normalizationFiniteEtale_card_aut j E).trans hc
  let t : Y.obj.left ⟶ E.obj.left := e.inv.hom.left ≫ pullback.fst E.obj.hom g
  have heover : e.inv.hom.left ≫ pullback.snd E.obj.hom g = Y.obj.hom :=
    Over.w e.inv.hom
  have Ht : IsPullback t Y.obj.hom E.obj.hom g := by
    refine IsPullback.of_iso_pullback ⟨?_⟩ ((forgetToScheme B).mapIso e.symm) rfl ?_
    · dsimp only [t]
      rw [Category.assoc, pullback.condition, ← Category.assoc, heover]
    · exact heover
  let k : Y.obj.left ⟶ (genericMap j E.obj.hom).normalization :=
    t ≫ inclusion j E.obj.hom
  have Hk : IsPullback k Y.obj.hom f π := by
    have H := Ht.paste_horiz (isPullback j E.obj.hom)
    change IsPullback k Y.obj.hom f (g ≫ j) at H
    have hg' : g ≫ j = π := hg
    rw [hg'] at H
    exact H
  let eG : (baseChange π).obj G ≅ Y :=
    ObjectProperty.isoMk _ (Over.isoMk Hk.isoPullback.symm Hk.isoPullback_inv_snd)
  let b : Spec (Spec (.of A)).functionField ⟶ ((baseChange π).obj G).obj.left :=
    a ≫ Hk.isoPullback.hom
  refine ⟨G, hGI, hGG, hGc, l, hl.1, eG, b, ?_, ?_⟩
  · change (a ≫ Hk.isoPullback.hom) ≫ pullback.fst f π = γ ≫ l
    rw [Category.assoc, Hk.isoPullback_hom_fst]
    change a ≫ t ≫ inclusion j E.obj.hom = γ ≫ l
    have hat : a ≫ t = aW := haW.symm
    rw [← Category.assoc, hat]
    exact hl.2.symm
  · change (a ≫ Hk.isoPullback.hom) ≫ Hk.isoPullback.inv = a
    rw [Category.assoc, Hk.isoPullback.hom_inv_id, Category.comp_id]

end AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery
