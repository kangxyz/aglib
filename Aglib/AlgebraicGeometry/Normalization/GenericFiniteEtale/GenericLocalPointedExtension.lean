/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.GenericBaseOpenGalois
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.RestrictSquareComparison
public import
  Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.SmoothLocalGaloisPointedExtension

/-! # Original generic pointed Galois covers near the local section

The original generic cover spreads to a base open and its single original
normalization extends near the entire local section. The final reconstruction
is only over the inverse image of that target neighborhood in the generic
fibre; no whole-generic-fibre containment is asserted.
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

local instance genericLocal_connected :
    ConnectedSpace (pullback p
      ((Spec (.of A)).fromSpecStalk (genericPoint (Spec (.of A)))) : Scheme.{u}) := by
  let : Subsingleton (Spec ((Spec (.of A)).presheaf.stalk
      (genericPoint (Spec (.of A))))) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum (Spec (.of A)).functionField))
  exact GeometricallyConnected.connectedSpace_of_subsingleton (pullback.snd p _)

/-- A prescribed original generic Galois cover of invertible bounded order
extends near the whole section, with its exact restricted reconstruction
and original generic point. -/
theorem exists_genericLocal_galoisPointedExtension
    (s : Spec (.of A) ⟶ X) (hs : s ≫ p = 𝟙 _)
    (N : ℕ) (hN : 0 < N) (hunit : IsUnit (N : A))
    (Y : FiniteEtale (pullback p
      ((Spec (.of A)).fromSpecStalk (genericPoint (Spec (.of A)))))) [IsGalois Y]
    (hcard : Nat.card (Aut Y) ∣ N)
    (a : Spec (Spec (.of A)).functionField ⟶ Y.obj.left)
    (ha : a ≫ Y.obj.hom ≫ pullback.fst p _ =
      (Spec (.of A)).fromSpecStalk (genericPoint (Spec (.of A))) ≫ s) :
    ∃ (V : X.Opens) (hV : Set.range s ⊆ V) (G : FiniteEtale V),
      let : GeometricallyIntegral p :=
        geometricallyIntegral_of_smooth_of_geometricallyConnected p
      let : IsIntegral X := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian p
      let : Nonempty V := ⟨⟨s (IsLocalRing.closedPoint A), hV ⟨_, rfl⟩⟩⟩
      let : IsIntegral V := isIntegral_of_isOpenImmersion V.ι
      IsGalois G ∧ Nat.card (Aut G) = Nat.card (Aut Y) ∧
      ∃ (sV : Spec (.of A) ⟶ V) (lV : Spec (.of A) ⟶ G.obj.left),
        sV ≫ V.ι = s ∧ lV ≫ G.obj.hom = sV ∧
        ∃ e : (baseChange ((pullback.fst p _) ∣_ V)).obj G ≅
            (baseChange ((pullback.fst p _) ⁻¹ᵁ V).ι).obj Y,
          ∃ b : Spec (Spec (.of A)).functionField ⟶
              ((baseChange ((pullback.fst p _) ∣_ V)).obj G).obj.left,
            b ≫ pullback.fst G.obj.hom ((pullback.fst p _) ∣_ V) =
              (Spec (.of A)).fromSpecStalk (genericPoint (Spec (.of A))) ≫ lV ∧
            b ≫ e.hom.hom.left ≫ pullback.fst Y.obj.hom
              ((pullback.fst p _) ⁻¹ᵁ V).ι = a := by
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
  obtain ⟨V, hV, hEt, hVG, hVc, sV, lV, hsV, hlV, hgeneric⟩ :=
    exists_smoothLocal_galoisPointedExtension A p s hs W j hj N hN hunit
      E hEcard aW haWbase
  let : Nonempty V := ⟨⟨s (IsLocalRing.closedPoint A), hV ⟨_, rfl⟩⟩⟩
  let : IsIntegral V := isIntegral_of_isOpenImmersion V.ι
  let f := (genericMap j E.obj.hom).fromNormalization
  let : IsFinite f := fromNormalization_isFinite j E.obj.hom
  let : Etale (f ∣_ V) := hEt
  let G := restrictedNormalizationCover j E V
  let : IsGalois G := hVG
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
  obtain ⟨eV, heV⟩ := exists_restrictSquare_comparison f π Y k Hk V
  let Vη : B.Opens := π ⁻¹ᵁ V
  have harange : Set.range (a ≫ Y.obj.hom) ⊆ Set.range Vη.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    change π ((a ≫ Y.obj.hom) x) ∈ V
    rw [← Scheme.Hom.comp_apply, Category.assoc, ha]
    exact hV ⟨γ x, rfl⟩
  let r := IsOpenImmersion.lift Vη.ι (a ≫ Y.obj.hom) harange
  have hr : r ≫ Vη.ι = a ≫ Y.obj.hom := IsOpenImmersion.lift_fac ..
  let aV : Spec (Spec (.of A)).functionField ⟶ ((baseChange Vη.ι).obj Y).obj.left :=
    pullback.lift a r hr.symm
  let πY : ((baseChange Vη.ι).obj Y).obj.left ⟶ Y.obj.left :=
    pullback.fst Y.obj.hom Vη.ι
  have haV : aV ≫ πY = a := pullback.lift_fst a r hr.symm
  have heVV : eV.inv.hom.left ≫ eV.hom.hom.left =
      𝟙 (((baseChange Vη.ι).obj Y).obj.left) :=
    ((forgetToScheme Vη).mapIso eV).inv_hom_id
  have hat : a ≫ t = aW := haW.symm
  let b := aV ≫ eV.inv.hom.left
  refine ⟨V, hV, G, hVG, hVc.trans hc, sV, lV, hsV, hlV, eV, b, ?_, ?_⟩
  · apply (cancel_mono (f ⁻¹ᵁ V).ι).mp
    change (aV ≫ eV.inv.hom.left ≫ pullback.fst (f ∣_ V) (π ∣_ V)) ≫
      (f ⁻¹ᵁ V).ι = (γ ≫ lV) ≫ (f ⁻¹ᵁ V).ι
    rw [Category.assoc, Category.assoc, heV]
    change aV ≫ πY ≫ k = _
    rw [← Category.assoc, haV]
    change a ≫ t ≫ inclusion j E.obj.hom = _
    rw [← Category.assoc, hat]
    exact hgeneric.symm
  · change (aV ≫ eV.inv.hom.left) ≫ eV.hom.hom.left ≫ πY = a
    rw [Category.assoc, ← Category.assoc eV.inv.hom.left, heVV,
      Category.id_comp]
    exact haV

end AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery
