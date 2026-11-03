/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.LocalizedGenericFiber
public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.GenericTargetNeighborhoodExtension
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.GaloisBaseChange

/-! # Marked original fraction-field covers give target neighborhoods

The full original fibre point, not just its ambient projection, is transported
through the canonical localized generic-fibre isomorphism. The local whole
extension and its principal descent remain the same constructions. No zero
class or arithmetic normalization is supplied by this geometric consumer.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory Opposite

namespace AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery

universe u

variable (A F : Type u) [CommRing A] [IsDomain A] [Field F]
  [Algebra A F] [IsFractionRing A F] (q : PrimeSpectrum A)
  {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of A))
  (σ : Spec (CommRingCat.of A) ⟶ X) (hσ : σ ≫ p = 𝟙 _)

local notation "L" => Localization.AtPrime q.asIdeal
local notation "l" => Spec.algebraMap A L
local notation "s" => Spec.algebraMap A F
local notation "pq" => pullback.snd p l
local notation "γ" =>
  Scheme.fromSpecStalk (Spec (CommRingCat.of L)) (genericPoint (Spec (CommRingCat.of L)))
local notation "eK" => localizedGenericSpectrumIso A F q
local notation "eX" => localizedGenericFiberIso A F q p
local notation "σq" => baseLocalizationSection A p q σ hσ

/-- The original fraction-field point of the whole section. -/
def fractionSectionPoint : Spec (CommRingCat.of F) ⟶ pullback p s :=
  pullback.lift (s ≫ σ) (𝟙 _) (by simp [Category.assoc, hσ])

omit [IsDomain A] [IsFractionRing A F] in
@[reassoc (attr := simp)] theorem fractionSectionPoint_fst :
    fractionSectionPoint A F p σ hσ ≫ pullback.fst p s = s ≫ σ :=
  pullback.lift_fst ..

omit [IsDomain A] [IsFractionRing A F] in
@[reassoc (attr := simp)] theorem fractionSectionPoint_snd :
    fractionSectionPoint A F p σ hσ ≫ pullback.snd p s = 𝟙 _ :=
  pullback.lift_snd ..

/-- The full transported point has the prescribed native local section. -/
private theorem transportedPoint_fst :
    (eK).inv ≫ fractionSectionPoint A F p σ hσ ≫ (eX).hom ≫ pullback.fst pq γ =
      γ ≫ σq := by
  apply pullback.hom_ext
  · simp only [Category.assoc, localizedGenericFiberIso_hom_fst,
      fractionSectionPoint_fst, baseLocalizationSection_fst]
    have h := localizedFraction_base_triangle A F q
    have hg := localizedGenericSpectrumIso_hom_generic A F q
    rw [← h, ← hg]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  · rw [Category.assoc, Category.assoc, Category.assoc,
      pullback.condition, ← Category.assoc (eX).hom,
      localizedGenericFiberIso_hom_snd]
    simp only [Category.assoc, fractionSectionPoint_snd_assoc,
      Iso.inv_hom_id_assoc, baseLocalizationSection_snd, Category.comp_id]

/-- The actual original marked cover, pulled back to the native generic fibre. -/
def nativeFractionCover (Z : FiniteEtale (pullback p s)) : FiniteEtale (pullback pq γ) :=
  (baseChange (eX).inv).obj Z

/-- Transport the full original fibre lift without choosing another marking. -/
def nativeFractionCoverPoint (Z : FiniteEtale (pullback p s))
    (z : Fiber (fractionSectionPoint A F p σ hσ) Z) :
    Spec (Spec (CommRingCat.of L)).functionField ⟶
      (nativeFractionCover A F q p Z).obj.left :=
  pullback.lift (f := Z.obj.hom) (g := (eX).inv) ((eK).inv ≫ z.left)
    ((eK).inv ≫ fractionSectionPoint A F p σ hσ ≫ (eX).hom) (by
      have hz : z.left ≫ Z.obj.hom = fractionSectionPoint A F p σ hσ := Over.w z
      calc
        ((eK).inv ≫ z.left) ≫ Z.obj.hom =
            (eK).inv ≫ fractionSectionPoint A F p σ hσ :=
          (Category.assoc ..).trans (congrArg (fun k => (eK).inv ≫ k) hz)
        _ = ((eK).inv ≫ fractionSectionPoint A F p σ hσ ≫ (eX).hom) ≫ (eX).inv := by
          simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id])

/-- The transported point still projects to the original specified lift. -/
@[reassoc] theorem nativeFractionCoverPoint_original (Z : FiniteEtale (pullback p s))
    (z : Fiber (fractionSectionPoint A F p σ hσ) Z) :
    nativeFractionCoverPoint A F q p σ hσ Z z ≫ pullback.fst Z.obj.hom (eX).inv =
      (eK).inv ≫ z.left := pullback.lift_fst ..

/-- The exact marked triangle required by whole local target extension. -/
theorem nativeFractionCoverPoint_section (Z : FiniteEtale (pullback p s))
    (z : Fiber (fractionSectionPoint A F p σ hσ) Z) :
    nativeFractionCoverPoint A F q p σ hσ Z z ≫
        (nativeFractionCover A F q p Z).obj.hom ≫ pullback.fst pq γ = γ ≫ σq := by
  have hs : nativeFractionCoverPoint A F q p σ hσ Z z ≫
      (nativeFractionCover A F q p Z).obj.hom =
      (eK).inv ≫ fractionSectionPoint A F p σ hσ ≫ (eX).hom :=
    pullback.lift_snd ..
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun v => v ≫ pullback.fst pq γ) hs).trans
      (by simpa only [Category.assoc] using transportedPoint_fst A F q p σ hσ))

/-- Returning a native reconstructed cover to the original fibre retains the
specified original generic cover, using only composition and identity. -/
def originalFractionCoverReconstruction (G : FiniteEtale (pullback p l))
    (Z : FiniteEtale (pullback p s))
    (r : (baseChange (pullback.fst pq γ)).obj G ≅ nativeFractionCover A F q p Z) :
    (baseChange ((eX).hom ≫ pullback.fst pq γ)).obj G ≅ Z :=
  (baseChangeComp (pullback.fst pq γ) (eX).hom).app G ≪≫
    (baseChange (eX).hom).mapIso r ≪≫
    (baseChangeComp (eX).inv (eX).hom).symm.app Z ≪≫
    eqToIso (congrArg (fun v => (baseChange v).obj Z) (eX).hom_inv_id) ≪≫
    (baseChangeId _).app Z

variable [IsNoetherianRing A] [IsIntegrallyClosed A]
  [CompactSpace X] [QuasiSeparatedSpace X] [Smooth p] [GeometricallyConnected p]

local notation "D" => PrincipalNeighborhoodLimit.schemeDiagram q.asIdeal.primeCompl p
local notation "π" => PrincipalNeighborhoodLimit.baseChangeProjection q.asIdeal.primeCompl L p

/-- A tame, fully marked cover of the original fraction-field fibre yields an
actual surjective étale target neighborhood and the original reconstruction.
The native marking retained in the conclusion has the exact original-point
projection `nativeFractionCoverPoint_original`. -/
theorem exists_marked_fraction_target_extension (N : ℕ) (hN : 0 < N)
    (hunit : IsUnit (N : A)) (Z : FiniteEtale (pullback p s)) [IsGalois Z]
    (z : Fiber (fractionSectionPoint A F p σ hσ) Z)
    (hcard : Nat.card (Aut Z) ∣ N) :
    ∃ (G : FiniteEtale (pullback p l)), IsIntegral G.obj.left ∧ IsGalois G ∧
      Nat.card (Aut G) = Nat.card (Aut Z) ∧
      ∃ (r : Spec (CommRingCat.of L) ⟶ G.obj.left), r ≫ G.obj.hom = σq ∧
        ∃ (rN : (baseChange (pullback.fst pq γ)).obj G ≅ nativeFractionCover A F q p Z)
          (b : Spec (Spec (CommRingCat.of L)).functionField ⟶
            ((baseChange (pullback.fst pq γ)).obj G).obj.left),
          b ≫ pullback.fst G.obj.hom (pullback.fst pq γ) = γ ≫ r ∧
          b ≫ rN.hom.hom.left = nativeFractionCoverPoint A F q p σ hσ Z z ∧
          Nonempty ((baseChange ((eX).hom ≫ pullback.fst pq γ)).obj G ≅ Z) ∧
          ∃ (t : Finset q.asIdeal.primeCompl) (Gs : FiniteEtale ((D).obj (op t)).left)
            (es : (baseChange (π (op t))).obj Gs ≅ G)
            (d : G.obj.left ⟶ Gs.obj.left),
            d = es.inv.hom.left ≫ pullback.fst Gs.obj.hom (π (op t)) ∧
            IsPullback d G.obj.hom Gs.obj.hom (π (op t)) ∧
            Etale (Gs.obj.hom ≫ ((D).obj (op t)).hom) ∧ Surjective Gs.obj.hom ∧
            (r ≫ d) ≫ Gs.obj.hom ≫ ((D).obj (op t)).hom = l ≫ σ := by
  let : ConnectedSpace (pullback p s : Scheme.{u}) :=
    GeometricallyConnected.connectedSpace_of_subsingleton (pullback.snd p s)
  let : ConnectedSpace (pullback pq γ : Scheme.{u}) :=
    (eX).hom.homeomorph.connectedSpace_iff.mp inferInstance
  let : ConnectedSpace Z.obj.left := Connectedness.connectedSpace_of_categoricalConnected Z
  let : ConnectedSpace ((baseChange (eX).inv).obj Z).obj.left :=
    (asIso (pullback.fst Z.obj.hom (eX).inv)).inv.homeomorph.connectedSpace_iff.mp inferInstance
  let : IsGalois (nativeFractionCover A F q p Z) :=
    baseChange_isGalois_of_connected (eX).inv Z
  have hc : Nat.card (Aut (nativeFractionCover A F q p Z)) = Nat.card (Aut Z) :=
    baseChange_card_aut_of_connected (eX).inv Z
  obtain ⟨G, hGI, hGG, hGc, r, hr, rN, b, hb, hba, t, Gs, es, d, hd, H, het, hsurj, hmark⟩ :=
    exists_generic_target_neighborhood_extension A q p σ hσ N hN hunit
      (nativeFractionCover A F q p Z) (nativeFractionCoverPoint A F q p σ hσ Z z)
      (nativeFractionCoverPoint_section A F q p σ hσ Z z)
      (by simpa only [hc] using hcard)
  exact ⟨G, hGI, hGG, hGc.trans hc, r, hr, rN, b, hb, hba,
    ⟨originalFractionCoverReconstruction A F q p G Z rN⟩,
    t, Gs, es, d, hd, H, het, hsurj, hmark⟩

end AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery
