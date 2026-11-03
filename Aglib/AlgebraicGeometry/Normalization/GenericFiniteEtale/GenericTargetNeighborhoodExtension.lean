/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.GenericLocalWholePointedExtension
public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.BaseLocalizationSection
public import Aglib.AlgebraicGeometry.Spec.PrincipalBaseChangeLimit
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.PointedTargetRefinement

/-! # A generic tame cover gives an actual target neighborhood

The smooth scheme here is the target of the higher direct image in the direct
smooth-base-change proof. The coefficient scheme is not replaced by this
cover. Local whole extension and descent through the original principal
neighborhoods retain the generic reconstruction and the entire local section.
No cohomological zero, finite arithmetic normalization, or Nagata property is
asserted by this construction.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory Opposite

namespace AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery

universe u

variable (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A]
  [IsIntegrallyClosed A] (q : PrimeSpectrum A)
  {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
  (p : X ⟶ Spec (.of A)) [Smooth p] [GeometricallyConnected p]
  (σ : Spec (.of A) ⟶ X) (hσ : σ ≫ p = 𝟙 _)

local notation "L" => Localization.AtPrime q.asIdeal
local notation "l" => Spec.algebraMap A L
local notation "Xq" => pullback p l
local notation "pq" => pullback.snd p l
local notation "σq" => baseLocalizationSection A p q σ hσ
local notation "γ" =>
  Scheme.fromSpecStalk (Spec (CommRingCat.of L)) (genericPoint (Spec (CommRingCat.of L)))
local notation "D" => PrincipalNeighborhoodLimit.schemeDiagram q.asIdeal.primeCompl p
local notation "π" => PrincipalNeighborhoodLimit.baseChangeProjection q.asIdeal.primeCompl L p

/-- The original generic cover over the localized smooth target extends and
then descends to a principal target neighborhood. Both reconstruction squares
and the original marked generic point survive; no arbitrary source-site
cover is substituted for a target refinement. -/
theorem exists_generic_target_neighborhood_extension
    (N : ℕ) (hN : 0 < N) (hunit : IsUnit (N : A))
    (Z : FiniteEtale (pullback pq γ)) [IsGalois Z]
    (a : Spec (Spec (.of L)).functionField ⟶ Z.obj.left)
    (ha : a ≫ Z.obj.hom ≫ pullback.fst pq γ = γ ≫ σq)
    (hcard : Nat.card (Aut Z) ∣ N) :
    ∃ (G : FiniteEtale Xq), IsIntegral G.obj.left ∧ IsGalois G ∧
      Nat.card (Aut G) = Nat.card (Aut Z) ∧
      ∃ (r : Spec (.of L) ⟶ G.obj.left), r ≫ G.obj.hom = σq ∧
        ∃ (e : (baseChange (pullback.fst pq γ)).obj G ≅ Z)
          (b : Spec (Spec (.of L)).functionField ⟶
            ((baseChange (pullback.fst pq γ)).obj G).obj.left),
          b ≫ pullback.fst G.obj.hom (pullback.fst pq γ) = γ ≫ r ∧
          b ≫ e.hom.hom.left = a ∧
          ∃ (s : Finset q.asIdeal.primeCompl) (Gs : FiniteEtale ((D).obj (op s)).left)
            (es : (baseChange (π (op s))).obj Gs ≅ G)
            (d : G.obj.left ⟶ Gs.obj.left),
            d = es.inv.hom.left ≫ pullback.fst Gs.obj.hom (π (op s)) ∧
            IsPullback d G.obj.hom Gs.obj.hom (π (op s)) ∧
            Etale (Gs.obj.hom ≫ ((D).obj (op s)).hom) ∧
            Surjective Gs.obj.hom ∧
            (r ≫ d) ≫ Gs.obj.hom ≫ ((D).obj (op s)).hom = l ≫ σ := by
  let : IsIntegrallyClosed L := isIntegrallyClosed_of_isLocalization L
    q.asIdeal.primeCompl q.asIdeal.primeCompl_le_nonZeroDivisors
  have hunitL : IsUnit (N : L) := by
    simpa only [map_natCast] using hunit.map (algebraMap A L)
  have hσq : σq ≫ pq = 𝟙 _ := baseLocalizationSection_snd A p q σ hσ
  obtain ⟨G, hGI, hGG, hGc, r, hr, e, b, hb, hba⟩ :=
    exists_genericLocal_whole_galoisPointedExtension L pq σq hσq
      N hN hunitL Z hcard a ha
  let c : Cone D :=
    (PrincipalNeighborhoodLimit.schemeCone q.asIdeal.primeCompl L p).extend
      (Over.homMk (U := Over.mk (pullback.fst p l)) (pullbackSymmetry p l).hom
        (pullbackSymmetry_hom_comp_snd p l))
  have hc : IsLimit ((Over.forget X).mapCone c) :=
    PrincipalNeighborhoodLimit.baseChangeConeIsLimit q.asIdeal.primeCompl L p
  let : ∀ {i j} (f : i ⟶ j), IsAffineHom ((D).map f).left := fun {_ _} f =>
    inferInstanceAs (IsAffineHom
      ((PrincipalNeighborhoodLimit.baseChangeDiagram q.asIdeal.primeCompl p).map f))
  let : ∀ i, CompactSpace ((D).obj i).left := fun i =>
    inferInstanceAs (CompactSpace
      ((PrincipalNeighborhoodLimit.baseChangeDiagram q.asIdeal.primeCompl p).obj i))
  let : ∀ i, QuasiSeparatedSpace ((D).obj i).left := fun i =>
    inferInstanceAs (QuasiSeparatedSpace
      ((PrincipalNeighborhoodLimit.baseChangeDiagram q.asIdeal.primeCompl p).obj i))
  let : ∀ i, Etale ((D).obj i).hom := fun i => by
    change Etale (pullback.snd
      (Spec.algebraMap A (IsLocalization.PrincipalDiagram.stage q.asIdeal.primeCompl i.unop)) p)
    infer_instance
  have hmark : r ≫ G.obj.hom ≫ c.pt.hom = l ≫ σ := by
    change r ≫ G.obj.hom ≫ pullback.fst p l = _
    rw [← Category.assoc, hr]
    exact baseLocalizationSection_fst A p q σ hσ
  obtain ⟨i, Gs, es, d, hd, H, hover, het, _⟩ :=
    LimitDescent.exists_pointed_target_etale_refinement_of_limit_cover
      D c hc G r (l ≫ σ) hmark
  have hden : IsLocalization.PrincipalDiagram.denominator q.asIdeal.primeCompl i.unop ≠ 0 :=
    nonZeroDivisors.ne_zero (q.asIdeal.primeCompl_le_nonZeroDivisors
      (IsLocalization.PrincipalDiagram.denominator_mem q.asIdeal.primeCompl i.unop))
  let : IsDomain (IsLocalization.PrincipalDiagram.stage q.asIdeal.primeCompl i.unop) :=
    Localization.Away.isDomain hden
  let : ConnectedSpace ((D).obj i).left := inferInstanceAs (ConnectedSpace
    (pullback (Spec.algebraMap A
      (IsLocalization.PrincipalDiagram.stage q.asIdeal.primeCompl i.unop)) p : Scheme.{u}))
  let : Nonempty Gs.obj.left := ⟨(r ≫ d) (IsLocalRing.closedPoint L)⟩
  have hsurj : Surjective Gs.obj.hom := by
    have hcl : IsClopen (Set.range Gs.obj.hom) :=
      ⟨Gs.obj.hom.isClosedMap.isClosed_range, Gs.obj.hom.isOpenMap.isOpen_range⟩
    exact ⟨Set.range_eq_univ.mp (hcl.eq_univ (Set.range_nonempty _))⟩
  refine ⟨G, hGI, hGG, hGc, r, hr, e, b, hb, hba,
    i.unop, Gs, es, d, hd, H, het, hsurj, ?_⟩
  exact (Category.assoc r d (Gs.obj.hom ≫ ((D).obj i).hom)).trans
    ((congrArg (fun z => r ≫ z) hover).trans hmark)

end AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery
