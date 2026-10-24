/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.Arc
public import Aglib.AlgebraicGeometry.Blowup.RegularPoint.Scheme
public import Aglib.RingTheory.Blowup.ArcTermination.Descent

/-!
# Finite arc iteration on the original point blowups

The exact algebraic iterates are realized by flat preimmersions into successive
ordinary closed-point blowups. The centre pullback, canonical flat comparison,
actual universal arc lifts and stalk scalar/quotient equations are derived.
The proved finite algebraic descent then gives regularity of the same actual
selected scheme stalk. No regularity of a blowup centre is assumed.
-/

open CategoryTheory AlgebraicGeometry
open Localization.Away

@[expose] public noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Blowup.Arc

/-- Equality of actual scheme points induces the native stalk comparison. -/
def pointStalkIso (X : Scheme.{u}) {x y : X} (h : x = y) :
    X.presheaf.stalk x ≅ X.presheaf.stalk y :=
  X.presheaf.stalkCongr (.of_eq h)

/-- Retain an arbitrary original categorical ring arrow in affine pullback. -/
theorem affineCenter_comap_hom {A B : CommRingCat.{u}} (f : A ⟶ B) (I : Ideal A) :
    (affineCenter A I).comap (Spec.map f) = affineCenter B (I.map f.hom) :=
  BaseChange.affineCenter_comap f.hom I

/-- Compose the original affine factorization over fixed scheme objects. -/
theorem spec_comp_factor {P C D : CommRingCat.{u}} {X : Scheme.{u}}
    (φ : P ⟶ C) (f : C ⟶ D) (u : Spec P ⟶ X) (l : Spec C ⟶ X)
    (h : Spec.map φ ≫ u = l) : Spec.map (φ ≫ f) ≫ u = Spec.map f ≫ l := by
  rw [Spec.map_comp, Category.assoc, h]

/-- Flatness and a preimmersion give an isomorphism from the actual selected
scheme stalk to the original local ring. -/
theorem isIso_stalkClosedPointTo
    {C : CommRingCat.{u}} [IsLocalRing C] {X : Scheme.{u}}
    (l : Spec C ⟶ X) [Flat l] [IsPreimmersion l] :
    IsIso (Scheme.stalkClosedPointTo l) := by
  let J : X.presheaf.stalk (l (specClosedPoint C)) ⟶
      (Spec C).presheaf.stalk (specClosedPoint C) := l.stalkMap (specClosedPoint C)
  let E : (Spec C).presheaf.stalk (specClosedPoint C) ≅ C := stalkClosedPointIso C
  let : IsIso J :=
    Scheme.Hom.isIso_stalkMap_of_flat_of_surjectiveOnStalks l _
  change IsIso (J ≫ E.hom)
  infer_instance

/-- The actual closed-point ideal pulls back to the actual maximal ideal.
The proof is independent of regularity of either scheme or point. -/
theorem pointCentre_comap
    {C : Type u} [CommRing C] [IsLocalRing C] {X : Scheme.{u}}
    (l : Spec (.of C) ⟶ X) [Flat l] [IsPreimmersion l]
    (hx : IsClosed ({l (Arc.specClosedPoint (.of C))} : Set X)) :
    (X.fromSpecResidueField (l (Arc.specClosedPoint (.of C)))).ker.comap l =
      affineCenter C (IsLocalRing.maximalIdeal C) := by
  let x : X := l (Arc.specClosedPoint (.of C))
  let φ : X.presheaf.stalk x ⟶ CommRingCat.of C := Scheme.stalkClosedPointTo l
  let : IsIso φ := isIso_stalkClosedPointTo l
  have hsurj : Function.Surjective φ.hom :=
    (ConcreteCategory.bijective_of_isIso φ).2
  have hfac : Spec.map φ ≫ X.fromSpecStalk x = l :=
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk l
  let I := (X.fromSpecResidueField x).ker
  change I.comap l = _
  calc
    I.comap l = I.comap (Spec.map φ ≫ X.fromSpecStalk x) :=
      congrArg (fun g => I.comap g) hfac.symm
    _ = (I.comap (X.fromSpecStalk x)).comap (Spec.map φ) :=
      Scheme.IdealSheafData.comap_comp I _ _
    _ = affineCenter C ((IsLocalRing.maximalIdeal (X.presheaf.stalk x)).map φ.hom) := by
      rw [RegularPoint.pointCentre_comap_fromSpecStalk X x hx,
        affineCenter_comap_hom]
    _ = affineCenter C (IsLocalRing.maximalIdeal C) := by
      rw [IsLocalRing.map_maximalIdeal_of_surjective φ.hom hsurj]

/-- The actual quotient equation with its actual point transport. This is a
consequence of the native local-spectrum equivalence, not an input equation. -/
theorem stalk_quotient_comp
    {C R : CommRingCat.{u}} [IsLocalRing C] [IsLocalRing R] {X : Scheme.{u}}
    (l : Spec C ⟶ X) (f : C ⟶ R) [IsLocalHom f.hom] :
    ∃ hx : (Spec.map f ≫ l) (Arc.specClosedPoint R) = l (Arc.specClosedPoint C),
      Scheme.stalkClosedPointTo (Spec.map f ≫ l) =
        (pointStalkIso X hx).hom ≫
          Scheme.stalkClosedPointTo l ≫ f := by
  let φ : X.presheaf.stalk (l (specClosedPoint C)) ⟶ C := Scheme.stalkClosedPointTo l
  let hφ : IsLocalHom φ.hom := Scheme.isLocalHom_stalkClosedPointTo l
  let k : X.presheaf.stalk (l (Arc.specClosedPoint C)) ⟶ R :=
    φ ≫ f
  have hk : IsLocalHom k.hom := RingHom.isLocalHom_comp f.hom φ.hom
  let η : Σ x, {g : X.presheaf.stalk x ⟶ R // IsLocalHom g.hom} :=
    ⟨l (Arc.specClosedPoint C), k, hk⟩
  let E := SpecToEquivOfLocalRing X R
  let u : Spec (X.presheaf.stalk (l (specClosedPoint C))) ⟶ X :=
    X.fromSpecStalk (l (specClosedPoint C))
  have hφu : Spec.map φ ≫ u = l := Scheme.Spec_stalkClosedPointTo_fromSpecStalk l
  have hη : E.symm η = Spec.map f ≫ l := by
    exact spec_comp_factor φ f u l hφu
  have hpair : E (Spec.map f ≫ l) = η :=
    (congrArg E hη).symm.trans (E.apply_symm_apply η)
  obtain ⟨hx, hq⟩ := SpecToEquivOfLocalRing_eq_iff.mp hpair
  exact ⟨hx, hq⟩

/-- The original stalk arrow with the literal composite-image source fixed. -/
def compositeStalkMap {D : CommRingCat.{u}} [IsLocalRing D] {X Y : Scheme.{u}}
    (n : Spec D ⟶ Y) (b : Y ⟶ X) :
    X.presheaf.stalk ((n ≫ b) (Arc.specClosedPoint D)) ⟶
      Y.presheaf.stalk (n (Arc.specClosedPoint D)) :=
  b.stalkMap (n (Arc.specClosedPoint D))

/-- An actual scalar triangle gives its actual local-ring square, including
the original point transport; no stalk compatibility is a premise. -/
theorem stalk_scalar_of_triangle
    {C D : CommRingCat.{u}} [IsLocalRing C] [IsLocalRing D] {X Y : Scheme.{u}}
    (l : Spec C ⟶ X) (n : Spec D ⟶ Y) (b : Y ⟶ X)
    (c : C ⟶ D) [IsLocalHom c.hom]
    (h : n ≫ b = Spec.map c ≫ l) :
    ∃ hx : (n ≫ b) (Arc.specClosedPoint D) = l (Arc.specClosedPoint C),
      compositeStalkMap n b ≫ Scheme.stalkClosedPointTo n =
        (pointStalkIso X hx).hom ≫
          Scheme.stalkClosedPointTo l ≫ c := by
  let φ : X.presheaf.stalk (l (specClosedPoint C)) ⟶ C := Scheme.stalkClosedPointTo l
  let hφ : IsLocalHom φ.hom := Scheme.isLocalHom_stalkClosedPointTo l
  let k : X.presheaf.stalk (l (Arc.specClosedPoint C)) ⟶ D :=
    φ ≫ c
  have hk : IsLocalHom k.hom := RingHom.isLocalHom_comp c.hom φ.hom
  let η : Σ x, {g : X.presheaf.stalk x ⟶ D // IsLocalHom g.hom} :=
    ⟨l (Arc.specClosedPoint C), k, hk⟩
  let E := SpecToEquivOfLocalRing X D
  let u : Spec (X.presheaf.stalk (l (specClosedPoint C))) ⟶ X :=
    X.fromSpecStalk (l (specClosedPoint C))
  have hφu : Spec.map φ ≫ u = l := Scheme.Spec_stalkClosedPointTo_fromSpecStalk l
  have hη : E.symm η = n ≫ b := by
    exact (spec_comp_factor φ c u l hφu).trans h.symm
  have hpair : E (n ≫ b) = η :=
    (congrArg E hη).symm.trans (E.apply_symm_apply η)
  obtain ⟨hx, hq⟩ := SpecToEquivOfLocalRing_eq_iff.mp hpair
  have hcomp : Scheme.stalkClosedPointTo (n ≫ b) =
      compositeStalkMap n b ≫ Scheme.stalkClosedPointTo n :=
    Scheme.stalkClosedPointTo_comp n b
  exact ⟨hx, hcomp.symm.trans hq⟩

/-- Paste actual scalar and quotient equations before supplying concrete schemes. -/
theorem arc_base_of_scalar
    {C D R : CommRingCat.{u}} {X Y : Scheme.{u}}
    (l : Spec C ⟶ X) (n : Spec D ⟶ Y) (b : Y ⟶ X)
    (c : C ⟶ D) (q : C ⟶ R) (q' : D ⟶ R)
    (hc : n ≫ b = Spec.map c ≫ l) (hq : c ≫ q' = q) :
    (Spec.map q' ≫ n) ≫ b = Spec.map q ≫ l := by
  rw [Category.assoc, hc, ← Category.assoc, ← Spec.map_comp, hq]

/-- Paste the actual comparison and chart triangles over fixed native objects. -/
theorem chart_base_paste {D A B Y C X : Scheme.{u}}
    (q : D ⟶ A) (j : A ⟶ B) (β : B ⟶ Y) (b : Y ⟶ X)
    (u : B ⟶ C) (l : C ⟶ X) (h : D ⟶ C)
    (hβ : β ≫ b = u ≫ l) (hj : q ≫ j ≫ u = h) :
    (q ≫ j ≫ β) ≫ b = h ≫ l := by
  calc
    (q ≫ j ≫ β) ≫ b = q ≫ j ≫ (β ≫ b) := by simp only [Category.assoc]
    _ = q ≫ j ≫ (u ≫ l) := by rw [hβ]
    _ = (q ≫ j ≫ u) ≫ l := by simp only [Category.assoc]
    _ = h ≫ l := by rw [hj]

/-- Compose scalar triangles without rewriting dependent iterate carriers. -/
theorem origin_scalar_paste {C D E : CommRingCat.{u}} {X Y Z : Scheme.{u}}
    (n : Spec D ⟶ Y) (l : Spec C ⟶ X) (π : Y ⟶ X) (ρ : X ⟶ Z)
    (l₀ : Spec E ⟶ Z) (c : C ⟶ D) (a : E ⟶ C) (b : E ⟶ D)
    (hn : n ≫ π = Spec.map c ≫ l) (hl : l ≫ ρ = Spec.map a ≫ l₀)
    (hb : b = a ≫ c) : n ≫ (π ≫ ρ) = Spec.map b ≫ l₀ := by
  rw [← Category.assoc, hn, Category.assoc, hl,
    ← Category.assoc, ← Spec.map_comp, ← hb]

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- The original quotient has fixed native categorical endpoints. -/
def quotientArrow (S : LocalArcState.{u, u} R) :
    CommRingCat.of S.Ring ⟶ CommRingCat.of R := CommRingCat.ofHom S.quotient

/-- The original transition has fixed native categorical endpoints. -/
def scalarArrow (S : LocalArcState.{u, u} R) :
    CommRingCat.of S.Ring ⟶ CommRingCat.of S.next.Ring :=
  CommRingCat.ofHom S.transition

/-- The composite still starts at the original coefficient ring. -/
def iterateScalarArrow (S : LocalArcState.{u, u} R) (n : ℕ) :
    CommRingCat.of S.Ring ⟶ CommRingCat.of (S.iterate n).Ring :=
  CommRingCat.ofHom (S.iterateMap n)

theorem iterateScalarArrow_succ (S : LocalArcState.{u, u} R) (n : ℕ) :
    iterateScalarArrow S (n + 1) = iterateScalarArrow S n ≫ scalarArrow (S.iterate n) :=
  rfl

theorem iterateScalarArrow_quotient (S : LocalArcState.{u, u} R) (n : ℕ) :
    iterateScalarArrow S n ≫ quotientArrow (S.iterate n) = quotientArrow S := by
  apply CommRingCat.hom_ext
  exact S.quotient_comp_iterateMap n

theorem iterateScalarArrow_parameter (S : LocalArcState.{u, u} R) (n : ℕ) :
    (iterateScalarArrow S n).hom S.parameter = (S.iterate n).parameter :=
  S.iterateMap_parameter n

theorem scalar_quotient (S : LocalArcState.{u, u} R) :
    scalarArrow S ≫ quotientArrow S.next = quotientArrow S := by
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  exact S.quotient_transition x

theorem scalarArrow_isLocal (S : LocalArcState.{u, u} R) :
    IsLocalHom (scalarArrow S).hom := by
  let : IsLocalHom S.quotient := IsLocalHom.of_surjective S.quotient S.surjective
  have hcomp : S.next.quotient.comp S.transition = S.quotient := by
    ext x
    exact S.quotient_transition x
  let : IsLocalHom (S.next.quotient.comp S.transition) := by
    rw [hcomp]
    infer_instance
  exact isLocalHom_of_comp S.transition S.next.quotient

/-- These are induction invariants, all derived for the constructed successor.
The closed arc is the composite through the exact algebraic ring, not a chosen
successor or termination premise. -/
structure Realization (S : LocalArcState.{u, u} R) where
  /-- The actual scheme reached by the original point blowups. -/
  X : Scheme.{u}
  /-- The realization map from the literal actual algebraic iterate. -/
  localMap : Spec (.of S.Ring) ⟶ X
  /-- Local Noetherianity is preserved by the actual proper blowdown. -/
  [noetherian : IsLocallyNoetherian X]
  /-- The original local-spectrum realization is flat. -/
  [flat : Flat localMap]
  /-- The realization embeds points and is surjective on the actual stalks. -/
  [preimmersion : IsPreimmersion localMap]
  /-- The original quotient arc remains a closed immersion on this scheme. -/
  [closedArc : IsClosedImmersion (Spec.map (quotientArrow S) ≫ localMap)]

attribute [instance] Realization.noetherian Realization.flat
  Realization.preimmersion Realization.closedArc

namespace Realization

variable {S : LocalArcState.{u, u} R}

/-- The actual arc to the same original DVR at this realization. -/
def arc (G : Realization S) : Spec (.of R) ⟶ G.X :=
  Spec.map (quotientArrow S) ≫ G.localMap

/-- The selected point of the actual original scheme. -/
abbrev point (G : Realization S) : G.X := G.localMap (Arc.specClosedPoint (.of S.Ring))

theorem arc_closedPoint (G : Realization S) :
    G.arc (Arc.specClosedPoint (.of R)) = G.point := by
  let : IsLocalHom (quotientArrow S).hom := IsLocalHom.of_surjective S.quotient S.surjective
  change (Spec.map (quotientArrow S) ≫ G.localMap) (Arc.specClosedPoint (.of R)) = _
  rw [Scheme.Hom.comp_apply]
  exact congrArg G.localMap (Spec_closedPoint (f := quotientArrow S))

theorem point_isClosed (G : Realization S) : IsClosed ({G.point} : Set G.X) := by
  let : IsClosedImmersion G.arc := G.closedArc
  have h := Arc.isClosed_map_point G.arc G.arc.isClosedEmbedding.isClosedMap
    (Arc.specClosedPoint (.of R)) (Arc.isClosed_specClosedPoint (.of R))
  rw [arc_closedPoint] at h
  exact h

/-- The centre is the actual residue-field closed point on the original scheme. -/
def centre (G : Realization S) : G.X.IdealSheafData :=
  (G.X.fromSpecResidueField G.point).ker

theorem centre_comap (G : Realization S) :
    G.centre.comap G.localMap = affineCenter S.Ring (IsLocalRing.maximalIdeal S.Ring) :=
  pointCentre_comap G.localMap G.point_isClosed

/-- An ordinary point blowup is constructed from this actual centre. -/
def nextBlowup (G : Realization S) : BlowupDatum G.centre := blowupDatum G.centre

/-- The exact centre equality constructs the canonical comparison. -/
def comparison (G : Realization S) : (Arc.pointBlowup S.Ring).Y ⟶ G.nextBlowup.Y :=
  BaseChange.map G.localMap G.centre_comap G.nextBlowup (Arc.pointBlowup S.Ring)

theorem comparison_map (G : Realization S) :
    G.comparison ≫ G.nextBlowup.map = (Arc.pointBlowup S.Ring).map ≫ G.localMap :=
  BaseChange.map_triangle G.localMap G.centre_comap _ _

theorem comparison_isPullback (G : Realization S) :
    IsPullback G.comparison (Arc.pointBlowup S.Ring).map G.nextBlowup.map G.localMap :=
  BaseChange.isPullback_of_flat G.localMap inferInstance G.centre_comap _ _

instance comparison_flat (G : Realization S) : Flat G.comparison :=
  MorphismProperty.of_isPullback (P := @Flat) G.comparison_isPullback.flip inferInstance

instance comparison_preimmersion (G : Realization S) : IsPreimmersion G.comparison :=
  MorphismProperty.of_isPullback (P := @IsPreimmersion)
    G.comparison_isPullback.flip inferInstance

instance nextBlowup_proper (G : Realization S) : IsProper G.nextBlowup.map :=
  G.nextBlowup.isProper_of_isLocallyNoetherian

/-- The original prime-localization arrow with the literal next-state target fixed. -/
def nextChartBase (S : LocalArcState.{u, u} R) :
    CommRingCat.of (arcChart S.quotient S.parameter) ⟶ CommRingCat.of S.next.Ring :=
  Arc.chartLocalBase S.quotient S.parameter S.uniformizer.ne_zero

theorem nextChartBase_scalar (S : LocalArcState.{u, u} R) :
    CommRingCat.ofHom (algebraMap S.Ring (arcChart S.quotient S.parameter)) ≫
      nextChartBase S = scalarArrow S := rfl

/-- The literal prime localization of the passed chart is flat. -/
theorem chartLocalization_flat (S : LocalArcState.{u, u} R) :
    Flat (Spec.map (nextChartBase S)) := by
  change Flat (Spec.map (Arc.chartLocalBase S.quotient S.parameter S.uniformizer.ne_zero))
  let D := arcLocalRing S.quotient S.parameter S.uniformizer.ne_zero
  let : Module.Flat (arcChart S.quotient S.parameter) D :=
    IsLocalization.flat D
      (arcClosedPoint S.quotient S.parameter S.uniformizer.ne_zero).primeCompl
  apply Flat.SpecMap_iff.mpr
  exact RingHom.flat_algebraMap_iff.mpr inferInstance

/-- The literal prime localization of the passed chart is a preimmersion. -/
theorem chartLocalization_preimmersion (S : LocalArcState.{u, u} R) :
    IsPreimmersion (Spec.map (nextChartBase S)) := by
  change IsPreimmersion
    (Spec.map (Arc.chartLocalBase S.quotient S.parameter S.uniformizer.ne_zero))
  exact IsPreimmersion.of_isLocalization
    (R := arcChart S.quotient S.parameter)
    (S := arcLocalRing S.quotient S.parameter S.uniformizer.ne_zero)
    (arcClosedPoint S.quotient S.parameter S.uniformizer.ne_zero).primeCompl

/-- The next realization is the original localization, original atlas chart,
and canonical flat comparison, with no chosen isomorphic ring successor. -/
def nextMap (G : Realization S) : Spec (.of S.next.Ring) ⟶ G.nextBlowup.Y :=
  Spec.map (nextChartBase S) ≫
    Arc.chart (Arc.pointBlowup S.Ring) S.quotient S.surjective S.parameter S.uniformizer ≫
      G.comparison

theorem nextMap_scalar (G : Realization S) :
    G.nextMap ≫ G.nextBlowup.map = Spec.map (scalarArrow S) ≫ G.localMap := by
  have hlocal :
      Spec.map (nextChartBase S) ≫
        Arc.chart (Arc.pointBlowup S.Ring) S.quotient S.surjective S.parameter S.uniformizer ≫
          (Arc.pointBlowup S.Ring).map = Spec.map (scalarArrow S) := by
    rw [Arc.chart_map, ← Spec.map_comp, nextChartBase_scalar]
  exact chart_base_paste (Spec.map (nextChartBase S))
    (Arc.chart (Arc.pointBlowup S.Ring) S.quotient S.surjective S.parameter S.uniformizer)
    G.comparison G.nextBlowup.map (Arc.pointBlowup S.Ring).map G.localMap
    (Spec.map (scalarArrow S)) G.comparison_map hlocal

theorem nextArc_map (G : Realization S) :
    (Spec.map (quotientArrow S.next) ≫ G.nextMap) ≫ G.nextBlowup.map = G.arc :=
  arc_base_of_scalar G.localMap G.nextMap G.nextBlowup.map
    (scalarArrow S) (quotientArrow S) (quotientArrow S.next)
    G.nextMap_scalar (scalar_quotient S)

theorem arc_cartier (G : Realization S) : cartierPullback G.centre G.arc := by
  unfold cartierPullback
  rw [arc, Scheme.IdealSheafData.comap_comp, centre_comap]
  exact Arc.cartier_specMap S.quotient S.surjective S.parameter S.uniformizer

/-- All induction invariants are proved for the actual next point blowup. -/
def next (G : Realization S) : Realization S.next where
  X := G.nextBlowup.Y
  localMap := G.nextMap
  noetherian := LocallyOfFiniteType.isLocallyNoetherian G.nextBlowup.map
  flat := by
    let := chartLocalization_flat S
    dsimp only [nextMap]
    infer_instance
  preimmersion := by
    let := chartLocalization_preimmersion S
    dsimp only [nextMap]
    infer_instance
  closedArc := by
    let : IsClosedImmersion
        ((Spec.map (quotientArrow S.next) ≫ G.nextMap) ≫ G.nextBlowup.map) := by
      rw [nextArc_map]
      exact G.closedArc
    exact IsClosedImmersion.of_comp _ G.nextBlowup.map

/-- The actual next arc is the universal lift, with its Cartier hypothesis proved. -/
theorem next_arc_eq_lift (G : Realization S) :
    G.next.arc = G.nextBlowup.lift G.arc G.arc_cartier :=
  G.nextBlowup.hom_ext G.arc_cartier G.nextArc_map
    (G.nextBlowup.lift_map G.arc G.arc_cartier)

/-- The original local-spectrum stalk map with its actual selected point fixed. -/
def localStalkMap (G : Realization S) : G.X.presheaf.stalk G.point ⟶ CommRingCat.of S.Ring :=
  Scheme.stalkClosedPointTo G.localMap

/-- This canonical stalk iso is induced by the original realization map. -/
def stalkIso (G : Realization S) : G.X.presheaf.stalk G.point ≅ CommRingCat.of S.Ring := by
  let : IsIso G.localStalkMap := isIso_stalkClosedPointTo G.localMap
  exact asIso G.localStalkMap

theorem stalkIso_hom (G : Realization S) : G.stalkIso.hom = G.localStalkMap := rfl

theorem stalkIso_quotient (G : Realization S) :
    ∃ hx : G.arc (Arc.specClosedPoint (.of R)) = G.point,
      Scheme.stalkClosedPointTo G.arc =
        (pointStalkIso G.X hx).hom ≫
          G.stalkIso.hom ≫ quotientArrow S := by
  let : IsLocalHom (quotientArrow S).hom := IsLocalHom.of_surjective S.quotient S.surjective
  change ∃ hx : G.arc (specClosedPoint (.of R)) = G.point,
    Scheme.stalkClosedPointTo G.arc = (pointStalkIso G.X hx).hom ≫
      Scheme.stalkClosedPointTo G.localMap ≫ quotientArrow S
  exact stalk_quotient_comp G.localMap (quotientArrow S)

theorem stalkIso_scalar (G : Realization S) :
    ∃ hx : (G.next.localMap ≫ G.nextBlowup.map)
        (Arc.specClosedPoint (.of S.next.Ring)) = G.point,
      compositeStalkMap G.next.localMap G.nextBlowup.map ≫ G.next.stalkIso.hom =
        (pointStalkIso G.X hx).hom ≫
          G.stalkIso.hom ≫ scalarArrow S := by
  let := scalarArrow_isLocal S
  change ∃ hx : (G.next.localMap ≫ G.nextBlowup.map)
      (specClosedPoint (.of S.next.Ring)) = G.point,
    compositeStalkMap G.next.localMap G.nextBlowup.map ≫
      Scheme.stalkClosedPointTo G.next.localMap = (pointStalkIso G.X hx).hom ≫
        Scheme.stalkClosedPointTo G.localMap ≫ scalarArrow S
  exact stalk_scalar_of_triangle G.localMap G.next.localMap G.nextBlowup.map
    (scalarArrow S) G.nextMap_scalar

theorem regular_stalk (G : Realization S) [IsRegularLocalRing S.Ring] :
    IsRegularLocalRing (G.X.presheaf.stalk G.point) :=
  IsRegularLocalRing.of_ringEquiv G.stalkIso.commRingCatIsoToRingEquiv.symm

/-- Geometric iteration is dependent on the already constructed algebraic iterate. -/
def iterate (G : Realization S) : (n : ℕ) → Realization (S.iterate n)
  | 0 => G
  | n + 1 => (G.iterate n).next

/-- Each transition is the actual ordinary blowdown at the preceding actual point. -/
def blowdown (G : Realization S) (n : ℕ) :
    (G.iterate (n + 1)).X ⟶ (G.iterate n).X := (G.iterate n).nextBlowup.map

theorem iterate_arc_map (G : Realization S) (n : ℕ) :
    (G.iterate (n + 1)).arc ≫ G.blowdown n = (G.iterate n).arc :=
  (G.iterate n).nextArc_map

/-- The original selected points, rather than arbitrary chart points, form the chain. -/
theorem iterate_map_point (G : Realization S) (n : ℕ) :
    G.blowdown n (G.iterate (n + 1)).point = (G.iterate n).point := by
  rw [← (G.iterate (n + 1)).arc_closedPoint, ← Scheme.Hom.comp_apply, iterate_arc_map]
  exact (G.iterate n).arc_closedPoint

/-- Original coefficients retain all actual scalar transition arrows. -/
theorem iterate_scalar_map (G : Realization S) (n : ℕ) :
    (G.iterate (n + 1)).localMap ≫ G.blowdown n =
      Spec.map (scalarArrow (S.iterate n)) ≫ (G.iterate n).localMap :=
  (G.iterate n).nextMap_scalar

/-- The composite uses the original scheme blowdowns. -/
def originMap (G : Realization S) : (n : ℕ) → (G.iterate n).X ⟶ G.X
  | 0 => 𝟙 G.X
  | n + 1 => G.blowdown n ≫ G.originMap n

theorem iterate_local_originMap (G : Realization S) (n : ℕ) :
    (G.iterate n).localMap ≫ G.originMap n = Spec.map (iterateScalarArrow S n) ≫ G.localMap := by
  induction n with
  | zero =>
    change G.localMap ≫ 𝟙 G.X = Spec.map (𝟙 (CommRingCat.of S.Ring)) ≫ G.localMap
    simp
  | succ n ih =>
    exact origin_scalar_paste (G.iterate (n + 1)).localMap (G.iterate n).localMap
      (G.blowdown n) (G.originMap n) G.localMap (scalarArrow (S.iterate n))
      (iterateScalarArrow S n) (iterateScalarArrow S (n + 1))
      (G.iterate_scalar_map n) ih (iterateScalarArrow_succ S n)

theorem iterate_arc_originMap (G : Realization S) (n : ℕ) :
    (G.iterate n).arc ≫ G.originMap n = G.arc := by
  induction n with
  | zero => exact Category.comp_id _
  | succ n ih =>
    change (G.iterate (n + 1)).arc ≫ G.blowdown n ≫ G.originMap n = G.arc
    rw [← Category.assoc, iterate_arc_map, ih]

/-- The only termination input is the passed actual strict algebraic descent. -/
theorem exists_regular_iterate (G : Realization S) :
    ∃ n : ℕ, IsRegularLocalRing ((G.iterate n).X.presheaf.stalk (G.iterate n).point) := by
  obtain ⟨n, hn⟩ := LocalArcState.exists_regular_iterate S
  let := hn
  exact ⟨n, (G.iterate n).regular_stalk⟩

end Realization

/-- The original source spectrum has the required realization invariants. -/
def initial (S : LocalArcState.{u, u} R) : Realization S where
  X := Spec (.of S.Ring)
  localMap := 𝟙 _
  noetherian := inferInstance
  flat := inferInstance
  preimmersion := inferInstance
  closedArc := by
    simpa only [Category.comp_id] using
      (IsClosedImmersion.spec_of_surjective (quotientArrow S) S.surjective)

/-- The original source spectrum has its original quotient arc. -/
theorem initial_arc (S : LocalArcState.{u, u} R) :
    (initial S).arc = Spec.map (quotientArrow S) := Category.comp_id _

attribute [local instance] RingHom.ker_isPrime

/-- The original two-dimensional regular-generic surface data reach a regular
stalk after finitely many of the constructed original closed-point blowups.
The original surjection, quotient DVR, parameter and actual centres are retained. -/
theorem exists_regular_point_iterate_of_regular_surface
    {C : Type u} [CommRing C] [IsLocalRing C] [IsNoetherianRing C] [IsDomain C]
    (f : C →+* R) (hf : Function.Surjective f) (t : C) (ht : Irreducible (f t))
    (hd : ringKrullDim C = 2)
    [IsRegularLocalRing (Localization.AtPrime (RingHom.ker f))] :
    let S := LocalArcState.ofRegularGenericSurface f hf t ht hd
    ∃ n : ℕ, IsRegularLocalRing
      (((initial S).iterate n).X.presheaf.stalk (((initial S).iterate n).point)) :=
  Realization.exists_regular_iterate
    (initial (LocalArcState.ofRegularGenericSurface f hf t ht hd))

end AlgebraicGeometry.Scheme.Blowup.Arc
