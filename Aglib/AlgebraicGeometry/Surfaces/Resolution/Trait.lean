/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.Resolution.Principalization
public import Aglib.AlgebraicGeometry.Surfaces.Birational.TraitGraph

/-!
# The original generic fibre of an actual point-blowup chain

A closed point of a proper scheme over a DVR lies over the trait's closed
point. Its actual centre ideal therefore pulls back to the unit ideal on
the original literal generic fibre. The existing off-centre blowup
isomorphism proves that the original generic map of each point blowup is
an isomorphism. Induction gives this property for the supplied finite
`PointBlowupChain`, with its original map and structural triangles.
Regularity, integrality and flatness of the model are not assumed.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits TopologicalSpace
open AlgebraicGeometry.Scheme.LocalRing.GenericFiber (baseMap)

universe u

namespace AlgebraicGeometry.Scheme.Blowup

variable (R F : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field F] [Algebra R F] [IsFractionRing R F]

/-- The original proper structural map sends every actual closed point
to the closed point of the original trait. -/
theorem closedPoint_image_eq_closedPoint {X : Scheme.{u}}
    (p : X ⟶ Spec (.of R)) [IsProper p] (x : X) (hx : IsClosed ({x} : Set X)) :
    p x = IsLocalRing.closedPoint R := by
  have himage : IsClosed ({p x} : Set (Spec (.of R))) := by
    simpa only [Set.image_singleton] using p.isClosedMap {x} hx
  apply PrimeSpectrum.ext
  exact IsLocalRing.eq_maximalIdeal
    ((PrimeSpectrum.isClosed_singleton_iff_isMaximal (p x)).mp himage)

private theorem baseMap_ne_closedPoint (z : Spec (.of F)) :
    baseMap R F z ≠ IsLocalRing.closedPoint R := by
  intro he
  rw [Subsingleton.elim z (IsLocalRing.closedPoint F),
    LocalRing.GenericFiber.baseMap_closedPoint_eq_genericPoint,
    genericPoint_eq_bot_of_affine] at he
  exact (IsDiscreteValuationRing.not_a_field R)
    (congrArg PrimeSpectrum.asIdeal he.symm)

/-- The ideal of the original closed point becomes the unit ideal on the
literal generic fibre of the original proper model. -/
theorem pointCentre_generic_comap_eq_top {X : Scheme.{u}}
    (p : X ⟶ Spec (.of R)) [IsProper p] (x : X) (hx : IsClosed ({x} : Set X)) :
    (X.fromSpecResidueField x).ker.comap (pullback.fst p (baseMap R F)) = ⊤ := by
  have : IsClosedImmersion (X.fromSpecResidueField x) :=
    isClosed_singleton_iff_isClosedImmersion.mp hx
  have hnot (y : pullback (C := Scheme.{u}) p (baseMap R F)) :
      pullback.fst p (baseMap R F) y ≠ x := by
    intro heq
    have he := congrArg
      (fun m : pullback (C := Scheme.{u}) p (baseMap R F) ⟶ Spec (.of R) => m y)
      (pullback.condition (f := p) (g := baseMap R F))
    change p (pullback.fst p (baseMap R F) y) =
      baseMap R F (pullback.snd p (baseMap R F) y) at he
    rw [heq, closedPoint_image_eq_closedPoint R p x hx] at he
    exact baseMap_ne_closedPoint R F (pullback.snd p (baseMap R F) y) he.symm
  apply (IdealSheafData.support_eq_bot_iff _).mp
  rw [IdealSheafData.support_comap]
  ext y
  change (pullback.fst p (baseMap R F) y ∈
    ((X.fromSpecResidueField x).ker.support : Set X)) ↔ False
  rw [Scheme.Hom.support_ker, Scheme.range_fromSpecResidueField, hx.closure_eq]
  exact iff_false_intro (hnot y)

private theorem overPullbackMap_isPullback {S T X Y : Scheme.{u}}
    (b : T ⟶ S) (p : X ⟶ S) (f : Y ⟶ X) :
    IsPullback
      ((Over.pullback b).map (Over.homMk f rfl : Over.mk (f ≫ p) ⟶ Over.mk p)).left
      (pullback.fst (f ≫ p) b) (pullback.fst p b) f := by
  refine IsPullback.of_right (h₁₂ := pullback.snd p b) ?_ ?_
    (IsPullback.of_hasPullback p b).flip
  · simpa [Over.pullback_map_left] using (IsPullback.of_hasPullback (f ≫ p) b).flip
  · simp [Over.pullback_map_left]

private theorem blowup_overPullbackMap_isIso_of_comap_eq_top
    {S T X : Scheme.{u}} (b : T ⟶ S) (p : X ⟶ S)
    {I : X.IdealSheafData} (B : BlowupDatum I)
    (hI : I.comap (pullback.fst p b) = ⊤) :
    IsIso ((Over.pullback b).map
      (Over.homMk B.map rfl : Over.mk (B.map ≫ p) ⟶ Over.mk p)) := by
  let m := (Over.pullback b).map
    (Over.homMk B.map rfl : Over.mk (B.map ≫ p) ⟶ Over.mk p)
  have H := overPullbackMap_isPullback b p B.map
  have : IsIso (pullback.snd B.map (pullback.fst p b)) :=
    B.pullback_snd_isIso_of_comap_eq_top (pullback.fst p b) hI
  have hm : IsIso m.left := by
    change IsIso (((Over.pullback b).map
      (Over.homMk B.map rfl : Over.mk (B.map ≫ p) ⟶ Over.mk p)).left)
    rw [← H.flip.isoPullback_hom_snd]
    infer_instance
  have : IsIso ((Over.forget T).map m) := hm
  exact isIso_of_reflects_iso m (Over.forget T)

/-- The actual generic-fibre map of the original closed-point blowup is an
isomorphism. The centre's dimension and regularity are not needed here. -/
theorem pointBlowup_genericBaseChange_isIso {X : Scheme.{u}}
    (p : X ⟶ Spec (.of R)) [IsProper p] (x : X) (hx : IsClosed ({x} : Set X)) :
    IsIso ((Over.pullback (baseMap R F)).map
      (Over.homMk (blowupDatum (X.fromSpecResidueField x).ker).map rfl :
        Over.mk ((blowupDatum (X.fromSpecResidueField x).ker).map ≫ p) ⟶ Over.mk p)) :=
  blowup_overPullbackMap_isIso_of_comap_eq_top (baseMap R F) p
    (blowupDatum (X.fromSpecResidueField x).ker)
    (pointCentre_generic_comap_eq_top R F p x hx)

private theorem chain_genericBaseChange_isIso_of_triangle
    {X Y : Scheme.{u}} {f : Y ⟶ X} (c : PointBlowupChain f) :
    ∀ (p : X ⟶ Spec (.of R)) (q : Y ⟶ Spec (.of R)) (h : f ≫ p = q),
      IsProper p → IsIso ((Over.pullback (baseMap R F)).map
        (Over.homMk f h : Over.mk q ⟶ Over.mk p)) := by
  induction c with
  | refl X =>
    intro p q h _hp
    let m : Over.mk q ⟶ Over.mk p := Over.homMk (𝟙 X) h
    have : IsIso ((Over.forget (Spec (.of R))).map m) := inferInstanceAs (IsIso (𝟙 X))
    have : IsIso m := isIso_of_reflects_iso m (Over.forget (Spec (.of R)))
    exact (Over.pullback (baseMap R F)).map_isIso m
  | @cons X Y x hx _hd g tail ih =>
    intro p q h hp
    have : IsProper p := hp
    have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
    let B := blowupDatum (X.fromSpecResidueField x).ker
    have : IsProper B.map := B.isProper_of_isLocallyNoetherian
    have hq : g ≫ (B.map ≫ p) = q := by
      simpa only [Category.assoc] using h
    have : IsIso ((Over.pullback (baseMap R F)).map
        (Over.homMk g hq : Over.mk q ⟶ Over.mk (B.map ≫ p))) :=
      ih (B.map ≫ p) q hq inferInstance
    have : IsIso ((Over.pullback (baseMap R F)).map
        (Over.homMk B.map rfl : Over.mk (B.map ≫ p) ⟶ Over.mk p)) :=
      pointBlowup_genericBaseChange_isIso R F p x hx
    have heq : (Over.homMk (g ≫ B.map) h : Over.mk q ⟶ Over.mk p) =
        (Over.homMk g hq : Over.mk q ⟶ Over.mk (B.map ≫ p)) ≫
          (Over.homMk B.map rfl : Over.mk (B.map ≫ p) ⟶ Over.mk p) := by
      apply Over.OverMorphism.ext
      rfl
    change IsIso ((Over.pullback (baseMap R F)).map
      (Over.homMk (g ≫ B.map) h : Over.mk q ⟶ Over.mk p))
    rw [heq, Functor.map_comp]
    infer_instance

/-- The original literal generic-fibre map of a supplied actual finite
point-blowup chain on a proper DVR model is an isomorphism. -/
theorem PointBlowupChain.genericBaseChange_isIso
    {X Y : Scheme.{u}} {f : Y ⟶ X} (c : PointBlowupChain f)
    (p : X ⟶ Spec (.of R)) [IsProper p] :
    IsIso ((Over.pullback (baseMap R F)).map
      (Over.homMk f rfl : Over.mk (f ≫ p) ⟶ Over.mk p)) :=
  chain_genericBaseChange_isIso_of_triangle R F c p (f ≫ p) rfl inferInstance

/-- The isomorphism whose forward arrow is the original native base change
of the original point-blowup chain map. -/
def PointBlowupChain.genericIso
    {X Y : Scheme.{u}} {f : Y ⟶ X} (c : PointBlowupChain f)
    (p : X ⟶ Spec (.of R)) [IsProper p] :
    (Over.pullback (baseMap R F)).obj (Over.mk (f ≫ p)) ≅
      (Over.pullback (baseMap R F)).obj (Over.mk p) := by
  have := PointBlowupChain.genericBaseChange_isIso R F c p
  exact asIso ((Over.pullback (baseMap R F)).map
    (Over.homMk f rfl : Over.mk (f ≫ p) ⟶ Over.mk p))

@[simp]
theorem PointBlowupChain.genericIso_hom
    {X Y : Scheme.{u}} {f : Y ⟶ X} (c : PointBlowupChain f)
    (p : X ⟶ Spec (.of R)) [IsProper p] :
    (PointBlowupChain.genericIso R F c p).hom =
      (Over.pullback (baseMap R F)).map
        (Over.homMk f rfl : Over.mk (f ≫ p) ⟶ Over.mk p) := rfl

/-- The generic comparison retains the original chain map on first projections. -/
@[reassoc]
theorem PointBlowupChain.genericIso_hom_fst
    {X Y : Scheme.{u}} {f : Y ⟶ X} (c : PointBlowupChain f)
    (p : X ⟶ Spec (.of R)) [IsProper p] :
    (PointBlowupChain.genericIso R F c p).hom.left ≫ pullback.fst p (baseMap R F) =
      pullback.fst (f ≫ p) (baseMap R F) ≫ f := by
  rw [PointBlowupChain.genericIso_hom]
  simp [Over.pullback_map_left]

/-- The same comparison retains the original structural map to the specified fraction field. -/
@[reassoc]
theorem PointBlowupChain.genericIso_hom_snd
    {X Y : Scheme.{u}} {f : Y ⟶ X} (c : PointBlowupChain f)
    (p : X ⟶ Spec (.of R)) [IsProper p] :
    (PointBlowupChain.genericIso R F c p).hom.left ≫ pullback.snd p (baseMap R F) =
      pullback.snd (f ≫ p) (baseMap R F) :=
  (PointBlowupChain.genericIso R F c p).hom.w

end AlgebraicGeometry.Scheme.Blowup
