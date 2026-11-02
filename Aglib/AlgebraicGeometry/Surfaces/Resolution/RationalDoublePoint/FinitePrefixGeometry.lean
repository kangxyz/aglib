/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.ClosedPointPrefix.BaseChange
public import Aglib.AlgebraicGeometry.Surfaces.Resolution.PointBlowupChain.ClosedPrefix
public import Aglib.AlgebraicGeometry.Surfaces.Resolution.RationalDoublePoint.BlowupChildren
public import Aglib.AlgebraicGeometry.Surfaces.Resolution.RationalDoublePoint.FiniteSingularLocus
public import Aglib.AlgebraicGeometry.Surfaces.RationalSingularities.Blowup.PointNormality

/-!
# Actual finite-prefix geometry over a rational surface base

The original finite prefixes remain normal, and their actual ancestor centres
have dimension two. Their actual next blowup has a finite singular set, even
when there is no singular child. No infinite extension or finite-set premise
is used to derive these facts.
-/

@[expose] public noncomputable section
set_option autoImplicit false

open CategoryTheory TopologicalSpace
open AlgebraicGeometry.Scheme.RationalSingularities

universe u

namespace AlgebraicGeometry.Scheme.Blowup.ClosedPointPrefix

variable (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A]
    (hA : IsNagataRing.{u, 0} A) (hdA : ringKrullDim A = 2)
    (hRat : NormalModificationH1Vanishing A)
    {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of A)) [IsProper f] [IsDominant f]
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap f)))

include hA hdA hRat hff in
private theorem singular_stalk_after_pointChain
    {Y : Scheme.{u}} (g : Y ⟶ X) (c : PointBlowupChain g)
    (hY : NormalStalks Y) (y : Y)
    (hy : ¬ IsRegularLocalRing (Y.presheaf.stalk y)) :
    IsNagataRing.{u, 0} (Y.presheaf.stalk y) ∧
      ringKrullDim (Y.presheaf.stalk y) = 2 ∧
      (letI : IsDomain (Y.presheaf.stalk y) := (hY y).1;
        NormalModificationH1Vanishing (Y.presheaf.stalk y)) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : IsIntegral Y := c.isIntegral inferInstance
  let : IsProper g := c.isProper inferInstance
  let : IsDominant g := c.isDominant inferInstance
  let : IsIso (CommRingCat.ofHom (functionFieldMap g)) := c.functionFieldMap_isIso inferInstance
  let : IsIso (CommRingCat.ofHom (functionFieldMap f)) := hff
  have hcomp : IsIso (CommRingCat.ofHom (functionFieldMap (g ≫ f))) := by
    rw [functionFieldMap_comp, CommRingCat.ofHom_comp]
    infer_instance
  obtain ⟨_, _, _, hN, hd, _, _, _, _, hR⟩ :=
    singular_stalk_properties_of_rational_model A hA hdA hRat (g ≫ f) hY hcomp y hy
  exact ⟨hN, hd, hR⟩

include hA hdA hRat hff in
/-- Every actual finite singular prefix is normal, and all its actual selected
truncation ancestors have dimension two. No infinite continuation is assumed. -/
theorem singularPrefix_normal_and_dimensions (hX : NormalStalks X)
    (x : X) (hx : ¬ IsRegularLocalRing (X.presheaf.stalk x))
    (n : ℕ) (p : SingularPrefix X x n) :
    NormalStalks (scheme p) ∧ ∀ m (hm : m ≤ n),
      ringKrullDim ((scheme (truncate hm p)).presheaf.stalk
        (point (truncate hm p))) = 2 := by
  obtain ⟨_, _, _, _, hdimRoot, hclosed, _, _, _, _⟩ :=
    singular_stalk_properties_of_rational_model A hA hdA hRat f hX hff x hx
  induction n with
  | zero =>
    refine ⟨hX, fun m hm => ?_⟩
    have hm0 : m = 0 := Nat.eq_zero_of_le_zero hm
    subst m
    exact hdimRoot
  | succ n ih =>
    let q : SingularPrefix X x n := parent p
    obtain ⟨hNq, hdq⟩ := ih q
    have hdimq : ringKrullDim ((scheme q).presheaf.stalk (point q)) = 2 := by
      exact Eq.mp (congrArg (fun a : SingularPrefix X x n =>
        ringKrullDim ((scheme a).presheaf.stalk (point a)) = 2) (truncate_refl q))
        (hdq n (Nat.le_refl n))
    let c := pointBlowupChain_toBase hclosed q (fun m hm => hdq m hm.le)
    obtain ⟨hN, _, hR⟩ := singular_stalk_after_pointChain A hA hdA hRat f hff
      (toBase q) c hNq (point q) (point_eligible hx q)
    have hB : NormalStalks (datum q).Y :=
      normalStalks_pointBlowup_of_rational_stalk (scheme q) hNq (point q)
        (point_closed hclosed q) hN hdimq hR
    have hanc : ∀ m (hm : m < n + 1),
        ringKrullDim ((scheme (truncate hm.le p)).presheaf.stalk
          (point (truncate hm.le p))) = 2 := by
      intro m hm
      have hmn : m ≤ n := Nat.le_of_lt_succ hm
      rw [truncate_succ hmn]
      exact hdq m hmn
    let cp := pointBlowupChain_toBase hclosed p hanc
    have hdimP := (singular_stalk_after_pointChain A hA hdA hRat f hff
      (toBase p) cp hB (point p) (point_eligible hx p)).2.1
    refine ⟨hB, fun m hm => ?_⟩
    by_cases he : m = n + 1
    · subst m
      exact Eq.mpr (congrArg (fun a : SingularPrefix X x (n + 1) =>
        ringKrullDim ((scheme a).presheaf.stalk (point a)) = 2) (truncate_refl p)) hdimP
    · exact hanc m (lt_of_le_of_ne hm he)

include hA hdA hRat hff in
/-- The actual next blowup of any finite singular prefix has finitely many
singular points, including when the selected prefix has no singular child. -/
theorem finite_singularSet_datum_of_rational_model (hX : NormalStalks X)
    (x : X) (hx : ¬ IsRegularLocalRing (X.presheaf.stalk x))
    {n : ℕ} (p : SingularPrefix X x n) :
    {y : (datum p).Y | ¬ IsRegularLocalRing ((datum p).Y.presheaf.stalk y)}.Finite := by
  obtain ⟨_, _, _, _, _, hclosed, _, _, _, _⟩ :=
    singular_stalk_properties_of_rational_model A hA hdA hRat f hX hff x hx
  obtain ⟨hNp, hdp⟩ := singularPrefix_normal_and_dimensions A hA hdA hRat f hff hX x hx n p
  have hd : ringKrullDim ((scheme p).presheaf.stalk (point p)) = 2 := by
    exact Eq.mp (congrArg (fun a : SingularPrefix X x n =>
      ringKrullDim ((scheme a).presheaf.stalk (point a)) = 2) (truncate_refl p))
      (hdp n (Nat.le_refl n))
  let c := pointBlowupChain_toBase hclosed p (fun m hm => hdp m hm.le)
  obtain ⟨hN, _, hR⟩ := singular_stalk_after_pointChain A hA hdA hRat f hff
    (toBase p) c hNp (point p) (point_eligible hx p)
  have hB : NormalStalks (datum p).Y :=
    normalStalks_pointBlowup_of_rational_stalk (scheme p) hNp (point p)
      (point_closed hclosed p) hN hd hR
  have hs : PointBlowupChain (datum p).map := by
    have hstep : PointBlowupChain (𝟙 (datum p).Y ≫ (datum p).map) :=
      PointBlowupChain.cons (point p) (point_closed hclosed p) hd
        (𝟙 (datum p).Y) (PointBlowupChain.refl (datum p).Y)
    exact Eq.mp (congrArg (fun g : (datum p).Y ⟶ scheme p => PointBlowupChain g)
      (Category.id_comp (datum p).map)) hstep
  let cs := c.comp hs
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : IsIntegral (datum p).Y := cs.isIntegral inferInstance
  let : IsProper ((datum p).map ≫ toBase p) := cs.isProper inferInstance
  let : IsDominant ((datum p).map ≫ toBase p) := cs.isDominant inferInstance
  let : IsIso (CommRingCat.ofHom (functionFieldMap ((datum p).map ≫ toBase p))) :=
    cs.functionFieldMap_isIso inferInstance
  let : IsIso (CommRingCat.ofHom (functionFieldMap f)) := hff
  let g := ((datum p).map ≫ toBase p) ≫ f
  have hcomp : IsIso (CommRingCat.ofHom (functionFieldMap g)) := by
    change IsIso (CommRingCat.ofHom (functionFieldMap (((datum p).map ≫ toBase p) ≫ f)))
    rw [functionFieldMap_comp, CommRingCat.ofHom_comp]
    infer_instance
  let : CompactSpace (datum p).Y := QuasiCompact.compactSpace_of_compactSpace g
  let : IsNoetherian (datum p).Y := { __ := LocallyOfFiniteType.isLocallyNoetherian g }
  have hdim := Cohomology.actualModel_dimension_of_nagata g hA hdA.le hcomp
  have hJ : IsJ2Ring.{u, 0} A :=
    IsNagataRing.isJ2Ring_of_semilocal_dimLE_two A hA hdA.le
  exact finite_singularSet_of_finiteType_of_isJ2Ring A g hJ hB hdim

include hA hdA hRat hff in
/-- Genuine rational-model geometry makes every original parent fibre finite. -/
theorem singularPrefix_parent_fiber_finite (hX : NormalStalks X)
    (x : X) (hx : ¬ IsRegularLocalRing (X.presheaf.stalk x))
    {n : ℕ} (p : SingularPrefix X x n) :
    Finite {q : SingularPrefix X x (n + 1) // parent q = p} :=
  parent_fiber_finite p
    (finite_singularSet_datum_of_rational_model A hA hdA hRat f hff hX x hx p)

end AlgebraicGeometry.Scheme.Blowup.ClosedPointPrefix
