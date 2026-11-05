/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Etale.PointedTargetRestriction
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Fields.TwoFieldEffacement.OriginalClassZeroTransport
public import Aglib.CategoryTheory.Sites.SheafCohomology.MapIsoInjection
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-! # Returning an actual target-chart zero to the original family

The original class is restricted along the chosen target chart. A genuine
stage zero for that restriction returns through the literal pullback-pasting
isomorphism to the unchanged original class. The coefficient form retains the
canonical inverse-image composition, so a fixed finite coefficient detector
can be used without changing its original coefficient sheaf or adjunct.

These are consumers of an actual produced chart-stage zero, not existence
claims for such a zero. The same etale chart and original point are retained
when its map is composed into the arbitrary original target scheme.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Finite

universe u eY

attribute [local instance] hasSheafifyLarge HasExt.standard

variable {X O Y V : Scheme.{u}} (j : O ⟶ X) (a : Y ⟶ X) (t : V ⟶ O)
    [HasExt.{eY} (AbelianSheaf.{u, u + 1} Y)]

/-- A zero of the actual iterated restriction returns to the full original
family pullback along the composite target map. -/
theorem target_composite_zero_of_restriction_zero
    (M : AbelianSheaf.{u, u + 1} Y) (q : ℕ) (c : Sheaf.H.{eY} M q)
    (hc : cohomologyPullback.{u, u + 2, u + 2}
      (pullback.snd t (pullback.fst j a)) ((inverseImage (pullback.snd j a)).obj M) q
      (cohomologyPullback.{u, eY, u + 2} (pullback.snd j a) M q c) = 0) :
    cohomologyPullback.{u, eY, u + 2} (pullback.snd (t ≫ j) a) M q c = 0 := by
  have hcomp : cohomologyPullback.{u, eY, u + 2}
      (pullback.snd t (pullback.fst j a) ≫ pullback.snd j a) M q c = 0 := by
    apply (cohomologyMapIso_bijective
      ((inverseImageComp (pullback.snd j a) (pullback.snd t (pullback.fst j a))).app M)
      q).injective
    exact (cohomologyPullback_comp.{u, eY, u + 2, u + 2}
      (pullback.snd j a) (pullback.snd t (pullback.fst j a)) M q c).trans
        (hc.trans (map_zero _).symm)
  exact TwoFieldEffacement.original_class_zero_of_map_law
    (pullbackRightPullbackFstIso j a t).inv
    (pullback.snd t (pullback.fst j a) ≫ pullback.snd j a)
    (pullback.snd (t ≫ j) a)
    (pullbackRightPullbackFstIso_inv_snd_snd j a t) M q c hcomp

/-- Return a stage zero written with the same original coefficient sheaf and
its actual restricted structural map, including the canonical coefficient iso. -/
theorem target_composite_zero_of_coefficient_restriction_zero
    {B : Scheme.{u}} (b : Y ⟶ B) (I : AbelianSheaf.{u, u + 1} B)
    (q : ℕ) (c : Sheaf.H.{eY} ((inverseImage b).obj I) q)
    (hc : cohomologyPullback.{u, u + 2, u + 2}
      (pullback.snd t (pullback.fst j a))
      ((inverseImage (pullback.snd j a ≫ b)).obj I) q
      (Sheaf.H.map ((inverseImageComp b (pullback.snd j a)).inv.app I) q
        (cohomologyPullback.{u, eY, u + 2} (pullback.snd j a)
          ((inverseImage b).obj I) q c)) = 0) :
    cohomologyPullback.{u, eY, u + 2} (pullback.snd (t ≫ j) a)
      ((inverseImage b).obj I) q c = 0 := by
  apply target_composite_zero_of_restriction_zero j a t ((inverseImage b).obj I) q c
  apply Sheaf.H.map_injective_of_isIso
    ((inverseImage (pullback.snd t (pullback.fst j a))).map
      ((inverseImageComp b (pullback.snd j a)).inv.app I)) q
  exact (cohomologyPullback_coefficientMap.{u, u + 2, u + 2}
    (pullback.snd t (pullback.fst j a))
    ((inverseImageComp b (pullback.snd j a)).inv.app I) q
    (cohomologyPullback.{u, eY, u + 2} (pullback.snd j a)
      ((inverseImage b).obj I) q c)).symm.trans (hc.trans (map_zero _).symm)

/-- Compose the actual pointed etale stage with the target open immersion.
The original point and the original full family class are both retained. -/
theorem pointed_target_chart_return
    [IsOpenImmersion j] (Ω : Type u) [Field Ω]
    (x : Spec (.of Ω) ⟶ X) (xO : Spec (.of Ω) ⟶ O) (hxO : xO ≫ j = x)
    (U : O.Etale) (z : Spec (.of Ω) ⟶ U.left) (hz : z ≫ U.hom = xO)
    {B : Scheme.{u}} (b : Y ⟶ B) (I : AbelianSheaf.{u, u + 1} B)
    (q : ℕ) (c : Sheaf.H.{eY} ((inverseImage b).obj I) q)
    (hc : cohomologyPullback.{u, u + 2, u + 2}
      (pullback.snd U.hom (pullback.fst j a))
      ((inverseImage (pullback.snd j a ≫ b)).obj I) q
      (Sheaf.H.map ((inverseImageComp b (pullback.snd j a)).inv.app I) q
        (cohomologyPullback.{u, eY, u + 2} (pullback.snd j a)
          ((inverseImage b).obj I) q c)) = 0) :
    let W : X.Etale := Scheme.Etale.mk (U.hom ≫ j)
    z ≫ W.hom = x ∧
      cohomologyPullback.{u, eY, u + 2} (pullback.snd W.hom a)
        ((inverseImage b).obj I) q c = 0 := by
  constructor
  · exact (Category.assoc z U.hom j).symm.trans
      ((congrArg (fun f : Spec (.of Ω) ⟶ O => f ≫ j) hz).trans hxO)
  · exact target_composite_zero_of_coefficient_restriction_zero j a U.hom b I q c hc

end AlgebraicGeometry.Scheme.EtaleCohomology.Finite
