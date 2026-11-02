/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Over.FixedFiberHom

public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.SectionPullback
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finiteness.ProperCurveH1Family.RationalValues

/-! # Original fibre arrows and section differences

A Cartesian constant family gives a canonical map from the original scheme to
every rational fibre. Its composite to the original scheme is the identity,
not an unspecified automorphism. The cohomology operations below are the
original inverse-image Ext pullback and the original section pullback.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.EtaleCohomology.PointedNaturality

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology.ProperCurveH1Family

attribute [local instance] hasSheafifyLarge HasExt.standard

section PullbackZero

variable {X Y Z : Scheme.{u}}

/-- Vanishing through a composite is equivalent to vanishing under the actual
iterated pullback. Only the canonical coefficient isomorphism is canceled. -/
theorem h1Pullback_comp_eq_zero_iff (f : Y ⟶ X) (g : Z ⟶ Y)
    (L : AbelianSheaf.{u, u + 1} X) (c : H1Etale.{u, u + 1, u + 2} X L) :
    h1Pullback g ((inverseImage f).obj L) (h1Pullback f L c) = 0 ↔
      h1Pullback (g ≫ f) L c = 0 := by
  constructor
  · intro h
    apply (coefficientIso ((inverseImageComp f g).app L)).injective
    change coefficientMap ((inverseImageComp f g).hom.app L)
      (h1Pullback (g ≫ f) L c) = coefficientMap ((inverseImageComp f g).hom.app L) 0
    rw [h1Pullback_comp, h, map_zero]
  · intro h
    rw [← h1Pullback_comp, h, map_zero]

/-- Vanishing stays zero after further original geometric pullback. -/
theorem h1Pullback_comp_eq_zero (f : Y ⟶ X) (g : Z ⟶ Y)
    (L : AbelianSheaf.{u, u + 1} X) (c : H1Etale.{u, u + 1, u + 2} X L)
    (h : h1Pullback f L c = 0) : h1Pullback (g ≫ f) L c = 0 :=
  (h1Pullback_comp_eq_zero_iff f g L c).mp (by rw [h, map_zero])

/-- Equality of actual scheme arrows transports the zero assertion without
choosing a different cohomology model or coefficient identification. -/
theorem h1Pullback_eq_zero_of_eq {f g : Y ⟶ X} (hfg : f = g)
    (L : AbelianSheaf.{u, u + 1} X) (c : H1Etale.{u, u + 1, u + 2} X L)
    (h : h1Pullback f L c = 0) : h1Pullback g L c = 0 := by
  subst g
  exact h

end PullbackZero

section FibreArrow

variable {k : Type u} [Field k] {X Y T : Scheme.{u}}
  {f : X ⟶ Spec (.of k)} {t : T ⟶ Spec (.of k)}
  {r : Y ⟶ X} {p : Y ⟶ T} (h : IsPullback r p f t)
  (b : Spec (.of k) ⟶ T) (hb : b ≫ t = 𝟙 _)

/-- The literal arrow from the original scheme to the rational fibre of its
Cartesian constant family. -/
def fibreArrow : X ⟶ Y :=
  h.splitBaseArrow b hb

@[reassoc (attr := simp)]
theorem fibreArrow_curveMap : fibreArrow h b hb ≫ r = 𝟙 X :=
  h.splitBaseArrow_fst b hb

@[reassoc (attr := simp)]
theorem fibreArrow_projection : fibreArrow h b hb ≫ p = f ≫ b :=
  h.splitBaseArrow_snd b hb

/-- These two original projection equations determine the fibre arrow. -/
theorem eq_fibreArrow (a : X ⟶ Y) (haX : a ≫ r = 𝟙 X)
    (haT : a ≫ p = f ≫ b) : a = fibreArrow h b hb :=
  h.eq_splitBaseArrow b hb a haX haT

/-- Any actual map into this rational fibre factors through the original
scheme, with its original projection as the factor. -/
theorem comp_fibreArrow_eq {W : Scheme.{u}} (a : W ⟶ Y)
    (v : W ⟶ Spec (.of k)) (ha : a ≫ p = v ≫ b) :
    (a ≫ r) ≫ fibreArrow h b hb = a :=
  h.comp_splitBaseArrow_eq b hb a v ha

/-- The canonical original-scheme arrow gives the actual Cartesian fibre. -/
theorem isPullback_fibreArrow : IsPullback (fibreArrow h b hb) f p b :=
  h.isPullback_splitBaseArrow b hb

/-- The original cohomology value at an actual rational parameter. -/
def value (L : AbelianSheaf.{u, u + 1} X)
    (c : H1Etale.{u, u + 1, u + 2} Y ((inverseImage r).obj L)) :
    H1Etale.{u, u + 1, u + 2} X L :=
  sectionPullback r (fibreArrow h b hb) (fibreArrow_curveMap h b hb) L c

end FibreArrow

section Difference

variable {X Y : Scheme.{u}} (r : Y ⟶ X) (a : X ⟶ Y) (ha : a ≫ r = 𝟙 X)
  (L : AbelianSheaf.{u, u + 1} X)
  (c : H1Etale.{u, u + 1, u + 2} Y ((inverseImage r).obj L))

/-- Subtract the inflation of the actual original fibre value. -/
def difference : H1Etale.{u, u + 1, u + 2} Y ((inverseImage r).obj L) :=
  c - h1Pullback r L (sectionPullback r a ha L c)

/-- The section retraction proves that the actual geometric restriction of
the difference is zero, before any henselian or continuity argument. -/
theorem difference_pullback_eq_zero :
    h1Pullback a ((inverseImage r).obj L) (difference r a ha L c) = 0 := by
  apply (coefficientIso (sectionCoefficientIso r a ha L)).injective
  change sectionPullback r a ha L (difference r a ha L c) =
    coefficientIso (sectionCoefficientIso r a ha L) 0
  rw [map_zero]
  simp only [difference, map_sub, sectionPullback_inflation, sub_self]

/-- A zero restriction of the difference gives equality in the fixed original
H1 group; its coefficient identification is still the actual section map. -/
theorem sectionPullback_eq_of_difference_eq_zero
    (a' : X ⟶ Y) (ha' : a' ≫ r = 𝟙 X)
    (hz : h1Pullback a' ((inverseImage r).obj L) (difference r a ha L c) = 0) :
    sectionPullback r a' ha' L c = sectionPullback r a ha L c := by
  have hv := congrArg (coefficientIso (sectionCoefficientIso r a' ha' L)) hz
  change sectionPullback r a' ha' L (difference r a ha L c) =
    coefficientIso (sectionCoefficientIso r a' ha' L) 0 at hv
  rw [map_zero] at hv
  simpa only [difference, map_sub, sectionPullback_inflation, sub_eq_zero] using hv

end Difference

end AlgebraicGeometry.Scheme.EtaleCohomology.ProperCurveH1Family
