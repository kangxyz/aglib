/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.BaseChange
public import Aglib.AlgebraicGeometry.IdealSheaf.Cartier.FlatComap

/-!
# Actual flat base change of universal blowups

The literal pullback of a given universal blowup along a flat map is again
universal for the actual inverse-image centre. Comparing this constructed datum
with any given blowup of that centre makes the existing canonical base-change
map cartesian. No Noetherian, finite-generation or reducedness hypothesis is used.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Blowup

/-- Flat precomposition preserves the original Cartier image-ideal predicate. -/
theorem cartierPullback_comp_of_flat {X T W : Scheme.{u}} (I : X.IdealSheafData)
    (g : T ⟶ X) (hg : cartierPullback I g) (f : W ⟶ T) [Flat f] :
    cartierPullback I (f ≫ g) := by
  unfold cartierPullback
  rw [Scheme.IdealSheafData.comap_comp]
  exact (I.comap g).isLocallyRankOne_comap_of_flat f hg

/-- The literal pullback of a universal blowup along a flat base map, equipped with the
proved Cartier property and final-object property for the actual inverse-image centre. -/
def flatPullbackDatum {X X' : Scheme.{u}} {I : X.IdealSheafData}
    (B : BlowupDatum I) (f : X' ⟶ X) [Flat f] : BlowupDatum (I.comap f) where
  Y := pullback B.map f
  map := pullback.snd B.map f
  cartier := by
    have h := cartierPullback_comp_of_flat I B.map B.cartier (pullback.fst B.map f)
    unfold cartierPullback at h ⊢
    rw [pullback.condition, Scheme.IdealSheafData.comap_comp] at h
    exact h
  universal T t ht := by
    have htf : cartierPullback I (t ≫ f) := by
      unfold cartierPullback
      rw [Scheme.IdealSheafData.comap_comp]
      exact ht
    let l := B.lift (t ≫ f) htf
    have hl : l ≫ B.map = t ≫ f := B.lift_map (t ≫ f) htf
    refine ⟨pullback.lift l t hl, pullback.lift_snd l t hl, ?_⟩
    intro g hg
    apply pullback.hom_ext
    · rw [pullback.lift_fst]
      apply B.hom_ext htf _ hl
      rw [Category.assoc, pullback.condition, ← Category.assoc, hg]
    · rw [pullback.lift_snd]
      exact hg

/-- The unique comparison from the given blowup of the inverse-image centre to the
constructed universal datum on the literal pullback. -/
def flatComparisonIso {X X' : Scheme.{u}} {I : X.IdealSheafData}
    (B : BlowupDatum I) (f : X' ⟶ X) [Flat f] (B' : BlowupDatum (I.comap f)) :
    B'.Y ≅ pullback B.map f :=
  B'.comparisonIso (flatPullbackDatum B f)

@[reassoc (attr := simp)]
theorem flatComparisonIso_hom_snd {X X' : Scheme.{u}} {I : X.IdealSheafData}
    (B : BlowupDatum I) (f : X' ⟶ X) [Flat f] (B' : BlowupDatum (I.comap f)) :
    (flatComparisonIso B f B').hom ≫ pullback.snd B.map f = B'.map :=
  B'.comparisonIso_hom_map (flatPullbackDatum B f)

@[reassoc (attr := simp)]
theorem flatComparisonIso_hom_fst {X X' : Scheme.{u}} {I : X.IdealSheafData}
    (B : BlowupDatum I) (f : X' ⟶ X) [Flat f] (B' : BlowupDatum (I.comap f)) :
    (flatComparisonIso B f B').hom ≫ pullback.fst B.map f = BaseChange.map f rfl B B' := by
  apply BaseChange.map_unique
  rw [Category.assoc, pullback.condition, ← Category.assoc, flatComparisonIso_hom_snd]

/-- The existing canonical map between any two given universal blowups is cartesian
for an arbitrary flat base map and the exact actual centre equality. -/
theorem BaseChange.isPullback_of_flat {X X' : Scheme.{u}}
    {I : X.IdealSheafData} {I' : X'.IdealSheafData}
    (f : X' ⟶ X) (hf : Flat f) (hI : I.comap f = I')
    (B : BlowupDatum I) (B' : BlowupDatum I') :
    IsPullback (BaseChange.map f hI B B') B'.map B.map f := by
  subst I'
  let := hf
  exact IsPullback.of_iso_pullback ⟨BaseChange.map_triangle f rfl B B'⟩
    (flatComparisonIso B f B') (flatComparisonIso_hom_fst B f B')
    (flatComparisonIso_hom_snd B f B')

/-- The exact universal flat-base-change family is supplied by the constructed literal
pullback datum and its actual comparison with the given blowup. -/
theorem blowupFlatBaseChange : BlowupFlatBaseChange.{u} := by
  intro X X' f hf I B B'
  exact ⟨BaseChange.map f rfl B B', BaseChange.isPullback_of_flat f hf rfl B B'⟩

end AlgebraicGeometry.Scheme.Blowup
