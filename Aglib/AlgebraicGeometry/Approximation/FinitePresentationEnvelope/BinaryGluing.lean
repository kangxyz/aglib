/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Gluing.OpenPushoutMap
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Equifibered

/-!
# Actual inverse systems of binary open gluings

Glue the original open spans pointwise. Transition maps and cone projections
are the native `pushout.map`, and both chart natural transformations retain
their original cartesian squares. This constructs the diagram and cone, not
a limit certificate or a global finite-presentation envelope.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry.Scheme.FinitePresentationEnvelope.BinaryGluing

variable {I : Type v} [Category.{w} I]
  {W U V : I ⥤ Scheme.{u}} (f : W ⟶ U) (g : W ⟶ V)
  [∀ i, IsOpenImmersion (f.app i)] [∀ i, IsOpenImmersion (g.app i)]

/-- The actual pointwise open-pushout diagram, with native transition maps. -/
def diagram : I ⥤ Scheme.{u} where
  obj i := pushout (f.app i) (g.app i)
  map {i j} r := pushout.map (f.app i) (g.app i) (f.app j) (g.app j)
    (U.map r) (V.map r) (W.map r) (f.naturality r).symm (g.naturality r).symm
  map_id i := by simp
  map_comp r s := by simp only [Functor.map_comp, pushout.map_comp]

/-- The original left open charts form a natural transformation. -/
def left : U ⟶ diagram f g where
  app i := pushout.inl (f.app i) (g.app i)
  naturality i j r := by simp [diagram]

/-- The original right open charts form a natural transformation. -/
def right : V ⟶ diagram f g where
  app i := pushout.inr (f.app i) (g.app i)
  naturality i j r := by simp [diagram]

instance left_isOpenImmersion (i : I) : IsOpenImmersion ((left f g).app i) :=
  inferInstanceAs (IsOpenImmersion (pushout.inl (f.app i) (g.app i)))

instance right_isOpenImmersion (i : I) : IsOpenImmersion ((right f g).app i) :=
  inferInstanceAs (IsOpenImmersion (pushout.inr (f.app i) (g.app i)))

/-- The left charts remain cartesian when the right overlap squares are. -/
theorem left_equifibered (hg : g.Equifibered) : (left f g).Equifibered := by
  intro i j r
  exact OpenPushoutMap.isPullback_inl (f.app i) (g.app i) (f.app j) (g.app j)
    (W.map r) (U.map r) (V.map r) (f.naturality r).symm (g.naturality r).symm (hg r)

/-- The right charts remain cartesian when the left overlap squares are. -/
theorem right_equifibered (hf : f.Equifibered) : (right f g).Equifibered := by
  intro i j r
  exact OpenPushoutMap.isPullback_inr (f.app i) (g.app i) (f.app j) (g.app j)
    (W.map r) (U.map r) (V.map r) (f.naturality r).symm (g.naturality r).symm (hf r)

/-- Affine transition maps on both original charts give affine transitions
on the literal pointwise pushouts. -/
theorem map_isAffineHom (hf : f.Equifibered) (hg : g.Equifibered)
    {i j : I} (r : i ⟶ j) [IsAffineHom (U.map r)] [IsAffineHom (V.map r)] :
    IsAffineHom ((diagram f g).map r) :=
  OpenPushoutMap.isAffineHom (f.app i) (g.app i) (f.app j) (g.app j)
    (W.map r) (U.map r) (V.map r) (f.naturality r).symm (g.naturality r).symm
    (hf r) (hg r)

instance stage_compact [∀ i, CompactSpace (U.obj i)] [∀ i, CompactSpace (V.obj i)]
    (i : I) : CompactSpace ((diagram f g).obj i) :=
  openPushout_compactSpace (f.app i) (g.app i)

variable (cW : Cone W) (cU : Cone U) (cV : Cone V)
  (f₀ : cW.pt ⟶ cU.pt) (g₀ : cW.pt ⟶ cV.pt)
  [IsOpenImmersion f₀] [IsOpenImmersion g₀]
  (hf₀ : ∀ i, f₀ ≫ cU.π.app i = cW.π.app i ≫ f.app i)
  (hg₀ : ∀ i, g₀ ≫ cV.π.app i = cW.π.app i ≫ g.app i)

/-- Glue three compatible original cones. Its point is their native open
pushout, and every projection is the literal native map of pushouts. -/
def cone : Cone (diagram f g) where
  pt := pushout f₀ g₀
  π :=
    { app i := pushout.map f₀ g₀ (f.app i) (g.app i)
        (cU.π.app i) (cV.π.app i) (cW.π.app i) (hf₀ i) (hg₀ i)
      naturality i j r := by
        apply pushout.hom_ext <;>
          simp [diagram, Category.assoc] }

/-- Every projection retains its original left chart equation. -/
@[reassoc (attr := simp)]
theorem inl_cone_π (i : I) :
    pushout.inl f₀ g₀ ≫ (cone f g cW cU cV f₀ g₀ hf₀ hg₀).π.app i =
      cU.π.app i ≫ pushout.inl (f.app i) (g.app i) :=
  pushout.inl_desc _ _ _

/-- Every projection retains its original right chart equation. -/
@[reassoc (attr := simp)]
theorem inr_cone_π (i : I) :
    pushout.inr f₀ g₀ ≫ (cone f g cW cU cV f₀ g₀ hf₀ hg₀).π.app i =
      cV.π.app i ≫ pushout.inr (f.app i) (g.app i) :=
  pushout.inr_desc _ _ _

/-- A cartesian right-overlap cone square makes the original left cone
projection square cartesian. -/
theorem cone_inl_isPullback (i : I)
    (Hg : IsPullback (cW.π.app i) g₀ (g.app i) (cV.π.app i)) :
    IsPullback (cU.π.app i) (pushout.inl f₀ g₀)
      (pushout.inl (f.app i) (g.app i)) ((cone f g cW cU cV f₀ g₀ hf₀ hg₀).π.app i) :=
  OpenPushoutMap.isPullback_inl f₀ g₀ (f.app i) (g.app i)
    (cW.π.app i) (cU.π.app i) (cV.π.app i) (hf₀ i) (hg₀ i) Hg

/-- A cartesian left-overlap cone square makes the original right cone
projection square cartesian. -/
theorem cone_inr_isPullback (i : I)
    (Hf : IsPullback (cW.π.app i) f₀ (f.app i) (cU.π.app i)) :
    IsPullback (cV.π.app i) (pushout.inr f₀ g₀)
      (pushout.inr (f.app i) (g.app i)) ((cone f g cW cU cV f₀ g₀ hf₀ hg₀).π.app i) :=
  OpenPushoutMap.isPullback_inr f₀ g₀ (f.app i) (g.app i)
    (cW.π.app i) (cU.π.app i) (cV.π.app i) (hf₀ i) (hg₀ i) Hf

end AlgebraicGeometry.Scheme.FinitePresentationEnvelope.BinaryGluing
