/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Limits

/-! # Canonical affine-cover geometry for the original restriction cube

The target cover is the native affine cover and the target's base-change
cover is its literal native pullback cover. Both source restrictions are
literal pullbacks. Their original projections and the native pullback map
satisfy the exact restriction equations and form a Cartesian local square.
These constructions impose no properness or cohomological hypotheses.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Proper.AffineCoverGeometry

/-- The index of the native affine target cover. -/
abbrev Index (S : Scheme.{u}) := S.affineCover.I₀

/-- The original affine target chart. -/
def T (S : Scheme.{u}) (i : Index S) : Scheme.{u} := S.affineCover.X i

/-- The original affine-chart immersion. -/
def jS (S : Scheme.{u}) (i : Index S) : T S i ⟶ S := S.affineCover.f i

instance (S : Scheme.{u}) (i : Index S) : IsAffine (T S i) := by
  change IsAffine (S.affineCover.X i)
  infer_instance

instance (S : Scheme.{u}) (i : Index S) : IsOpenImmersion (jS S i) := by
  change IsOpenImmersion (S.affineCover.f i)
  infer_instance

/-- The literal native pullback open cover, with its geometric cover type retained. -/
def pullbackCover {S S' : Scheme.{u}} (g : S' ⟶ S) : S'.OpenCover :=
  S.affineCover.pullback₁ g

/-- The small-etale object of the literal native pullback open cover. -/
def U {S S' : Scheme.{u}} (g : S' ⟶ S) (i : Index S) : S'.Etale := by
  let : IsOpenImmersion ((pullbackCover g).f i) := (pullbackCover g).map_prop i
  exact Scheme.Etale.mk ((pullbackCover g).f i)

instance {S S' : Scheme.{u}} (g : S' ⟶ S) (i : Index S) :
    IsOpenImmersion (U g i).hom := by
  change IsOpenImmersion ((pullbackCover g).f i)
  exact (pullbackCover g).map_prop i

/-- The native pulled-back target charts jointly cover the actual base-change target. -/
theorem hU {S S' : Scheme.{u}} (g : S' ⟶ S) :
    ∀ s : S', ∃ (i : Index S) (x : (U g i).left), (U g i).hom x = s :=
  (pullbackCover g).exists_eq

/-- The first actual source restriction. -/
def Y {X S : Scheme.{u}} (f : X ⟶ S) (i : Index S) : Scheme.{u} :=
  pullback f (jS S i)

/-- Its projection to the original affine chart. -/
def p {X S : Scheme.{u}} (f : X ⟶ S) (i : Index S) : Y f i ⟶ T S i :=
  pullback.snd f (jS S i)

/-- Its projection to the original source. -/
def jX {X S : Scheme.{u}} (f : X ⟶ S) (i : Index S) : Y f i ⟶ X :=
  pullback.fst f (jS S i)

/-- The literal first source-restriction square, in the original cube convention. -/
theorem sf {X S : Scheme.{u}} (f : X ⟶ S) (i : Index S) :
    IsPullback (p f i) (jX f i) (jS S i) f :=
  (IsPullback.of_hasPullback f (jS S i)).flip

/-- The actual restriction of the base-changed source. -/
def Y' {X' S S' : Scheme.{u}} (f' : X' ⟶ S') (g : S' ⟶ S)
    (i : Index S) : Scheme.{u} := pullback f' (U g i).hom

/-- Its projection to the original pulled-back target chart. -/
def p' {X' S S' : Scheme.{u}} (f' : X' ⟶ S') (g : S' ⟶ S)
    (i : Index S) : Y' f' g i ⟶ (U g i).left :=
  pullback.snd f' (U g i).hom

/-- Its projection to the original base-changed source. -/
def jX' {X' S S' : Scheme.{u}} (f' : X' ⟶ S') (g : S' ⟶ S)
    (i : Index S) : Y' f' g i ⟶ X' := pullback.fst f' (U g i).hom

/-- The literal second source-restriction square. -/
theorem sf' {X' S S' : Scheme.{u}} (f' : X' ⟶ S') (g : S' ⟶ S)
    (i : Index S) : IsPullback (p' f' g i) (jX' f' g i) (U g i).hom f' :=
  (IsPullback.of_hasPullback f' (U g i).hom).flip

/-- The native pullback-cover projection to the original target chart. -/
def q {S S' : Scheme.{u}} (g : S' ⟶ S) (i : Index S) : (U g i).left ⟶ T S i :=
  S.affineCover.pullbackHom g i

/-- The actual target-map equation of the restriction cube. -/
theorem hg {S S' : Scheme.{u}} (g : S' ⟶ S) (i : Index S) :
    q g i ≫ jS S i = (U g i).hom ≫ g :=
  S.affineCover.pullbackHom_map g i

/-- The native map between the actual source restrictions. -/
def q' {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g) (i : Index S) : Y' f' g i ⟶ Y f i :=
  pullback.map f' (U g i).hom f (jS S i) g' (q g i) g sq.w.symm (hg g i).symm

/-- The actual source-map equation of the restriction cube. -/
theorem hg' {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g) (i : Index S) :
    q' f f' g g' sq i ≫ jX f i = jX' f' g i ≫ g' :=
  pullback.lift_fst _ _ _

/-- The original local maps commute before any sheaf or derived functor is applied. -/
theorem local_comm {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g) (i : Index S) :
    q' f f' g g' sq i ≫ p f i = p' f' g i ≫ q g i :=
  pullback.lift_snd _ _ _

/-- The actual local square is Cartesian by pasting and cancellation of the
two original restriction squares with the supplied global Cartesian square. -/
theorem localSq {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g) (i : Index S) :
    IsPullback (q' f f' g g' sq i) (p' f' g i) (p f i) (q g i) := by
  have hOuter : IsPullback (q' f f' g g' sq i ≫ jX f i) (p' f' g i)
      f (q g i ≫ jS S i) := by
    rw [hg', hg]
    exact (sf' f' g i).flip.paste_horiz sq
  exact hOuter.of_right (local_comm f f' g g' sq i) (sf f i).flip

end AlgebraicGeometry.Scheme.EtaleCohomology.Proper.AffineCoverGeometry
