/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Stalk.FlatBaseChange
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective

/-!
# Detecting isomorphisms on actual local-spectrum base changes

Closedness gives the topological homeomorphism after bijectivity is proved
from the original local squares. Flat localization preserves the actual
stalk-map arrows. No finite-presentation or normality assumption is needed.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

/-- A closed scheme map is an isomorphism if its base changes to all original
target stalk spectra are isomorphisms. -/
theorem isIso_of_isClosedMap_of_stalkPullback {X Y : Scheme.{u}}
    (f : X ⟶ Y) (hclosed : IsClosedMap f)
    (hlocal : ∀ y : Y, IsIso (pullback.snd f (Y.fromSpecStalk y))) : IsIso f := by
  have hsurj : Function.Surjective f := by
    intro y
    let s := Y.fromSpecStalk y
    let q := pullback.snd f s
    let : IsIso q := hlocal y
    obtain ⟨z, hz⟩ := q.surjective (IsLocalRing.closedPoint (Y.presheaf.stalk y))
    refine ⟨pullback.fst f s z, ?_⟩
    have H := congrArg (fun k : pullback f s ⟶ Y => k z) (pullback.condition (f := f) (g := s))
    change f (pullback.fst f s z) = s (q z) at H
    rw [hz] at H
    simpa only [s, Scheme.fromSpecStalk_closedPoint] using H
  have hinj : Function.Injective f := by
    intro x z hxz
    let s := Y.fromSpecStalk (f x)
    let q := pullback.snd f s
    let : IsIso q := hlocal (f x)
    obtain ⟨x', hx', hqx⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := s) x
      (IsLocalRing.closedPoint (Y.presheaf.stalk (f x)))
      (Scheme.fromSpecStalk_closedPoint (X := Y) (x := f x)).symm
    obtain ⟨z', hz', hqz⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := s) z
      (IsLocalRing.closedPoint (Y.presheaf.stalk (f x)))
      (hxz.symm.trans (Scheme.fromSpecStalk_closedPoint (X := Y) (x := f x)).symm)
    have he : x' = z' := q.injective (hqx.trans hqz.symm)
    exact hx'.symm.trans ((congrArg (pullback.fst f s) he).trans hz')
  apply (isIso_iff_isIso_stalkMap f).mpr
  refine ⟨?_, fun x => ?_⟩
  · apply (TopCat.isIso_iff_isHomeomorph f.base).mpr
    exact isHomeomorph_iff_continuous_isClosedMap_bijective.mpr
      ⟨f.continuous, hclosed, hinj, hsurj⟩
  · let s := Y.fromSpecStalk (f x)
    let : Flat s := Scheme.fromSpecStalk_flat Y (f x)
    let : IsIso (pullback.snd f s) := hlocal (f x)
    obtain ⟨z, hz, _⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := s) x
      (IsLocalRing.closedPoint (Y.presheaf.stalk (f x)))
      (Scheme.fromSpecStalk_closedPoint (X := Y) (x := f x)).symm
    exact ((MorphismProperty.isomorphisms CommRingCat).arrow_mk_iso_iff
      (Hom.stalkMapIsoOfIsPullbackOfFlatOfPreimmersion
        (IsPullback.of_hasPullback f s) z x hz)).mpr inferInstance

/-- A further base change preserves invertibility of the original structural
projection, with the native pullback associativity comparison. -/
theorem isIso_pullback_snd_comp {X Y S T : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (h : T ⟶ Y)
    [IsIso (pullback.snd f g)] : IsIso (pullback.snd f (h ≫ g)) := by
  rw [← pullbackLeftPullbackSndIso_inv_snd_snd f g h]
  infer_instance

/-- For a closed map over a base, testing all local spectra of that original
base suffices. The projection is a model localization, not a stalk spectrum
of the model. -/
theorem isIso_of_isClosedMap_of_baseStalkPullback {X Y S : Scheme.{u}}
    (f : X ⟶ Y) (b : Y ⟶ S) (hclosed : IsClosedMap f)
    (hlocal : ∀ s : S,
      IsIso (pullback.snd f (pullback.fst b (S.fromSpecStalk s)))) : IsIso f := by
  apply isIso_of_isClosedMap_of_stalkPullback f hclosed
  intro y
  let c := S.fromSpecStalk (b y)
  let k : Spec (Y.presheaf.stalk y) ⟶ pullback b c :=
    pullback.lift (Y.fromSpecStalk y) (Spec.map (b.stalkMap y))
      (Scheme.SpecMap_stalkMap_fromSpecStalk b (x := y)).symm
  let : IsIso (pullback.snd f (pullback.fst b c)) := hlocal (b y)
  have H := isIso_pullback_snd_comp f (pullback.fst b c) k
  have hk : k ≫ pullback.fst b c = Y.fromSpecStalk y := pullback.lift_fst ..
  rw [hk] at H
  exact H

/-- The original map between two base-changed models has its expected
cartesian square, retaining the supplied structural equality. -/
theorem isPullback_overBaseChange {X Y S T : Scheme.{u}}
    (f : X ⟶ Y) (b : Y ⟶ S) (p : X ⟶ S) (hfb : f ≫ b = p) (c : T ⟶ S) :
    IsPullback (pullback.fst p c)
      (pullback.map p c b c f (𝟙 T) (𝟙 S) (by simpa using hfb.symm) (by simp))
      f (pullback.fst b c) := by
  let k := pullback.map p c b c f (𝟙 T) (𝟙 S) (by simpa using hfb.symm) (by simp)
  have H : IsPullback (pullback.fst p c) (k ≫ pullback.snd b c) (f ≫ b) c := by
    simpa only [k, pullback.map, pullback.lift_snd, Category.comp_id, hfb] using
      (IsPullback.of_hasPullback p c)
  exact H.of_bot (by dsimp only [k, pullback.map]; rw [pullback.lift_fst])
    (IsPullback.of_hasPullback b c)

/-- Invertibility of the map of base-changed models is invertibility of the
literal base-change structural projection. -/
theorem isIso_pullback_snd_of_overBaseChange {X Y S T : Scheme.{u}}
    (f : X ⟶ Y) (b : Y ⟶ S) (p : X ⟶ S) (hfb : f ≫ b = p) (c : T ⟶ S)
    (hk : IsIso
      (pullback.map p c b c f (𝟙 T) (𝟙 S) (by simpa using hfb.symm) (by simp))) :
    IsIso (pullback.snd f (pullback.fst b c)) := by
  let := hk
  rw [← (isPullback_overBaseChange f b p hfb c).isoPullback_inv_snd]
  infer_instance

end AlgebraicGeometry.Scheme
