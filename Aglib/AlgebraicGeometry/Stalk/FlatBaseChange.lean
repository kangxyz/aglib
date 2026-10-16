/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.Tactic.Algebraize

/-!
# Flat stalk maps and actual base change

Flatness with surjectivity on stalks makes the actual stalk map an isomorphism.
The canonical map from a stalk spectrum is flat. A supplied pullback square
with flat preimmersion base map gives an isomorphism of the original stalk-map
arrows, including the specified point and its equality.

Source at 451aeda6b8bb5b44402b574dd6cf60f912360f8c:
Aglib/AlgebraicGeometry/Stalk/GenericFiber.lean:34–44 and
Aglib/AlgebraicGeometry/Morphisms/Etale/StalkBaseChange.lean:48–83.
Only the approved native owners/names and their internal references change.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- Flatness and surjectivity on stalks make each actual local homomorphism an iso. -/
theorem isIso_stalkMap_of_flat_of_surjectiveOnStalks
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [SurjectiveOnStalks f] (x : X) :
    IsIso (f.stalkMap x) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨?_, f.stalkMap_surjective x⟩
  algebraize [(f.stalkMap x).hom]
  have : Module.FaithfullyFlat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
      (Flat.stalkMap f x) (f.toLRSHom.prop x)
  exact ‹RingHom.FaithfullyFlat _›.injective

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme

/-- The actual canonical target localization is flat. -/
theorem fromSpecStalk_flat (X : Scheme.{u}) (x : X) : Flat (X.fromSpecStalk x) := by
  obtain ⟨U, hU, hxU, _⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
    (Opens.mem_top x)
  rw [← hU.fromSpecStalk_eq_fromSpecStalk hxU]
  letI : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hxU).hom.toAlgebra
  letI := hU.isLocalization_stalk ⟨x, hxU⟩
  letI : Module.Flat Γ(X, U) (X.presheaf.stalk x) :=
    IsLocalization.flat (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
  haveI : Flat (Spec.map (X.presheaf.germ U x hxU)) := by
    apply Flat.SpecMap_iff.mpr
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  dsimp only [IsAffineOpen.fromSpecStalk]
  infer_instance

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.Hom

/-- A flat preimmersion base change preserves the actual local ring map.
This is the same commutative stalk square as for open immersions. -/
def stalkMapIsoOfIsPullbackOfFlatOfPreimmersion {P Z Y X : Scheme.{u}}
    {fst : P ⟶ Z} {snd : P ⟶ Y} {f : Z ⟶ X} {g : Y ⟶ X}
    (h : IsPullback fst snd f g) [Flat g] [IsPreimmersion g]
    (p : P) (z : Z := fst p) (hz : fst p = z := by cat_disch) :
    Arrow.mk (f.stalkMap z) ≅ Arrow.mk (snd.stalkMap p) := by
  haveI : Flat fst := MorphismProperty.of_isPullback h.flip ‹_›
  haveI : IsPreimmersion fst := MorphismProperty.of_isPullback h.flip ‹_›
  haveI : IsIso (g.stalkMap (snd p)) :=
    isIso_stalkMap_of_flat_of_surjectiveOnStalks g (snd p)
  haveI : IsIso (fst.stalkMap p) :=
    isIso_stalkMap_of_flat_of_surjectiveOnStalks fst p
  exact Arrow.isoMk' _ _
    (TopCat.Presheaf.stalkCongr _ (.of_eq <| by rw [← hz, ← Scheme.Hom.comp_apply, h.w]; simp) ≪≫
      asIso (g.stalkMap (snd p)))
    (TopCat.Presheaf.stalkCongr _ (.of_eq <| by rw [hz]) ≪≫ asIso (fst.stalkMap p))
    (by
      subst hz
      simp [← Scheme.Hom.stalkMap_comp, ← Scheme.Hom.stalkMap_comp,
        Scheme.Hom.stalkMap_congr_hom _ _ h.w])

end AlgebraicGeometry.Scheme.Hom
