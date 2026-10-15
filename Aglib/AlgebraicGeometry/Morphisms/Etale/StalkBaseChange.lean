/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Etale.FormalProperties
public import Aglib.AlgebraicGeometry.Stalk.GenericFiber
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# Formal etaleness of stalk maps and stalk base change

The actual scheme stalk maps and pullback stalk isomorphisms transport that
property from an etale stalk-base-change morphism. Flat preimmersions provide
the canonical stalk isomorphism used by this transport. The general ring-map
properties are supplied by `Aglib.RingTheory.Etale.FormalProperties`.

Extraction source: `R5Lab.AlgebraicGeometry.LocalRing.EtaleBaseChange`
at revision `95a3772b895fbc19a81684be4ffd519d0fdcd6b3`.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry.Scheme.LocalRing.Etale

universe u

theorem etale_stalkMap_formallyEtale
    {Z X : Scheme.{u}} (f : Z ⟶ X) [Etale f] (z : Z) :
    (f.stalkMap z).hom.FormallyEtale := by
  exact HasRingHomProperty.stalkMap_of_respectsIso (P := @Etale)
    RingHom.FormallyEtale.respectsIso
    (fun f hf q _ =>
      RingHom.FormallyEtale.localRingHom rfl (RingHom.Etale.formallyEtale hf))
    inferInstance z

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
    GenericFiber.stalkMap_isIso_of_flat_of_surjectiveOnStalks g (snd p)
  haveI : IsIso (fst.stalkMap p) :=
    GenericFiber.stalkMap_isIso_of_flat_of_surjectiveOnStalks fst p
  exact Arrow.isoMk' _ _
    (TopCat.Presheaf.stalkCongr _ (.of_eq <| by rw [← hz, ← Scheme.Hom.comp_apply, h.w]; simp) ≪≫
      asIso (g.stalkMap (snd p)))
    (TopCat.Presheaf.stalkCongr _ (.of_eq <| by rw [hz]) ≪≫ asIso (fst.stalkMap p))
    (by
      subst hz
      simp [← Scheme.Hom.stalkMap_comp, ← Scheme.Hom.stalkMap_comp,
        Scheme.Hom.stalkMap_congr_hom _ _ h.w])

/-- Actual etaleness after target-stalk base change makes the original stalk
map formally etale. No flatness assumption on the original morphism is used. -/
theorem stalkMap_formallyEtale_of_etale_stalkBaseChange
    {Z X : Scheme.{u}} (f : Z ⟶ X) (z : Z)
    (h : Etale (Limits.pullback.snd f (X.fromSpecStalk (f z)))) :
    (f.stalkMap z).hom.FormallyEtale := by
  let g := X.fromSpecStalk (f z)
  let lift : Spec (Z.presheaf.stalk z) ⟶ Limits.pullback f g :=
    Limits.pullback.lift (Z.fromSpecStalk z) (Spec.map (f.stalkMap z))
      (Scheme.SpecMap_stalkMap_fromSpecStalk f).symm
  let p := lift (IsLocalRing.closedPoint (Z.presheaf.stalk z))
  have hp : Limits.pullback.fst f g p = z := by
    change (lift ≫ Limits.pullback.fst f g) (IsLocalRing.closedPoint _) = z
    rw [Limits.pullback.lift_fst]
    exact Scheme.fromSpecStalk_closedPoint
  letI : Flat g := fromSpecStalk_flat X (f z)
  letI : IsPreimmersion g := inferInstanceAs (IsPreimmersion (X.fromSpecStalk (f z)))
  letI : Etale (Limits.pullback.snd f g) := h
  let e := stalkMapIsoOfIsPullbackOfFlatOfPreimmersion (IsPullback.of_hasPullback f g) p z hp
  exact (RingHom.FormallyEtale.respectsIso.arrow_mk_iso_iff e).mpr
    (etale_stalkMap_formallyEtale (Limits.pullback.snd f g) p)

end AlgebraicGeometry.Scheme.LocalRing.Etale
