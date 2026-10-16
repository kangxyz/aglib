/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Etale.FormalProperties
public import Aglib.AlgebraicGeometry.Stalk.FlatBaseChange
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
  letI : Flat g := Scheme.fromSpecStalk_flat X (f z)
  letI : IsPreimmersion g := inferInstanceAs (IsPreimmersion (X.fromSpecStalk (f z)))
  letI : Etale (Limits.pullback.snd f g) := h
  let e := Scheme.Hom.stalkMapIsoOfIsPullbackOfFlatOfPreimmersion
    (IsPullback.of_hasPullback f g) p z hp
  exact (RingHom.FormallyEtale.respectsIso.arrow_mk_iso_iff e).mpr
    (etale_stalkMap_formallyEtale (Limits.pullback.snd f g) p)

end AlgebraicGeometry.Scheme.LocalRing.Etale
