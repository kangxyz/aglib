/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Quotient.Descent
public import Aglib.Algebra.Category.ModuleCat.Quotient.Unit
public import Aglib.AlgebraicGeometry.Modules.Pullback.FlatMorphism
public import Aglib.AlgebraicGeometry.Modules.Stalk.Reflection
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Nakayama

/-!
# Epimorphisms detected by a closed pullback and the complement

For the original module-sheaf map, epimorphy after the original closed
pullback and epimorphy of its original stalks off the image imply epimorphy
everywhere. Only the target stalks on the image need be finite. The source
is arbitrary, and no quasicoherence, flatness or Noetherian hypothesis is used.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Modules

private theorem epi_of_extendScalars_of_ker_le_jacobson
    {R S : Type u} [CommRing R] [CommRing S] (r : R →+* S)
    (hr : Function.Surjective r) (hJ : RingHom.ker r ≤ (⊥ : Ideal R).jacobson)
    {M N : ModuleCat.{u} R} (p : M ⟶ N) [Module.Finite R N]
    [Epi ((ModuleCat.extendScalars r).map p)] : Epi p := by
  let I := RingHom.ker r
  let P : Submodule R N := I • ⊤
  let Q : ModuleCat.{u} R := ModuleCat.of R (N ⧸ P)
  have hQ : RingHom.ker r ≤ Module.annihilator R Q := by
    intro a ha
    rw [Module.mem_annihilator]
    intro q
    exact Module.isTorsionBySet_quotient_ideal_smul N I (x := q) (a := ⟨a, ha⟩)
  obtain ⟨Q', ⟨e⟩⟩ :=
    (ModuleCat.mem_essImage_restrictScalars_iff_ker_le_annihilator r hr Q).mpr hQ
  let q : N ⟶ (ModuleCat.restrictScalars r).obj Q' := ModuleCat.ofHom P.mkQ ≫ e.inv
  let : Epi (ModuleCat.ofHom P.mkQ) :=
    (ModuleCat.epi_iff_surjective _).mpr P.mkQ_surjective
  let : Epi q := by dsimp [q]; infer_instance
  let adj := ModuleCat.extendRestrictScalarsAdj r
  let q' : (ModuleCat.extendScalars r).obj N ⟶ Q' := (adj.homEquiv N Q').symm q
  have hq : adj.unit.app N ≫ (ModuleCat.restrictScalars r).map q' = q := by
    change adj.homEquiv N Q' q' = q
    exact (adj.homEquiv N Q').apply_symm_apply q
  have : Epi (adj.unit.app N ≫ (ModuleCat.restrictScalars r).map q') := by
    rw [hq]
    infer_instance
  let : Epi ((ModuleCat.restrictScalars r).map q') :=
    epi_of_epi (adj.unit.app N) ((ModuleCat.restrictScalars r).map q')
  let : Epi (adj.unit.app M) := ModuleCat.extendRestrictScalarsAdj_unit_epi r hr M
  have hnat : p ≫ adj.unit.app N =
      adj.unit.app M ≫ (ModuleCat.restrictScalars r).map
        ((ModuleCat.extendScalars r).map p) := adj.unit.naturality p
  have hpq : Epi (p ≫ q) := by
    rw [← hq, ← Category.assoc, hnat]
    infer_instance
  have hcomp : Epi ((p ≫ ModuleCat.ofHom P.mkQ) ≫ e.inv) := by
    simpa only [q, Category.assoc] using hpq
  have hquot : Epi (p ≫ ModuleCat.ofHom P.mkQ) :=
    (epi_comp_iff_of_isIso _ _).mp hcomp
  apply (ModuleCat.epi_iff_surjective p).mpr
  apply LinearMap.surjective_of_surjective_comp_mkQ p.hom I hJ
  exact (ModuleCat.epi_iff_surjective _).mp hquot

/-- The original map is epi if its original closed pullback is epi and its
original stalks are epi off the image. Only target stalks on the image are finite. -/
theorem epi_of_pullback_closedImmersion_of_stalkFinite
    {E X : Scheme.{u}} (i : E ⟶ X) [IsClosedImmersion i]
    {M N : X.Modules} (φ : M ⟶ N)
    (hN : ∀ y : E, Module.Finite (X.presheaf.stalk (i y))
      ((moduleStalk X (i y)).obj N))
    [Epi ((pullback i).map φ)]
    (hoff : ∀ x : X, x ∉ Set.range i → Epi ((moduleStalk X x).map φ)) : Epi φ := by
  apply epi_of_moduleStalk
  intro x
  by_cases hx : x ∈ Set.range i
  · obtain ⟨y, rfl⟩ := hx
    let : Module.Finite (X.presheaf.stalk (i y)) ((moduleStalk X (i y)).obj N) := hN y
    let e := pullbackModuleStalkIso i y
    have hstalk : Epi ((moduleStalk E y).map ((pullback i).map φ)) := inferInstance
    have hscalar : Epi (e.hom.app M ≫
        (ModuleCat.extendScalars (i.stalkMap y).hom).map ((moduleStalk X (i y)).map φ)) := by
      change Epi (e.hom.app M ≫
        (moduleStalk X (i y) ⋙ ModuleCat.extendScalars (i.stalkMap y).hom).map φ)
      rw [← e.hom.naturality]
      change Epi ((moduleStalk E y).map ((pullback i).map φ) ≫ e.hom.app N)
      infer_instance
    let : Epi ((ModuleCat.extendScalars (i.stalkMap y).hom).map
        ((moduleStalk X (i y)).map φ)) := epi_of_epi (e.hom.app M) _
    apply epi_of_extendScalars_of_ker_le_jacobson (i.stalkMap y).hom
      (i.stalkMap_surjective y) ?_ ((moduleStalk X (i y)).map φ)
    exact (IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top _)).trans
      (IsLocalRing.maximalIdeal_le_jacobson _)
  · exact hoff x hx

/-- Surjectivity of the original stalk maps may be used for the complement
hypothesis, with the same finite target stalks and the same original pullback. -/
theorem epi_of_pullback_closedImmersion_of_stalkSurjective
    {E X : Scheme.{u}} (i : E ⟶ X) [IsClosedImmersion i]
    {M N : X.Modules} (φ : M ⟶ N)
    (hN : ∀ y : E, Module.Finite (X.presheaf.stalk (i y))
      ((moduleStalk X (i y)).obj N))
    [Epi ((pullback i).map φ)]
    (hoff : ∀ x : X, x ∉ Set.range i →
      Function.Surjective ((moduleStalk X x).map φ)) : Epi φ :=
  epi_of_pullback_closedImmersion_of_stalkFinite i φ hN
    (fun x hx => (ModuleCat.epi_iff_surjective _).mpr (hoff x hx))

end AlgebraicGeometry.Scheme.Modules
