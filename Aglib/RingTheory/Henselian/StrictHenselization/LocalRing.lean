/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.StrictHenselization.Colimit
public import Mathlib.RingTheory.LocalRing.Basic

/-!
# Localness of the geometric etale-neighborhood colimit

A colimit element with nonzero residue becomes invertible in an actual
one-element localization of a pointed etale neighborhood. This proves the
native local-ring structure and identifies the maximal ideal with the kernel
of the constructed residue map. Henselianity is not an input.
-/

@[expose] public section

noncomputable section

open CategoryTheory IsLocalRing

namespace GeometricEtaleColimit

universe u

variable (R : Type u) [CommRing R] (Ω : Type u) [Field Ω] [Algebra R Ω]

/-- A nonzero residue makes an element invertible in an actual etale
localization stage of the defining filtered diagram. -/
lemma isUnit_of_residue_ne_zero (x : GeometricEtaleColimit R Ω) (hx : residue R Ω x ≠ 0) :
    IsUnit x := by
  obtain ⟨X, a, rfl⟩ := exists_rep R Ω x
  have ha : IsUnit (X.point a) := by
    apply isUnit_iff_ne_zero.mpr
    have h := AlgHom.congr_fun (residue_comp_ι R Ω X) a
    change residue R Ω (ι R Ω X a) = X.point a at h
    rwa [← h]
  let p : Localization.Away a →ₐ[R] Ω :=
    IsLocalization.Away.liftAlgHom (S := Localization.Away a) (f := X.point) a ha
  have hp : p.comp (IsScalarTower.toAlgHom R X.algebra (Localization.Away a)) =
      X.point := by
    apply AlgHom.coe_ringHom_injective
    change (IsLocalization.Away.lift (S := Localization.Away a)
      (g := X.point.toRingHom) a ha).comp (algebraMap X.algebra (Localization.Away a)) =
        X.point.toRingHom
    exact IsLocalization.Away.lift_comp (S := Localization.Away a)
      (g := X.point.toRingHom) a ha
  obtain ⟨Y, e, he⟩ := GeometricEtaleNeighborhood.exists_equiv (Localization.Away a) p
  let f : X ⟶ Y :=
    ⟨e.toAlgHom.comp (IsScalarTower.toAlgHom R X.algebra (Localization.Away a)), by
      rw [← AlgHom.comp_assoc, he, hp]⟩
  have hu : IsUnit (ι R Ω Y (e (algebraMap X.algebra (Localization.Away a) a))) :=
    ((IsLocalization.Away.algebraMap_isUnit a).map e.toRingHom).map (ι R Ω Y).toRingHom
  have h := AlgHom.congr_fun (ι_naturality f) a
  change ι R Ω Y (e (algebraMap X.algebra (Localization.Away a) a)) = ι R Ω X a at h
  exact h ▸ hu

/-- Units of the actual geometric neighborhood colimit are exactly the elements with
nonzero image under its constructed residue-valued map. -/
lemma isUnit_iff_residue_ne_zero (x : GeometricEtaleColimit R Ω) :
    IsUnit x ↔ residue R Ω x ≠ 0 :=
  ⟨fun hx => isUnit_iff_ne_zero.mp (hx.map (residue R Ω).toRingHom),
    isUnit_of_residue_ne_zero R Ω x⟩

instance residue_isLocalHom : IsLocalHom (residue R Ω).toRingHom where
  map_nonunit x hx := isUnit_of_residue_ne_zero R Ω x (isUnit_iff_ne_zero.mp hx)

instance : IsLocalRing (GeometricEtaleColimit R Ω) :=
  (residue R Ω).toRingHom.domain_isLocalRing

/-- The native maximal ideal is the kernel of the constructed residue map. -/
lemma maximalIdeal_eq_ker_residue :
    maximalIdeal (GeometricEtaleColimit R Ω) = RingHom.ker (residue R Ω).toRingHom := by
  ext x
  simp only [mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_residue_ne_zero,
    RingHom.mem_ker, not_not]
  rfl

end GeometricEtaleColimit
