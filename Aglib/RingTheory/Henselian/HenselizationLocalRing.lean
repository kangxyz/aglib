/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.Henselization

/-!
# Localness of the constructed henselization

A colimit element with nonzero residue becomes invertible in an actual
one-element localization of a pointed etale neighborhood. This proves the
native local-ring structure and identifies the maximal ideal with the kernel
of the constructed residue map. Henselianity is not an input.
-/

@[expose] public section

noncomputable section

open CategoryTheory IsLocalRing

namespace Henselization

variable (R : Type*) [CommRing R] [IsLocalRing R]

/-- A nonzero residue makes an element invertible in an actual etale
localization stage of the defining filtered diagram. -/
lemma isUnit_of_residue_ne_zero (x : Henselization R) (hx : residue R x ≠ 0) :
    IsUnit x := by
  obtain ⟨X, a, rfl⟩ := exists_rep R x
  have ha : IsUnit (X.point a) := by
    apply isUnit_iff_ne_zero.mpr
    have h := AlgHom.congr_fun (residue_comp_ι R X) a
    change residue R (ι R X a) = X.point a at h
    rwa [← h]
  let p : Localization.Away a →ₐ[R] ResidueField R :=
    IsLocalization.Away.liftAlgHom (S := Localization.Away a) (f := X.point) a ha
  have hp : p.comp (IsScalarTower.toAlgHom R X.algebra (Localization.Away a)) =
      X.point := by
    apply AlgHom.coe_ringHom_injective
    change (IsLocalization.Away.lift (S := Localization.Away a)
      (g := X.point.toRingHom) a ha).comp (algebraMap X.algebra (Localization.Away a)) =
        X.point.toRingHom
    exact IsLocalization.Away.lift_comp (S := Localization.Away a)
      (g := X.point.toRingHom) a ha
  obtain ⟨Y, e, he⟩ := PointedEtaleNeighborhood.exists_equiv (Localization.Away a) p
  let f : X ⟶ Y :=
    ⟨e.toAlgHom.comp (IsScalarTower.toAlgHom R X.algebra (Localization.Away a)), by
      rw [← AlgHom.comp_assoc, he, hp]⟩
  have hu : IsUnit (ι R Y (e (algebraMap X.algebra (Localization.Away a) a))) :=
    ((IsLocalization.Away.algebraMap_isUnit a).map e.toRingHom).map (ι R Y).toRingHom
  have h := AlgHom.congr_fun (ι_naturality f) a
  change ι R Y (e (algebraMap X.algebra (Localization.Away a) a)) = ι R X a at h
  exact h ▸ hu

/-- Units of the actual henselization colimit are exactly the elements with
nonzero image under its constructed residue-valued map. -/
lemma isUnit_iff_residue_ne_zero (x : Henselization R) :
    IsUnit x ↔ residue R x ≠ 0 :=
  ⟨fun hx => isUnit_iff_ne_zero.mp (hx.map (residue R).toRingHom),
    isUnit_of_residue_ne_zero R x⟩

instance residue_isLocalHom : IsLocalHom (residue R).toRingHom where
  map_nonunit x hx := isUnit_of_residue_ne_zero R x (isUnit_iff_ne_zero.mp hx)

instance : IsLocalRing (Henselization R) :=
  (residue R).toRingHom.domain_isLocalRing

/-- The native maximal ideal is the kernel of the constructed residue map. -/
lemma maximalIdeal_eq_ker_residue :
    maximalIdeal (Henselization R) = RingHom.ker (residue R).toRingHom := by
  ext x
  simp only [mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_residue_ne_zero,
    RingHom.mem_ker, not_not]
  rfl

instance algebraMap_isLocalHom : IsLocalHom (algebraMap R (Henselization R)) where
  map_nonunit r hr := by
    apply (IsLocalRing.residue_ne_zero_iff_isUnit r).mp
    have h := (isUnit_iff_residue_ne_zero R (algebraMap R (Henselization R) r)).mp hr
    change residue R (of R r) ≠ 0 at h
    rwa [show residue R (of R r) = IsLocalRing.residue R r from
      RingHom.congr_fun (residue_comp_of R) r] at h

end Henselization
