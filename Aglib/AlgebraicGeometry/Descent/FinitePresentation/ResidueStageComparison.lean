/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.ResidueBaseChangeFiber
public import Aglib.AlgebraicGeometry.Spec.LocalHenselizationTarget

/-!
# The selected henselization map is the original residue-limit projection

The canonical local-target prime-fibre map agrees with the projection of the
marked residue-field limit after its original closed-fibre comparison.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.FiniteTypeResidueLimit

universe u

open Algebra.FiniteTypeSubalgebraLimit

variable (B R : Type u) [CommRing B] [CommRing R] [Algebra B R]
  [HenselianLocalRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of B))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The local-target map retains exactly the specified stage residue map. -/
theorem selectedPrimeSpecMap_eq (s : Finset R) :
    (localResidueSpecIso R).hom ≫
      Spec.map (CommRingCat.ofHom (residueInclusion B R (IsLocalRing.maximalIdeal R) s)) =
        LocalRing.AtLocalTarget.targetPrimeResidueSpecMap (stage B R s).val.toRingHom := by
  change Spec.map (CommRingCat.ofHom (IsLocalRing.residueFieldAtMaximalEquiv R).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (residueInclusion B R (IsLocalRing.maximalIdeal R) s)) = _
  rw [← Spec.map_comp]
  exact congrArg Spec.map (congrArg CommRingCat.ofHom
    (Localization.AtLocalTarget.residueMap_eq_idealResidueMap
      (stage B R s).val.toRingHom).symm)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual selected-prime fibre map is the original limit-cone projection,
with the canonical change from model-first to base-first pullback order. -/
theorem targetPrimeFiberMap_eq_projection (s : Finset R) :
    LocalRing.AtLocalTarget.targetPrimeFiberMap (stage B R s).val.toRingHom
      (algebraMap B (stage B R s)) f ≫
      (pullbackSymmetry f
        (Spec.algebraMap B (stagePrime B R (IsLocalRing.maximalIdeal R) s).ResidueField)).hom =
    (localClosedFiberIso B R f).hom ≫
      (schemeCone B R (IsLocalRing.maximalIdeal R) f).π.app (op s) := by
  let k := Spec.algebraMap B (IsLocalRing.maximalIdeal R).ResidueField
  let ks := Spec.algebraMap B (stagePrime B R (IsLocalRing.maximalIdeal R) s).ResidueField
  have htarget_fst :
      LocalRing.AtLocalTarget.targetPrimeFiberMap (stage B R s).val.toRingHom
          (algebraMap B (stage B R s)) f ≫ pullback.fst f ks =
        pullback.fst (pullback.snd f (Spec.algebraMap B R)) (LocalRing.residueSpecMap R) ≫
          pullback.fst f (Spec.algebraMap B R) :=
    LocalRing.AtLocalTarget.targetPrimeFiberMap_fst
      (stage B R s).val.toRingHom (algebraMap B (stage B R s)) f
  have htarget_snd :
      LocalRing.AtLocalTarget.targetPrimeFiberMap (stage B R s).val.toRingHom
          (algebraMap B (stage B R s)) f ≫ pullback.snd f ks =
        pullback.snd (pullback.snd f (Spec.algebraMap B R)) (LocalRing.residueSpecMap R) ≫
          LocalRing.AtLocalTarget.targetPrimeResidueSpecMap (stage B R s).val.toRingHom :=
    LocalRing.AtLocalTarget.targetPrimeFiberMap_snd
      (stage B R s).val.toRingHom (algebraMap B (stage B R s)) f
  have hfst : (schemeCone B R (IsLocalRing.maximalIdeal R) f).π.app (op s) ≫
      pullback.fst ks f = pullback.fst k f ≫
        Spec.map (CommRingCat.ofHom
          (residueInclusion B R (IsLocalRing.maximalIdeal R) s)) :=
    pullback.lift_fst _ _ _
  have hsnd : (schemeCone B R (IsLocalRing.maximalIdeal R) f).π.app (op s) ≫
      pullback.snd ks f = pullback.snd k f := pullback.lift_snd _ _ _
  have he : (localClosedFiberIso B R f).hom ≫ pullback.fst k f =
      pullback.snd (pullback.snd f (Spec.algebraMap B R)) (LocalRing.residueSpecMap R) ≫
        (localResidueSpecIso R).hom := by
    change ((LocalRing.residueFiberBaseChangeIso f (Spec.algebraMap B R) k
      (LocalRing.residueSpecMap R) (localResidueSpecIso R)
      (localResidueSpecIso_square B R)).hom ≫ (pullbackSymmetry f k).hom) ≫ _ = _
    rw [Category.assoc, pullbackSymmetry_hom_comp_fst]
    exact LocalRing.residueFiberBaseChangeIso_hom_snd _ _ _ _ _ _
  apply pullback.hom_ext
  · rw [Category.assoc, pullbackSymmetry_hom_comp_fst,
      htarget_snd, Category.assoc, hfst,
      ← Category.assoc, he, Category.assoc, selectedPrimeSpecMap_eq]
  · rw [Category.assoc, pullbackSymmetry_hom_comp_snd,
      htarget_fst, Category.assoc, hsnd]
    exact (localClosedFiberIso_hom_snd B R f).symm

end AlgebraicGeometry.Scheme.FiniteTypeResidueLimit
