/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Spec.LocalHenselizationFiber

/-!
# The original target fibre and a selected local henselization

The actual local map from a selected henselization to the target induces
maps of the direct coefficient base changes and their literal closed fibres.
The final prime-fibre map retains the original residue-field marking.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.LocalRing.AtLocalTarget

universe u

variable {S B R : Type u} [CommRing S] [CommRing B] [CommRing R] [HenselianLocalRing R]
  (a : B →+* R) (b : S →+* B)

local notation "H" => Henselization.AtLocalTarget.Ring a

/-- The actual map between the residue spectra of the target and the
selected henselization. -/
abbrev targetHenselizationResidueSpecMap :
    Spec (.of (IsLocalRing.ResidueField R)) ⟶ Spec (.of (IsLocalRing.ResidueField H)) :=
  Spec.map (CommRingCat.ofHom
    (IsLocalRing.ResidueField.map (Henselization.AtLocalTarget.map a)))

/-- The original selected-prime residue map into the target residue field,
contravariantly on spectra. -/
abbrev targetPrimeResidueSpecMap :
    Spec (.of (IsLocalRing.ResidueField R)) ⟶
      Spec (.of (IsLocalRing.ResidueField (Localization.AtLocalTarget.Ring a))) :=
  Spec.map (CommRingCat.ofHom
    (IsLocalRing.ResidueField.map (Localization.AtLocalTarget.map a)))

@[reassoc]
theorem targetHenselizationResidueSpecMap_square :
    residueSpecMap R ≫ targetToHenselizationSpecMap a =
      targetHenselizationResidueSpecMap a ≫ residueSpecMap H := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  rfl

@[reassoc (attr := simp)]
theorem targetHenselizationResidueSpecMap_comp :
    targetHenselizationResidueSpecMap a ≫ (henselizationResidueSpecIso a).hom =
      targetPrimeResidueSpecMap a := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  exact congrArg CommRingCat.ofHom
    (Henselization.AtLocalTarget.residueMap_comp_residueEquiv_symm a)

variable {X : Scheme.{u}} (f : X ⟶ Spec (.of S))

/-- The original target base change maps to the selected henselization base
change through the actual local coefficient map. -/
def targetBaseChangeMap : targetBaseChange a b f ⟶ henselizationBaseChange a b f :=
  pullback.lift (pullback.fst f (targetSpecMap a b))
    (pullback.snd f (targetSpecMap a b) ≫ targetToHenselizationSpecMap a) (by
      rw [Category.assoc, targetToHenselizationSpecMap_comp]
      exact pullback.condition)

@[reassoc (attr := simp)]
theorem targetBaseChangeMap_fst :
    targetBaseChangeMap a b f ≫ pullback.fst f (henselizationSpecMap a b) =
      pullback.fst f (targetSpecMap a b) := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem targetBaseChangeMap_snd :
    targetBaseChangeMap a b f ≫ pullback.snd f (henselizationSpecMap a b) =
      pullback.snd f (targetSpecMap a b) ≫ targetToHenselizationSpecMap a :=
  pullback.lift_snd _ _ _

/-- The actual map between the two literal closed fibres. -/
def targetClosedFiberMap :
    pullback (pullback.snd f (targetSpecMap a b)) (residueSpecMap R) ⟶
      pullback (pullback.snd f (henselizationSpecMap a b)) (residueSpecMap H) :=
  pullback.lift
    (pullback.fst (pullback.snd f (targetSpecMap a b)) (residueSpecMap R) ≫
      targetBaseChangeMap a b f)
    (pullback.snd (pullback.snd f (targetSpecMap a b)) (residueSpecMap R) ≫
      targetHenselizationResidueSpecMap a) (by
      simp only [Category.assoc, targetBaseChangeMap_snd, pullback.condition_assoc,
        targetHenselizationResidueSpecMap_square])

@[reassoc (attr := simp)]
theorem targetClosedFiberMap_fst :
    targetClosedFiberMap a b f ≫
        pullback.fst (pullback.snd f (henselizationSpecMap a b)) (residueSpecMap H) =
      pullback.fst (pullback.snd f (targetSpecMap a b)) (residueSpecMap R) ≫
        targetBaseChangeMap a b f := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem targetClosedFiberMap_snd :
    targetClosedFiberMap a b f ≫
        pullback.snd (pullback.snd f (henselizationSpecMap a b)) (residueSpecMap H) =
      pullback.snd (pullback.snd f (targetSpecMap a b)) (residueSpecMap R) ≫
        targetHenselizationResidueSpecMap a := pullback.lift_snd _ _ _

/-- The canonical map from the original target closed fibre to the selected
prime fibre of the original coefficient model. -/
def targetPrimeFiberMap :
    pullback (pullback.snd f (targetSpecMap a b)) (residueSpecMap R) ⟶ primeFiber a b f :=
  targetClosedFiberMap a b f ≫ (henselizationFiberIso a b f).hom

@[reassoc (attr := simp)]
theorem targetPrimeFiberMap_fst :
    targetPrimeFiberMap a b f ≫ pullback.fst f (primeResidueSpecMap a b) =
      pullback.fst (pullback.snd f (targetSpecMap a b)) (residueSpecMap R) ≫
        pullback.fst f (targetSpecMap a b) := by
  simp only [targetPrimeFiberMap, Category.assoc, henselizationFiberIso_hom_fst,
    targetClosedFiberMap_fst_assoc, targetBaseChangeMap_fst]

@[reassoc (attr := simp)]
theorem targetPrimeFiberMap_snd :
    targetPrimeFiberMap a b f ≫ pullback.snd f (primeResidueSpecMap a b) =
      pullback.snd (pullback.snd f (targetSpecMap a b)) (residueSpecMap R) ≫
        targetPrimeResidueSpecMap a := by
  simp only [targetPrimeFiberMap, Category.assoc, henselizationFiberIso_hom_snd,
    targetClosedFiberMap_snd_assoc, targetHenselizationResidueSpecMap_comp]

end AlgebraicGeometry.Scheme.LocalRing.AtLocalTarget
