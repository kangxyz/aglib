/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Spec.CompletionSpecialization
public import Aglib.RingTheory.Henselian.LocalTargetResidue

/-!
# The literal fibre of a selected local henselization

The henselization selected by an actual map to a henselian local ring has
the original residue field at its selected prime. Applying the canonical
pullback comparison identifies its literal closed fibre with that original
prime fibre, preserving both structure maps.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.LocalRing.AtLocalTarget

universe u

variable {S B R : Type u} [CommRing S] [CommRing B] [CommRing R] [HenselianLocalRing R]
  (a : B →+* R) (b : S →+* B)

local notation "Aₚ" => Localization.AtLocalTarget.Ring a
local notation "H" => Henselization.AtLocalTarget.Ring a

/-- The actual selected henselization coefficient map on spectra. -/
abbrev henselizationSpecMap : Spec (.of H) ⟶ Spec (.of S) :=
  Spec.map (CommRingCat.ofHom ((Henselization.AtLocalTarget.of a).comp b))

/-- The original target coefficient map on spectra. -/
abbrev targetSpecMap : Spec (.of R) ⟶ Spec (.of S) :=
  Spec.map (CommRingCat.ofHom (a.comp b))

/-- The actual local map from the selected henselization to the target,
contravariantly on spectra. -/
abbrev targetToHenselizationSpecMap : Spec (.of R) ⟶ Spec (.of H) :=
  Spec.map (CommRingCat.ofHom (Henselization.AtLocalTarget.map a))

/-- The original residue point at the selected prime. -/
abbrev primeResidueSpecMap : Spec (.of (IsLocalRing.ResidueField Aₚ)) ⟶ Spec (.of S) :=
  Spec.map (CommRingCat.ofHom ((algebraMap B (IsLocalRing.ResidueField Aₚ)).comp b))

/-- The canonical spectrum isomorphism of the two actual residue fields. -/
def henselizationResidueSpecIso :
    Spec (.of (IsLocalRing.ResidueField H)) ≅ Spec (.of (IsLocalRing.ResidueField Aₚ)) :=
  Scheme.Spec.mapIso (Henselization.residueEquiv Aₚ).symm.toCommRingCatIso.op

@[reassoc (attr := simp)]
theorem targetToHenselizationSpecMap_comp :
    targetToHenselizationSpecMap a ≫ henselizationSpecMap a b = targetSpecMap a b := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  exact congrArg CommRingCat.ofHom (RingHom.ext fun s =>
    Henselization.AtLocalTarget.map_of a (b s))

/-- The residue isomorphism retains the original coefficient square. -/
@[reassoc]
theorem henselizationResidueSpecIso_square :
    residueSpecMap H ≫ henselizationSpecMap a b =
      (henselizationResidueSpecIso a).hom ≫ primeResidueSpecMap a b := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  exact congrArg CommRingCat.ofHom (RingHom.ext fun s =>
    (Henselization.residueEquiv_symm_residue Aₚ (algebraMap B Aₚ (b s))).symm)

variable {X : Scheme.{u}} (f : X ⟶ Spec (.of S))

/-- The literal base change to the selected local henselization. -/
abbrev henselizationBaseChange : Scheme.{u} := pullback f (henselizationSpecMap a b)

/-- The literal base change to the original target ring. -/
abbrev targetBaseChange : Scheme.{u} := pullback f (targetSpecMap a b)

/-- The literal original fibre at the selected prime. -/
abbrev primeFiber : Scheme.{u} := pullback f (primeResidueSpecMap a b)

/-- The closed fibre of the actual henselization base change is canonically
the original prime fibre. -/
def henselizationFiberIso :
    pullback (pullback.snd f (henselizationSpecMap a b)) (residueSpecMap H) ≅
      primeFiber a b f :=
  residueFiberBaseChangeIso f (henselizationSpecMap a b) (primeResidueSpecMap a b)
    (residueSpecMap H) (henselizationResidueSpecIso a) (henselizationResidueSpecIso_square a b)

@[reassoc (attr := simp)]
theorem henselizationFiberIso_hom_fst :
    (henselizationFiberIso a b f).hom ≫ pullback.fst f (primeResidueSpecMap a b) =
      pullback.fst (pullback.snd f (henselizationSpecMap a b)) (residueSpecMap H) ≫
        pullback.fst f (henselizationSpecMap a b) :=
  residueFiberBaseChangeIso_hom_fst _ _ _ _ _ _

@[reassoc (attr := simp)]
theorem henselizationFiberIso_hom_snd :
    (henselizationFiberIso a b f).hom ≫ pullback.snd f (primeResidueSpecMap a b) =
      pullback.snd (pullback.snd f (henselizationSpecMap a b)) (residueSpecMap H) ≫
        (henselizationResidueSpecIso a).hom :=
  residueFiberBaseChangeIso_hom_snd _ _ _ _ _ _

end AlgebraicGeometry.Scheme.LocalRing.AtLocalTarget
