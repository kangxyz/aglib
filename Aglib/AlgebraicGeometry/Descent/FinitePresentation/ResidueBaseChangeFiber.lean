/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.ResidueBaseChangeLimit
public import Aglib.AlgebraicGeometry.Spec.CompletionResidueFiber
public import Aglib.RingTheory.Henselian.LocalTargetIdealResidue

/-!
# The original local closed fibre and the marked residue-stage limit

The limit point built from the residue fields at inverse-image primes is
canonically the original closed fibre of the coefficient base change.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.FiniteTypeResidueLimit

universe u

variable (B R : Type u) [CommRing B] [CommRing R] [Algebra B R] [IsLocalRing R]

/-- The original residue field and the prime-localization residue field have
the canonical spectrum isomorphism, with no choice of a field identification. -/
def localResidueSpecIso :
    Spec (.of (IsLocalRing.ResidueField R)) ≅
      Spec (.of (IsLocalRing.maximalIdeal R).ResidueField) :=
  Scheme.Spec.mapIso (IsLocalRing.residueFieldAtMaximalEquiv R).toCommRingCatIso.op

/-- The canonical residue spectrum isomorphism retains the coefficient map. -/
theorem localResidueSpecIso_square :
    LocalRing.residueSpecMap R ≫ Spec.algebraMap B R =
      (localResidueSpecIso R).hom ≫
        Spec.algebraMap B (IsLocalRing.maximalIdeal R).ResidueField := by
  change Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) ≫
    Spec.map (CommRingCat.ofHom (algebraMap B R)) =
    Spec.map (CommRingCat.ofHom (IsLocalRing.residueFieldAtMaximalEquiv R).toRingHom) ≫
      Spec.map (CommRingCat.ofHom
        (algebraMap B (IsLocalRing.maximalIdeal R).ResidueField))
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext b
  change IsLocalRing.residue R (algebraMap B R b) =
    IsLocalRing.residueFieldAtMaximalEquiv R
      (algebraMap B (IsLocalRing.maximalIdeal R).ResidueField b)
  rw [IsScalarTower.algebraMap_apply B R (IsLocalRing.maximalIdeal R).ResidueField b,
    IsLocalRing.residueFieldAtMaximalEquiv_algebraMap]

variable {X : Scheme.{u}} (f : X ⟶ Spec (.of B))

/-- The original closed fibre, identified with the actual residue-limit point. -/
def localClosedFiberIso :
    pullback (pullback.snd f (Spec.algebraMap B R)) (LocalRing.residueSpecMap R) ≅
      (schemeCone B R (IsLocalRing.maximalIdeal R) f).pt :=
  LocalRing.residueFiberBaseChangeIso f (Spec.algebraMap B R)
    (Spec.algebraMap B (IsLocalRing.maximalIdeal R).ResidueField)
    (LocalRing.residueSpecMap R) (localResidueSpecIso R)
    (localResidueSpecIso_square B R) ≪≫
      pullbackSymmetry f (Spec.algebraMap B (IsLocalRing.maximalIdeal R).ResidueField)

/-- The comparison retains the original projection to the coefficient model. -/
@[reassoc]
theorem localClosedFiberIso_hom_snd :
    (localClosedFiberIso B R f).hom ≫
      pullback.snd (Spec.algebraMap B (IsLocalRing.maximalIdeal R).ResidueField) f =
        pullback.fst (pullback.snd f (Spec.algebraMap B R))
          (LocalRing.residueSpecMap R) ≫ pullback.fst f (Spec.algebraMap B R) := by
  change ((LocalRing.residueFiberBaseChangeIso f (Spec.algebraMap B R)
    (Spec.algebraMap B (IsLocalRing.maximalIdeal R).ResidueField)
    (LocalRing.residueSpecMap R) (localResidueSpecIso R)
    (localResidueSpecIso_square B R)).hom ≫
      (pullbackSymmetry f
        (Spec.algebraMap B (IsLocalRing.maximalIdeal R).ResidueField)).hom) ≫ _ = _
  rw [Category.assoc, pullbackSymmetry_hom_comp_snd]
  exact LocalRing.residueFiberBaseChangeIso_hom_fst _ _ _ _ _ _

end AlgebraicGeometry.Scheme.FiniteTypeResidueLimit
