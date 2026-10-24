/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.GeometricNeighborhoodLimit
public import Aglib.AlgebraicGeometry.Spec.ResidueFiber
public import Aglib.RingTheory.Henselian.StrictHenselization.RationalResidue
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-! # The actual rational fibre of the geometric neighborhood limit

The canonical residue equivalence retains its triangle with the original
chosen point. Its base change identifies the literal proper closed fibre
with the literal original rational fibre, over the original scheme.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Finite.GeometricNeighborhood

universe u

variable (R k : Type u) [CommRing R] [Field k] [Algebra R k]
  (h : Function.Surjective (algebraMap R k))

/-- The spectrum equivalence induced by the inverse of the actual residue embedding. -/
def rationalResidueSpecIso :
    Spec (.of (IsLocalRing.ResidueField (GeometricEtaleColimit R k))) ≅ Spec (.of k) :=
  Scheme.Spec.mapIso (GeometricEtaleColimit.rationalResidueEquiv R k h).symm.toCommRingCatIso.op

/-- The actual residue map is the original point after the canonical residue identification. -/
@[reassoc (attr := simp)]
theorem rationalResidueSpecIso_point :
    (rationalResidueSpecIso R k h).hom ≫ point R k =
      LocalRing.residueSpecMap (GeometricEtaleColimit R k) := by
  change Spec.map (CommRingCat.ofHom
      (GeometricEtaleColimit.rationalResidueEquiv R k h).symm.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (GeometricEtaleColimit.residue R k).toRingHom) = _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
    GeometricEtaleColimit.rationalResidueEquiv_symm_comp_residue]

/-- The residue identification lies over the original affine base, with its chosen point. -/
@[reassoc]
theorem rationalResidueSpecIso_square :
    LocalRing.residueSpecMap (GeometricEtaleColimit R k) ≫
        Spec.algebraMap R (GeometricEtaleColimit R k) =
      (rationalResidueSpecIso R k h).hom ≫ Spec.algebraMap R k := by
  let t : Spec (.of k) ⟶ Spec (.of (GeometricEtaleColimit R k)) := point R k
  have ht : t ≫ Spec.algebraMap R (GeometricEtaleColimit R k) =
      Spec.algebraMap R k := point_structure R k
  have he : (rationalResidueSpecIso R k h).hom ≫ t =
      LocalRing.residueSpecMap (GeometricEtaleColimit R k) :=
    rationalResidueSpecIso_point R k h
  calc
    _ = ((rationalResidueSpecIso R k h).hom ≫ t) ≫
        Spec.algebraMap R (GeometricEtaleColimit R k) :=
      congrArg (fun z : Spec (.of (IsLocalRing.ResidueField (GeometricEtaleColimit R k))) ⟶
        Spec (.of (GeometricEtaleColimit R k)) =>
          z ≫ Spec.algebraMap R (GeometricEtaleColimit R k)) he.symm
    _ = (rationalResidueSpecIso R k h).hom ≫
        (t ≫ Spec.algebraMap R (GeometricEtaleColimit R k)) := Category.assoc _ _ _
    _ = _ := congrArg (fun z : Spec (.of k) ⟶ Spec (.of R) =>
      (rationalResidueSpecIso R k h).hom ≫ z) ht

variable {Y : Scheme.{u}} (p : Y ⟶ Spec (.of R))

/-- The closed fibre of the actual neighborhood-limit base change is the
literal original rational fibre, rather than an unspecified equivalent scheme. -/
def rationalResidueFiberIso :
    pullback (pullback.fst (Spec.algebraMap R (GeometricEtaleColimit R k)) p)
      (LocalRing.residueSpecMap (GeometricEtaleColimit R k)) ≅
        pullback (Spec.algebraMap R k) p :=
  pullbackSymmetry _ _ ≪≫
    pullbackRightPullbackFstIso _ _ _ ≪≫
      pullback.congrHom (rationalResidueSpecIso_square R k h) rfl ≪≫
        (pullbackRightPullbackFstIso (Spec.algebraMap R k) p
          (rationalResidueSpecIso R k h).hom).symm ≪≫
            asIso (pullback.snd (rationalResidueSpecIso R k h).hom
              (pullback.fst (Spec.algebraMap R k) p))

/-- The fibre identification preserves the original projection to the proper scheme. -/
@[reassoc (attr := simp)]
theorem rationalResidueFiberIso_hom_snd :
    (rationalResidueFiberIso R k h p).hom ≫ pullback.snd (Spec.algebraMap R k) p =
      pullback.fst (pullback.fst (Spec.algebraMap R (GeometricEtaleColimit R k)) p)
          (LocalRing.residueSpecMap (GeometricEtaleColimit R k)) ≫
        pullback.snd (Spec.algebraMap R (GeometricEtaleColimit R k)) p := by
  simp [rationalResidueFiberIso, pullback.map, pullback.lift_snd, Category.assoc]

end AlgebraicGeometry.Scheme.EtaleCohomology.Finite.GeometricNeighborhood
