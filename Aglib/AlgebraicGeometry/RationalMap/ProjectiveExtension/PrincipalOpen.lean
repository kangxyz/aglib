/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.RationalMap.ProjectiveExtension.AffineAgreement

/-!
# Projective extension from a principal affine open

The prescribed principal open has its actual canonical lift to the
coordinate-ideal blowup. The construction retains the original localized
coordinates and the actual structural triangle. No domain hypothesis occurs.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.ProjectiveSpace.FromSections
open IsLocalization.Away

universe u

namespace AlgebraicGeometry.Scheme.RationalCoordinates

variable (A : Type u) [CommRing A] {I : Type u} [Finite I]
variable (f : A) (n : ℕ) (a : I → A)

/-- The original principal open lifts canonically through the actual
coordinate blowup, by the inverse of the native pullback projection. -/
def principalCoordinateLift : Spec (.of (Localization.Away f)) ⟶
    (Blowup.blowupDatum (Blowup.affineCenter A (principalCoordinateIdeal f n a))).Y :=
  ((Blowup.blowupDatum _).awayPullbackIso
    (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f))))
    (principalCoordinateCenter_comap_eq_top A f n a)).inv ≫ pullback.fst _ _

instance principalCoordinateLift_isOpenImmersion :
    IsOpenImmersion (principalCoordinateLift A f n a) := by
  unfold principalCoordinateLift
  infer_instance

omit [Finite I] in
@[reassoc]
theorem principalCoordinateLift_map :
    principalCoordinateLift A f n a ≫
      (Blowup.blowupDatum (Blowup.affineCenter A (principalCoordinateIdeal f n a))).map =
    Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f))) := by
  unfold principalCoordinateLift
  rw [Category.assoc, pullback.condition]
  exact Iso.inv_hom_id_assoc _ _

omit [Finite I] in
/-- The whole lifted principal open, not only its generic point, is a unit
locus for the actual image ideal on the blowup. -/
theorem principalCoordinateLift_comap_eq_top :
    ((Blowup.affineCenter A (principalCoordinateIdeal f n a)).comap
      (Blowup.blowupDatum (Blowup.affineCenter A (principalCoordinateIdeal f n a))).map).comap
      (principalCoordinateLift A f n a) = ⊤ := by
  rw [← IdealSheafData.comap_comp, principalCoordinateLift_map]
  exact principalCoordinateCenter_comap_eq_top A f n a

omit [Finite I] in
/-- Each coordinate after restriction is the image of the original homogeneous
coordinate under the actual localization ring map. -/
theorem principalCoordinateLift_scalar (i : Option I) :
    affineRestrictedScalar A (principalHomogeneousCoordinates f n a)
      (principalCoordinateLift A f n a) i =
    Blowup.IdealFrames.affineMultiplication (Localization.Away f)
      (algebraMap A (Localization.Away f) (principalHomogeneousCoordinates f n a i)) := by
  exact (congrArg (fun q : Spec (.of (Localization.Away f)) ⟶ Spec (.of A) ↦
    pullbackUnitEnd q (Blowup.IdealFrames.affineMultiplication A
      (principalHomogeneousCoordinates f n a i)))
    (principalCoordinateLift_map A f n a)).trans
      (pullbackUnitEnd_affine (algebraMap A (Localization.Away f)) _)

variable {S : Type u} [CommRing S]

/-- The original affine tuple, with its distinguished coordinate exactly one. -/
def affineTupleSection (s : I → S) (i : Option I) :=
  Blowup.IdealFrames.affineMultiplication S (Option.elim i 1 s)

instance affineTupleSection_epi (s : I → S) :
    Epi (Sigma.desc (affineTupleSection s)) := by
  have h : Sigma.ι (fun _ : Option I ↦ SheafOfModules.unit (Spec (.of S)).ringCatSheaf) none ≫
      Sigma.desc (affineTupleSection s) = 𝟙 _ := by
    rw [Sigma.ι_comp_desc]
    simp only [affineTupleSection, Option.elim_none,
      Blowup.IdealFrames.affineMultiplication_eq_unitMul, map_one, unitMul_one]
  exact epi_of_epi_fac h

variable {R : Type u} [CommRing R] (p : Spec (.of A) ⟶ Spec (.of R))

/-- The canonical projective map agrees with the original affine coordinate
tuple over the whole prescribed principal open. The only scalar equation
required is the literal common-denominator identity. -/
theorem principalCoordinateBlowupMap_agrees (s : I → Localization.Away f)
    (h : ∀ i, algebraMap A (Localization.Away f) (principalHomogeneousCoordinates f n a i) =
      algebraMap A (Localization.Away f) f ^ n * Option.elim i 1 s) :
    letI : Epi (Sigma.desc (affineTupleSection s)) := affineTupleSection_epi s
    principalCoordinateLift A f n a ≫
      affineCoordinateBlowupMap A (principalHomogeneousCoordinates f n a) p =
    mapOfFiniteFamily
      (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f))) ≫ p)
      (SheafOfModules.unit (Spec (.of (Localization.Away f))).ringCatSheaf)
      (affineUnit_locallyRankOne (Localization.Away f)) (affineTupleSection s) := by
  let : Epi (Sigma.desc (affineTupleSection s)) := affineTupleSection_epi s
  let j := principalCoordinateLift A f n a
  let v := principalHomogeneousCoordinates f n a
  let : Epi (Sigma.desc (affineRestrictedScalar A v j)) :=
    affineRestrictedScalar_epi A v j (principalCoordinateLift_comap_eq_top A f n a)
  rw [affineCoordinateBlowupMap_restrict A v p j
    (principalCoordinateLift_comap_eq_top A f n a)]
  have hp : j ≫ (Blowup.blowupDatum
      (Blowup.affineCenter A (affineCoordinateIdeal A v))).map ≫ p =
      Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f))) ≫ p :=
    (Category.assoc _ _ _).symm.trans
      (congrArg (fun q ↦ q ≫ p) (principalCoordinateLift_map A f n a))
  have hbase := congrArg (fun q : Spec (.of (Localization.Away f)) ⟶ Spec (.of R) ↦
    mapOfFiniteFamily q (SheafOfModules.unit (Spec (.of (Localization.Away f))).ringCatSheaf)
      (affineUnit_locallyRankOne (Localization.Away f)) (affineRestrictedScalar A v j)) hp
  refine hbase.trans ?_
  symm
  let d : (Localization.Away f)ˣ :=
    ((IsLocalization.Away.algebraMap_isUnit f).pow n).unit
  let e := unitMulIso (Spec (.of (Localization.Away f)))
    (Units.map (Scheme.ΓSpecIso (.of (Localization.Away f))).inv.hom.toMonoidHom d)
  apply mapOfFiniteFamily_iso _ _ _ _ _ _ _ e
  intro i
  change affineTupleSection s i ≫ unitMul _
    ((Scheme.ΓSpecIso (.of (Localization.Away f))).inv (↑d)) =
      affineRestrictedScalar A v j i
  rw [← Blowup.IdealFrames.affineMultiplication_eq_unitMul,
    principalCoordinateLift_scalar]
  rw [affineTupleSection, Blowup.IdealFrames.affineMultiplication_comp, h i]
  congr 1
  rw [show (↑d : Localization.Away f) = algebraMap A (Localization.Away f) f ^ n from
    IsUnit.unit_spec _]
  exact mul_comm _ _

/-- Existence of actual homogeneous coordinates and agreement, for every
finite family on the original principal open. No denominator or agreement
assumption remains. -/
theorem exists_principalCoordinateBlowupMap_agrees (s : I → Localization.Away f) :
    letI : Epi (Sigma.desc (affineTupleSection s)) := affineTupleSection_epi s
    ∃ (n : ℕ) (a : I → A),
      principalCoordinateLift A f n a ≫
        affineCoordinateBlowupMap A (principalHomogeneousCoordinates f n a) p =
      mapOfFiniteFamily
        (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f))) ≫ p)
        (SheafOfModules.unit (Spec (.of (Localization.Away f))).ringCatSheaf)
        (affineUnit_locallyRankOne (Localization.Away f)) (affineTupleSection s) := by
  let : Epi (Sigma.desc (affineTupleSection s)) := affineTupleSection_epi s
  obtain ⟨n, a, h, _⟩ := exists_principal_homogeneous_coordinates f s
  exact ⟨n, a, principalCoordinateBlowupMap_agrees A f n a p s h⟩

end AlgebraicGeometry.Scheme.RationalCoordinates
