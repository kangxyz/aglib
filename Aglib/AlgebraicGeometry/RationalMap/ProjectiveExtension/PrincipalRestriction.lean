/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.RationalMap.ProjectiveExtension.PrincipalAffineChart
public import Aglib.AlgebraicGeometry.ProjectiveSpace.FromSections.AffineTuple
public import Aglib.AlgebraicGeometry.Blowup.Admissible

/-!
# Agreement on the entire inverse image of a principal open

The canonical localization lift is identified with the actual restriction
isomorphism of the coordinate blowup. Consequently its coordinate agreement
holds on the whole protected open subscheme, with the original sections.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ProjectiveSpace.FromSections
open IsLocalization.Away

universe u

namespace AlgebraicGeometry.Scheme.RationalCoordinates

variable {R S I : Type u} [CommRing R] [CommRing S] [Finite I]

/-- The scalar family presentation agrees with the arbitrary-scheme tuple
constructor over any given base morphism, not only a displayed ring map. -/
theorem affineTupleSection_map_eq (p : Spec (.of S) ⟶ Spec (.of R)) (s : I → S) :
    letI : Epi (Sigma.desc (affineTupleSection s)) := affineTupleSection_epi s
    mapOfFiniteFamily p (SheafOfModules.unit (Spec (.of S)).ringCatSheaf)
      (affineUnit_locallyRankOne S) (affineTupleSection s) =
    AffineTuple.map p ((Scheme.ΓSpecIso (.of S)).inv ∘ s) := by
  let : Epi (Sigma.desc (affineTupleSection s)) := affineTupleSection_epi s
  unfold AffineTuple.map
  apply @mapOfFiniteFamily_iso R _ (Option I) (Spec (.of S)) p
    (SheafOfModules.unit (Spec (.of S)).ringCatSheaf)
    (SheafOfModules.unit (Spec (.of S)).ringCatSheaf)
    (affineUnit_locallyRankOne S) (AffineTuple.unit_locallyRankOne _)
    inferInstance (affineTupleSection s)
    (AffineTuple.family (Spec (.of S)) ((Scheme.ΓSpecIso (.of S)).inv ∘ s))
    (affineTupleSection_epi s) (AffineTuple.family_epi _ _) (Iso.refl _)
  intro i
  exact (Category.comp_id _).trans
    ((congrFun (affineTupleSection_eq_chartFamily s) i).trans
      (congrFun (AffineTuple.family_spec s) i).symm)

variable (A : Type u) [CommRing A] (U : (Spec (.of A)).Opens) (f : A)
  (hU : U = PrimeSpectrum.basicOpen f)

/-- The original protected open identified with its actual localization. -/
def principalRestrictionIso : U.toScheme ≅ Spec (.of (Localization.Away f)) :=
  (Spec (.of A)).isoOfEq hU ≪≫ basicOpenIsoSpecAway (R := .of A) f

@[reassoc]
theorem principalRestrictionIso_hom_map :
    (principalRestrictionIso A U f hU).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f))) = U.ι := by
  dsimp only [principalRestrictionIso, Iso.trans_hom]
  rw [Category.assoc]
  exact (congrArg (fun g ↦ ((Spec (.of A)).isoOfEq hU).hom ≫ g)
    (basicOpenIsoSpecAway_hom_SpecMap (R := .of A) f)).trans
      ((Spec (.of A)).isoOfEq_hom_ι hU)

@[reassoc]
theorem principalRestrictionIso_inv_ι :
    (principalRestrictionIso A U f hU).inv ≫ U.ι =
      Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f))) := by
  rw [← principalRestrictionIso_hom_map A U f hU, Iso.inv_hom_id_assoc]

variable (n : ℕ) (a : I → A)

include hU in
omit [Finite I] in
/-- The actual coordinate centre is the unit ideal on the entire specified open. -/
theorem principalCoordinateCenter_comap_open_eq_top :
    (Blowup.affineCenter A (principalCoordinateIdeal f n a)).comap U.ι = ⊤ := by
  rw [← principalRestrictionIso_hom_map A U f hU, IdealSheafData.comap_comp,
    principalCoordinateCenter_comap_eq_top, IdealSheafData.comap_top]

omit [Finite I] in
/-- The canonical localization lift is the inverse of the literal protected
restriction of the blowdown, followed by the actual open inclusion. -/
theorem principalCoordinateLift_eq_restriction :
    principalCoordinateLift A f n a =
      (principalRestrictionIso A U f hU).inv ≫
        ((Blowup.blowupDatum
          (Blowup.affineCenter A (principalCoordinateIdeal f n a))).restrictIsoOfComapEqTop U
            (principalCoordinateCenter_comap_open_eq_top A U f hU n a)).inv ≫
        ((Blowup.blowupDatum (Blowup.affineCenter A
          (principalCoordinateIdeal f n a))).map ⁻¹ᵁ U).ι := by
  let B := Blowup.blowupDatum (Blowup.affineCenter A (principalCoordinateIdeal f n a))
  apply B.hom_ext (Blowup.cartier_of_comap_eq_top _ _
    (principalCoordinateCenter_comap_eq_top A f n a))
  · exact principalCoordinateLift_map A f n a
  · let e := principalRestrictionIso A U f hU
    let b := B.restrictIsoOfComapEqTop U
      (principalCoordinateCenter_comap_open_eq_top A U f hU n a)
    change (e.inv ≫ b.inv ≫ (B.map ⁻¹ᵁ U).ι) ≫ B.map = _
    have hb : b.hom ≫ U.ι = (B.map ⁻¹ᵁ U).ι ≫ B.map :=
      B.restrictIsoOfComapEqTop_hom_ι U _
    calc
      (e.inv ≫ b.inv ≫ (B.map ⁻¹ᵁ U).ι) ≫ B.map =
          e.inv ≫ b.inv ≫ b.hom ≫ U.ι := by
        simpa only [Category.assoc] using
          congrArg (fun k ↦ e.inv ≫ b.inv ≫ k) hb.symm
      _ = e.inv ≫ U.ι := by rw [Iso.inv_hom_id_assoc]
      _ = _ := principalRestrictionIso_inv_ι A U f hU

variable (p : Spec (.of A) ⟶ Spec (.of R))

include f hU in
/-- Every finite tuple on a specified principal open extends after an actual
coordinate-ideal blowup, with equality on its whole inverse-image open.
There are no reducedness, integrality, or dimension hypotheses. -/
theorem exists_principalRestriction_extension (s : I → Γ(U.toScheme, ⊤)) :
    ∃ (J : (Spec (.of A)).IdealSheafData) (B : Blowup.BlowupDatum J)
      (F : B.Y ⟶ ProjectiveSpace R (Option I)),
      J.comap U.ι = ⊤ ∧
      F ≫ ProjectiveSpace.toSpec R (Option I) = B.map ≫ p ∧
      (B.map ⁻¹ᵁ U).ι ≫ F =
        (B.map ∣_ U) ≫ AffineTuple.map (U.ι ≫ p) s := by
  let e := principalRestrictionIso A U f hU
  let t : I → Localization.Away f := fun i ↦
    (Scheme.ΓSpecIso (.of (Localization.Away f))).hom (e.inv.appTop (s i))
  obtain ⟨n, a, ha⟩ := exists_principalCoordinateBlowupMap_agrees A f p t
  let J := Blowup.affineCenter A (principalCoordinateIdeal f n a)
  let B := Blowup.blowupDatum J
  let F : B.Y ⟶ ProjectiveSpace R (Option I) :=
    affineCoordinateBlowupMap A (principalHomogeneousCoordinates f n a) p
  have hJ : J.comap U.ι = ⊤ := principalCoordinateCenter_comap_open_eq_top A U f hU n a
  refine ⟨J, B, F, hJ, affineCoordinateBlowupMap_toSpec A _ p, ?_⟩
  let b := B.restrictIsoOfComapEqTop U hJ
  have ht : (Scheme.ΓSpecIso (.of (Localization.Away f))).inv ∘ t = e.inv.appTop ∘ s := by
    funext i
    exact ConcreteCategory.congr_hom (Scheme.ΓSpecIso (.of (Localization.Away f))).hom_inv_id
      (e.inv.appTop (s i))
  have hlocal : principalCoordinateLift A f n a ≫ F =
      e.inv ≫ AffineTuple.map (U.ι ≫ p) s := by
    rw [ha, affineTupleSection_map_eq, ht, AffineTuple.map_naturality]
    congr 1
    exact (principalRestrictionIso_inv_ι_assoc A U f hU p).symm
  apply (cancel_epi (e.inv ≫ b.inv)).mp
  change (e.inv ≫ b.inv) ≫ (B.map ⁻¹ᵁ U).ι ≫ F =
    (e.inv ≫ b.inv) ≫ b.hom ≫ AffineTuple.map (U.ι ≫ p) s
  have hlift : principalCoordinateLift A f n a =
      e.inv ≫ b.inv ≫ (B.map ⁻¹ᵁ U).ι :=
    principalCoordinateLift_eq_restriction A U f hU n a
  calc
    (e.inv ≫ b.inv) ≫ (B.map ⁻¹ᵁ U).ι ≫ F =
        principalCoordinateLift A f n a ≫ F := by
      simpa only [Category.assoc] using
        (congrArg (fun k : Spec (.of (Localization.Away f)) ⟶ B.Y ↦ k ≫ F) hlift).symm
    _ = e.inv ≫ AffineTuple.map (U.ι ≫ p) s := hlocal
    _ = (e.inv ≫ b.inv) ≫ b.hom ≫ AffineTuple.map (U.ι ≫ p) s := by
      simp only [Category.assoc, Iso.inv_hom_id_assoc]

end AlgebraicGeometry.Scheme.RationalCoordinates
