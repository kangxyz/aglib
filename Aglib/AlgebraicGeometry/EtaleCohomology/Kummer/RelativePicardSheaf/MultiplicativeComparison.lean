/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.GmEtale
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.RelativePicardSheaf.EtaleNormalization
public import Aglib.AlgebraicGeometry.EtaleCohomology.Picard.Pullback
public import Aglib.AlgebraicGeometry.EtaleCohomology.PullbackEquivalence

/-! # Original R1 Gm and the normalized relative Picard sheaf

The original etale coefficient, chart cohomology and sheafification maps identify
native R1 Gm with the existing normalized relative Picard sheaf. The original
chart-unit equation and every natural-number power map are retained.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.EtaleCohomology
open GroupCohomology.Kummer.Coefficients
open GroupCohomology.Kummer.CoefficientBaseChange

universe u

private theorem adjunction_unit_transport_inverse
    {C D : Type*} [Category* C] [Category* D] {L : C ⥤ D} {R : D ⥤ C}
    (adj : L ⊣ R) {F G : C} {H N : D} (a : L.obj F ≅ H) (b : F ⟶ G)
    (k : L.obj G ⟶ N) (q : F ⟶ R.obj H) (r : G ⟶ R.obj N)
    (hq : adj.unit.app F ≫ R.map a.hom = q)
    (hr : adj.unit.app G ≫ R.map k = r) :
    q ≫ R.map (a.inv ≫ L.map b ≫ k) = b ≫ r := by
  have hc : q ≫ R.map a.inv = adj.unit.app F := by
    rw [← hq, Category.assoc, ← Functor.map_comp, a.hom_inv_id,
      CategoryTheory.Functor.map_id]
    exact Category.comp_id _
  calc
    q ≫ R.map (a.inv ≫ L.map b ≫ k) =
        (q ≫ R.map a.inv) ≫ R.map (L.map b) ≫ R.map k := by
      simp only [Functor.map_comp, Category.assoc]
    _ = (adj.unit.app F ≫ R.map (L.map b)) ≫ R.map k := by
      rw [hc, Category.assoc]
    _ = (b ≫ adj.unit.app G) ≫ R.map k := by
      simpa only [CategoryTheory.Functor.comp_map, CategoryTheory.Functor.id_map] using
        congrArg (fun t => t ≫ R.map k) (adj.unit.naturality b).symm
    _ = b ≫ r := by rw [Category.assoc, hr]

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Picard

open Scheme.RelativePicard Scheme.EtaleCohomology.Kummer
open Scheme.Modules.Invertible Scheme.Modules.Invertible.PullbackTensor.Local

universe w s e e'

attribute [local instance] hasSheafifyLarge

/-- Inverse Picard classification retains the original Gm cohomology pullback. -/
theorem picardCohomologyEquiv_symm_pullback {X Y : Scheme.{u}}
    [HasExt.{e} (AbelianSheaf.{u, u + 1} X)]
    [HasExt.{e'} (AbelianSheaf.{u, u + 1} Y)]
    (f : Y ⟶ X) (c : Sheaf.H.{e} (gm X) 1) :
    (picardCohomologyEquiv Y).symm (gmCohomologyPullback f 1 c) =
      pullbackClass f ((picardCohomologyEquiv X).symm c) := by
  apply (picardCohomologyEquiv Y).injective
  rw [AddEquiv.apply_symm_apply]
  simpa only [AddEquiv.apply_symm_apply] using
    picardCohomologyEquiv_pullback f ((picardCohomologyEquiv X).symm c)

/-- The supplied Ext universe on the original relative chart. -/
local instance gmRelativeChartHasExt {X S : Scheme.{u}} (p : X ⟶ S)
    [h : ∀ U : S.Etale, HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback U.hom p))]
    (U : S.Etale) : HasExt.{e} (AbelianSheaf.{u, u + 1} ((siteBaseChange p).obj U).left) :=
  inferInstanceAs (HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback U.hom p)))

/-- The supplied Ext universe on the relative identity chart. -/
local instance gmRelativeIdentityChartHasExt {X S : Scheme.{u}} (p : X ⟶ S)
    [h : ∀ U : S.Etale, HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback U.hom p))]
    (U : S.Etale) : HasExt.{e}
      (AbelianSheaf.{u, u + 1} ((𝟭 Scheme.{u}).obj ((siteBaseChange p).obj U).left)) :=
  inferInstanceAs (HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback U.hom p)))

section Chart

variable {X S : Scheme.{u}} (p : X ⟶ S)
  [∀ U : S.Etale, HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback U.hom p))]

/-- Original chart cohomology equals the actual family Picard group, via the original symmetry. -/
def fibreProductGmPicardEquiv (U : S.Etale) :
    Sheaf.H.{e} ((inverseImage (pullback.snd U.hom p)).obj (gm X)) 1 ≃+
      PicardGroup (pullback p U.hom) :=
  (AddEquiv.ofBijective (Sheaf.H.map (gmEtalePullbackIso (pullback.snd U.hom p)).hom 1)
    (cohomologyMapIso_bijective (gmEtalePullbackIso (pullback.snd U.hom p)) 1)).trans
      ((picardCohomologyEquiv (pullback U.hom p)).symm.trans
        ((picardFunctor.mapIso (pullbackSymmetry p U.hom).op).addCommGroupIsoToAddEquiv))

/-- The value uses the unchanged cohomology coefficient map, Picard inverse and symmetry. -/
theorem fibreProductGmPicardEquiv_apply (U : S.Etale)
    (c : Sheaf.H.{e} ((inverseImage (pullback.snd U.hom p)).obj (gm X)) 1) :
    fibreProductGmPicardEquiv p U c = pullbackClass (pullbackSymmetry p U.hom).hom
      ((picardCohomologyEquiv (pullback U.hom p)).symm
        (Sheaf.H.map (gmEtalePullbackIso (pullback.snd U.hom p)).hom 1 c)) := rfl

/-- The original coefficient isomorphisms respect the literal fibre-product restriction. -/
theorem fibreProductGmCohomology_restriction {U V : S.Etale} (a : V ⟶ U)
    (c : Sheaf.H.{e} ((inverseImage (pullback.snd U.hom p)).obj (gm X)) 1) :
    Sheaf.H.map (gmEtalePullbackIso (pullback.snd V.hom p)).hom 1
        (fibreProductCohomologyRestriction p a (gm X) 1 c) =
      gmCohomologyPullback ((siteBaseChange p).map a).left 1
        (Sheaf.H.map (gmEtalePullbackIso (pullback.snd U.hom p)).hom 1 c) := by
  have : Etale ((siteBaseChange p).map a).left := inferInstance
  let g := ((siteBaseChange p).map a).left
  have ht := gmEtalePullbackIso_triangle (pullback.snd U.hom p) g
    (pullback.snd V.hom p) (siteBaseChange_map_snd p a).symm
  have hc := cohomologyPullback_coefficientMap g
    (gmEtalePullbackIso (pullback.snd U.hom p)).hom 1 c
  change Sheaf.H.map (gmEtalePullbackIso (pullback.snd V.hom p)).hom 1
    (Sheaf.H.map ((pullbackTriangleIso (pullback.snd V.hom p)
      (pullback.snd U.hom p) g (siteBaseChange_map_snd p a)).inv.app (gm X)) 1
        (cohomologyPullback g ((inverseImage (pullback.snd U.hom p)).obj (gm X)) 1 c)) = _
  rw [← Sheaf.H.map_comp_apply, ht, Sheaf.H.map_comp_apply]
  change _ = Sheaf.H.map (torsorAdjunctionCoefficient g (q := gmUnit g)) 1
    (cohomologyPullback g (gm (pullback U.hom p)) 1
      (Sheaf.H.map (gmEtalePullbackIso (pullback.snd U.hom p)).hom 1 c))
  rw [gmUnit_adjoint_etale]
  exact congrArg (Sheaf.H.map (gmEtalePullbackIso g).hom 1) hc.symm

omit [∀ U : S.Etale, HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback U.hom p))] in
/-- The actual symmetry changes fibre-product orientation compatibly with the family map. -/
theorem familyPicardSymmetry_transition {U V : S.Etale} (a : V ⟶ U) :
    (pullbackSymmetry p V.hom).hom ≫ ((siteBaseChange p).map a).left =
      (familyScheme p).map ((Scheme.Etale.forget S).map a) ≫
        (pullbackSymmetry p U.hom).hom := by
  apply pullback.hom_ext
  · rw [Category.assoc, siteBaseChange_map_fst, ← Category.assoc,
      pullbackSymmetry_hom_comp_fst, Category.assoc, pullbackSymmetry_hom_comp_fst]
    exact (familyScheme_map_snd p ((Scheme.Etale.forget S).map a)).symm
  · rw [Category.assoc, siteBaseChange_map_snd, pullbackSymmetry_hom_comp_snd,
      Category.assoc, pullbackSymmetry_hom_comp_snd]
    exact (familyScheme_map_fst p ((Scheme.Etale.forget S).map a)).symm

/-- The actual chart equivalences are natural for the original restrictions. -/
theorem fibreProductGmPicardEquiv_restriction {U V : S.Etale} (a : V ⟶ U)
    (c : Sheaf.H.{e} ((inverseImage (pullback.snd U.hom p)).obj (gm X)) 1) :
    fibreProductGmPicardEquiv p V (fibreProductCohomologyRestriction p a (gm X) 1 c) =
      ((familyPicardFunctor p).map ((Scheme.Etale.forget S).map a).op).hom
        (fibreProductGmPicardEquiv p U c) := by
  rw [fibreProductGmPicardEquiv_apply, fibreProductGmPicardEquiv_apply,
    fibreProductGmCohomology_restriction]
  have hn := picardCohomologyEquiv_symm_pullback.{u, e, e}
    (X := pullback U.hom p) (Y := pullback V.hom p)
    ((siteBaseChange p).map a).left
    (Sheaf.H.map (gmEtalePullbackIso (pullback.snd U.hom p)).hom 1 c)
  refine (congrArg (pullbackClass (pullbackSymmetry p V.hom).hom) hn).trans ?_
  exact (pullbackClass_comp (pullbackSymmetry p V.hom).hom
    ((siteBaseChange p).map a).left _).symm.trans
      ((congrArg (fun f => pullbackClass f _) (familyPicardSymmetry_transition p a)).trans
        (pullbackClass_comp ((familyScheme p).map ((Scheme.Etale.forget S).map a))
          (pullbackSymmetry p U.hom).hom _))

end Chart

variable {X S : Scheme.{u}} (p : X ⟶ S)
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [∀ U : S.Etale, HasExt.{s} (Sheaf ((Scheme.smallEtaleTopology X).over
    ((siteBaseChange p).obj U)) AddCommGrpCat.{u + 1})]
  [∀ U : S.Etale, HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback U.hom p))]

/-- The same resized cohomology diagram maps to the original family Picard presheaf. -/
def fibreProductGmPicardNatTrans :
    smallFibreProductCohomologyPresheaf p (gm X) 1 ⟶
      (Scheme.Etale.forget S).op ⋙ familyPicardFunctor p := by
  let D := @Stalk.originalFibreProductCohomologyPresheaf X S p
    (inferInstance : HasExt.{w} (AbelianSheaf.{u, u + 1} X))
    (inferInstance : ∀ U : S.Etale, HasExt.{s}
      (Sheaf ((Scheme.smallEtaleTopology X).over ((siteBaseChange p).obj U))
        AddCommGrpCat.{u + 1}))
    (inferInstance : ∀ U : S.Etale,
      HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback U.hom p))) (gm X) 1
  let : ∀ U : S.Etaleᵒᵖ, Small.{u + 1} (D.obj U) := fun U =>
    fibreProductCohomology_small.{u, w, s, e} p (gm X) 1 U.unop
  exact resizeAdditiveDiagramHom D ((Scheme.Etale.forget S).op ⋙ familyPicardFunctor p)
    (fun U => (fibreProductGmPicardEquiv.{u, e} p U.unop).toAddMonoidHom)
    (fun {U V} a c => fibreProductGmPicardEquiv_restriction.{u, e} p a.unop c)

/-- Each actual chart map is bijective, so the original presheaf map is an isomorphism. -/
instance fibreProductGmPicardNatTransIsIso : IsIso (fibreProductGmPicardNatTrans p) := by
  let : ∀ U : S.Etaleᵒᵖ, IsIso ((fibreProductGmPicardNatTrans p).app U) := fun U => by
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    change Function.Bijective (fun c => fibreProductGmPicardEquiv p U.unop
      (fibreProductResizeEquiv.{u, w, s, e} p (gm X) 1 U.unop c))
    exact (fibreProductGmPicardEquiv p U.unop).bijective.comp
      (fibreProductResizeEquiv.{u, w, s, e} p (gm X) 1 U.unop).bijective
  exact NatIso.isIso_of_isIso_app _

variable (o : S ⟶ X) (ho : o ≫ p = 𝟙 S)
  [IsLocallyNoetherian S] [IsProper p] [Flat p] [GeometricallyIntegral p]

/-- Native R1 of the original Gm is the existing normalized relative Picard sheaf. -/
def gmHigherDirectImageNormalizedPicardIso :
    (higherDirectImage p 1).obj (gm X) ≅ normalizedPicardEtaleSheaf p o ho :=
  (fibreProductCohomologySheafificationIso p (gm X) 1).symm ≪≫
    (presheafToSheaf (Scheme.smallEtaleTopology S) AddCommGrpCat.{u + 1}).mapIso
      (asIso (fibreProductGmPicardNatTrans p)) ≪≫
        familyPicardEtaleSheafificationIso p o ho

/-- The complete original chart-unit equation fixes the comparison, before any stalk. -/
theorem gmHigherDirectImageNormalizedPicardIso_unit :
    fibreProductCohomologyToHigherDirectImage p (gm X) 1 ≫
      (gmHigherDirectImageNormalizedPicardIso p o ho).hom.hom =
        fibreProductGmPicardNatTrans p ≫ etaleFamilyNormalization p o ho := by
  exact adjunction_unit_transport_inverse
    (sheafificationAdjunction (Scheme.smallEtaleTopology S) AddCommGrpCat.{u + 1})
    (fibreProductCohomologySheafificationIso p (gm X) 1)
    (fibreProductGmPicardNatTrans p) (familyPicardEtaleToNormalized p o ho)
    (fibreProductCohomologyToHigherDirectImage p (gm X) 1)
    (etaleFamilyNormalization p o ho)
    (fibreProductCohomologyToHigherDirectImage_unit p (gm X) 1)
    (familyPicardEtaleToNormalized_unit p o ho)

/-- The isomorphism intertwines actual coefficient power with native Picard multiplication. -/
theorem gmHigherDirectImageNormalizedPicardIso_power (n : ℕ) :
    (higherDirectImage p 1).map (power X n) ≫
        (gmHigherDirectImageNormalizedPicardIso p o ho).hom =
      (gmHigherDirectImageNormalizedPicardIso p o ho).hom ≫
        (n • 𝟙 (normalizedPicardEtaleSheaf p o ho)) := by
  let := HasDerivedCategory.standard (AbelianSheaf.{u, u + 1} X)
  let := HasDerivedCategory.standard (AbelianSheaf.{u, u + 1} S)
  let : (higherDirectImage p 1).Additive :=
    Functor.additive_of_iso ((directImage p).rightDerivedSingleHomologyIso 1).symm
  exact (nsmul_identity_square (higherDirectImage p 1)
    (gmHigherDirectImageNormalizedPicardIso p o ho).hom n).symm

end AlgebraicGeometry.Scheme.EtaleCohomology.Picard
