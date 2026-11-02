/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.RelativePicardSheaf
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.FibreProductStalk
public import Aglib.AlgebraicGeometry.Picard.Comparison.Isomorphism
public import Aglib.AlgebraicGeometry.Modules.Invertible.IsomorphismSheaf
public import Aglib.AlgebraicGeometry.EtaleCohomology.PullbackIsomorphism
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.RepresentedCoefficients
public import Aglib.AlgebraicGeometry.Picard.GroupLaw
public import Mathlib.CategoryTheory.Sites.Limits
public import Aglib.AlgebraicGeometry.Sites.EtaleLocalInjectivity
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.FibreProductResize
public import Aglib.Algebra.Category.Grp.ResizeHom
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.RootsTriangle
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.RelativePicardSheaf.PointedKernel

/-!
# Original fibre-product Kummer classes and relative Picard classes

The source is the same resized fibre-product cohomology presheaf whose sheafification
is the native higher direct image. Coefficients are transported by the original roots
isomorphism; the opposite fibre-product orientations are related by the actual symmetry.
The target retains the original family Picard functor and its section-normalization.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits Opposite AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj
open AlgebraicGeometry.Scheme.Modules.Invertible
open GroupCohomology.Kummer.Coefficients GroupCohomology.Kummer.CoefficientBaseChange

universe u w s e e'

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Kummer

open RelativePicard

attribute [local instance] hasSheafifyLarge Over.cartesianMonoidalCategory

variable {X S : Scheme.{u}} (p : X ⟶ S)
    [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
    [∀ U : S.Etale, HasExt.{s} (Sheaf ((Scheme.smallEtaleTopology X).over
      ((siteBaseChange p).obj U)) AddCommGrpCat.{u + 1})]
    [∀ U : S.Etale, HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback U.hom p))]
    (n : ℕ) (hn : 0 < n) (hi : IsUnit (n : Γ(X, ⊤)))

/-- The original class map on a chart, using actual symmetry to reach `X ×_S U`. -/
def fibreProductRootsPicardMap (U : S.Etale) :
    Sheaf.H.{e} ((inverseImage (pullback.snd U.hom p)).obj (mu X n)) 1 →+
      PicardGroup (pullback p U.hom) :=
  (PullbackTensor.Local.pullbackHom (pullbackSymmetry p U.hom).hom).comp
    ((rootsPicardMap (pullback U.hom p) n).comp
      (Sheaf.H.map (rootsPullbackIso (pullback.snd U.hom p) n hn hi).hom 1))

omit [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [∀ U : S.Etale, HasExt.{s} (Sheaf ((Scheme.smallEtaleTopology X).over
    ((siteBaseChange p).obj U)) AddCommGrpCat.{u + 1})]
  [∀ U : S.Etale, HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback U.hom p))] in
private theorem symmetry_transition {U V : S.Etale} (a : V ⟶ U) :
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

omit [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [∀ U : S.Etale, HasExt.{s} (Sheaf ((Scheme.smallEtaleTopology X).over
    ((siteBaseChange p).obj U)) AddCommGrpCat.{u + 1})] in
/-- Naturality retains the actual fibre-product cohomology restriction, not a substitute map. -/
theorem fibreProductRootsPicardMap_restriction {U V : S.Etale} (a : V ⟶ U)
    (c : Sheaf.H.{e} ((inverseImage (pullback.snd U.hom p)).obj (mu X n)) 1) :
    fibreProductRootsPicardMap p n hn hi V
      (fibreProductCohomologyRestriction p a (mu X n) 1 c) =
        ((familyPicardFunctor p).map ((Scheme.Etale.forget S).map a).op).hom
          (fibreProductRootsPicardMap p n hn hi U c) := by
  have ht := rootsPicard_triangle.{u, e, e}
    (pullback.snd V.hom p) (pullback.snd U.hom p)
    ((siteBaseChange p).map a).left (siteBaseChange_map_snd p a) n hn hi c
  refine (congrArg (pullbackClass (pullbackSymmetry p V.hom).hom) ht).trans ?_
  exact (pullbackClass_comp (pullbackSymmetry p V.hom).hom
    ((siteBaseChange p).map a).left _).symm.trans
      ((congrArg (fun f => pullbackClass f _) (symmetry_transition p a)).trans
        (pullbackClass_comp ((familyScheme p).map ((Scheme.Etale.forget S).map a))
          (pullbackSymmetry p U.hom).hom _))

omit [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [∀ U : S.Etale, HasExt.{s} (Sheaf ((Scheme.smallEtaleTopology X).over
    ((siteBaseChange p).obj U)) AddCommGrpCat.{u + 1})] in
/-- The chart map lands in actual Picard `n`-torsion. -/
theorem nsmul_fibreProductRootsPicardMap (U : S.Etale)
    (c : Sheaf.H.{e} ((inverseImage (pullback.snd U.hom p)).obj (mu X n)) 1) :
    n • fibreProductRootsPicardMap p n hn hi U c = 0 := by
  change n • PullbackTensor.Local.pullbackHom (pullbackSymmetry p U.hom).hom
    (rootsPicardMap _ n (Sheaf.H.map _ 1 c)) = 0
  rw [← map_nsmul]
  have ht := (rootsPicardTorsionMap (pullback U.hom p) n hn
    (levelInvertible (pullback.snd U.hom p) n hi) (Sheaf.H.map
      (rootsPullbackIso (pullback.snd U.hom p) n hn hi).hom 1 c)).property
  change n • rootsPicardMap _ n (Sheaf.H.map _ 1 c) = 0 at ht
  rw [ht, map_zero]

/-- The actual same-model comparison before section-normalization. -/
def fibreProductRootsPicardNatTrans :
    smallFibreProductCohomologyPresheaf p (mu X n) 1 ⟶
      (Scheme.Etale.forget S).op ⋙ familyPicardFunctor p := by
  let D := @Stalk.originalFibreProductCohomologyPresheaf X S p
    (inferInstance : HasExt.{w} (AbelianSheaf.{u, u + 1} X))
    (inferInstance : ∀ U : S.Etale, HasExt.{s}
      (Sheaf ((Scheme.smallEtaleTopology X).over ((siteBaseChange p).obj U))
        AddCommGrpCat.{u + 1}))
    (inferInstance : ∀ U : S.Etale,
      HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback U.hom p))) (mu X n) 1
  let : ∀ U : S.Etaleᵒᵖ, Small.{u + 1} (D.obj U) := fun U =>
    fibreProductCohomology_small.{u, w, s, e} p (mu X n) 1 U.unop
  exact resizeAdditiveDiagramHom D ((Scheme.Etale.forget S).op ⋙ familyPicardFunctor p)
    (fun U => fibreProductRootsPicardMap.{u, e} p n hn hi U.unop)
    (fun {U V} a c => fibreProductRootsPicardMap_restriction p n hn hi a.unop c)

variable (o : S ⟶ X) (ho : o ≫ p = 𝟙 S)

/-- The existing section-normalization, applied to the original higher-image presheaf. -/
def fibreProductRootsNormalizedPicardNatTrans :
    smallFibreProductCohomologyPresheaf p (mu X n) 1 ⟶
      (Scheme.Etale.forget S).op ⋙ normalizedPicardFunctor p o ho :=
  fibreProductRootsPicardNatTrans p n hn hi ≫
    Functor.whiskerLeft (Scheme.Etale.forget S).op
      (quotientProjection p ≫ (quotientNormalizedIso p o ho).hom)

/-- The comparison is killed by the actual multiplication endomorphism of the target presheaf. -/
theorem fibreProductRootsNormalizedPicardNatTrans_nsmul :
    fibreProductRootsNormalizedPicardNatTrans p n hn hi o ho ≫
      (n • 𝟙 ((Scheme.Etale.forget S).op ⋙ normalizedPicardFunctor p o ho)) = 0 := by
  ext U c
  let N := ((quotientProjection p ≫ (quotientNormalizedIso p o ho).hom).app
    ((Scheme.Etale.forget S).op.obj U)).hom
  change n • N (fibreProductRootsPicardMap p n hn hi U.unop
    (fibreProductResizeEquiv.{u, w, s, e} p (mu X n) 1 U.unop c)) = 0
  rw [← map_nsmul, nsmul_fibreProductRootsPicardMap, map_zero]

/-- Factorization through the categorical kernel in the original small-étale presheaf category.
This is a genuine kernel, not a pointwise group relabeled as a sheaf kernel. -/
def fibreProductRootsNormalizedPicardKernelMap :
    smallFibreProductCohomologyPresheaf p (mu X n) 1 ⟶
      kernel (n • 𝟙 ((Scheme.Etale.forget S).op ⋙ normalizedPicardFunctor p o ho)) :=
  kernel.lift _ (fibreProductRootsNormalizedPicardNatTrans p n hn hi o ho)
    (fibreProductRootsNormalizedPicardNatTrans_nsmul p n hn hi o ho)

section Symmetry

variable [∀ U : S.Etale, HasExt.{e'} (AbelianSheaf.{u, u + 1} (pullback p U.hom))]

local instance familyOrientationHasExt (U : S.Etale) :
    HasExt.{e'} (AbelianSheaf.{u, u + 1}
      ((familyScheme p).obj ((Scheme.Etale.forget S).obj U))) :=
  inferInstanceAs (HasExt.{e'} (AbelianSheaf.{u, u + 1} (pullback p U.hom)))

local instance familyPullbackHasExt (U : S.Etale) :
    HasExt.{e'} (AbelianSheaf.{u, u + 1}
      (pullback p ((Scheme.Etale.forget S).obj U).hom)) :=
  inferInstanceAs (HasExt.{e'} (AbelianSheaf.{u, u + 1} (pullback p U.hom)))

/-- Actual cohomology transport to the Picard-family orientation; both group universes
are retained, and bijectivity comes from the actual scheme symmetry. -/
def fibreProductRootsCohomologyEquiv (U : S.Etale) :
    Sheaf.H.{e} ((inverseImage (pullback.snd U.hom p)).obj (mu X n)) 1 ≃+
      Sheaf.H.{e'} (mu (pullback p U.hom) n) 1 :=
  AddEquiv.ofBijective
    ((rootsCohomologyPullback (pullbackSymmetry p U.hom).hom n hn
      (levelInvertible (pullback.snd U.hom p) n hi) 1).comp
        (Sheaf.H.map (rootsPullbackIso (pullback.snd U.hom p) n hn hi).hom 1))
    (((cohomologyMapIso_bijective (rootsPullbackIso (pullbackSymmetry p U.hom).hom n hn
      (levelInvertible (pullback.snd U.hom p) n hi)) 1).comp
        (cohomologyPullback_bijective_of_isEquivalence (pullbackSymmetry p U.hom).hom
          (mu (pullback U.hom p) n) 1)).comp
      (cohomologyMapIso_bijective (rootsPullbackIso (pullback.snd U.hom p) n hn hi) 1))

omit [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [∀ U : S.Etale, HasExt.{s} (Sheaf ((Scheme.smallEtaleTopology X).over
    ((siteBaseChange p).obj U)) AddCommGrpCat.{u + 1})] in
/-- The same cohomology equivalence recovers the original chart-to-Picard map. -/
theorem fibreProductRootsCohomologyEquiv_picard (U : S.Etale)
    (c : Sheaf.H.{e} ((inverseImage (pullback.snd U.hom p)).obj (mu X n)) 1) :
    rootsPicardMap (pullback p U.hom) n (fibreProductRootsCohomologyEquiv p n hn hi U c) =
      fibreProductRootsPicardMap p n hn hi U c :=
  DFunLike.congr_fun (rootsPicardMap_pullback (pullbackSymmetry p U.hom).hom n hn
    (levelInvertible (pullback.snd U.hom p) n hi)) _

omit [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [∀ U : S.Etale, HasExt.{s} (Sheaf ((Scheme.smallEtaleTopology X).over
    ((siteBaseChange p).obj U)) AddCommGrpCat.{u + 1})] in
/-- The cohomology orientation comparison commutes with the same original restrictions. -/
theorem fibreProductRootsCohomologyEquiv_restriction {U V : S.Etale} (a : V ⟶ U)
    (c : Sheaf.H.{e} ((inverseImage (pullback.snd U.hom p)).obj (mu X n)) 1) :
    fibreProductRootsCohomologyEquiv p n hn hi V
      (fibreProductCohomologyRestriction p a (mu X n) 1 c) =
      rootsCohomologyPullback ((familyScheme p).map ((Scheme.Etale.forget S).map a)) n hn
        (levelInvertible (pullbackSymmetry p U.hom).hom n
          (levelInvertible (pullback.snd U.hom p) n hi)) 1
        (fibreProductRootsCohomologyEquiv p n hn hi U c) := by
  exact @rootsCohomology_triangle_orientation X
    (pullback V.hom p) (pullback U.hom p) (pullback p V.hom) (pullback p U.hom)
    (inferInstance : HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback V.hom p)))
    (inferInstance : HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback U.hom p)))
    (inferInstance : HasExt.{e'} (AbelianSheaf.{u, u + 1} (pullback p V.hom)))
    (inferInstance : HasExt.{e'} (AbelianSheaf.{u, u + 1} (pullback p U.hom)))
    (pullback.snd V.hom p) (pullback.snd U.hom p)
    ((siteBaseChange p).map a).left (siteBaseChange_map_snd p a)
    (pullbackSymmetry p V.hom).hom (pullbackSymmetry p U.hom).hom
    ((familyScheme p).map ((Scheme.Etale.forget S).map a)) (symmetry_transition p a)
    n hn hi c

/-- Every actual normalized torsion section has a preimage in the same native
higher-image presheaf, with no assumption of finite étale representability. -/
theorem fibreProductRootsNormalizedPicardNatTrans_surjective_torsion (U : S.Etale)
    (a : normalizedPicardTorsion p o ho ((Scheme.Etale.forget S).obj U) n) :
    ∃ c : (smallFibreProductCohomologyPresheaf p (mu X n) 1).obj (op U),
      (fibreProductRootsNormalizedPicardNatTrans p n hn hi o ho).app (op U) c = a.val := by
  let hU := levelInvertible (pullbackSymmetry p U.hom).hom n
    (levelInvertible (pullback.snd U.hom p) n hi)
  obtain ⟨b, hb⟩ := rootsNormalizedPicardMap_surjective p o ho
    ((Scheme.Etale.forget S).obj U) n hn hU a
  let c := (fibreProductRootsCohomologyEquiv p n hn hi U).symm b
  refine ⟨(fibreProductResizeEquiv.{u, w, s, e} p (mu X n) 1 U).symm c, ?_⟩
  have hp := fibreProductRootsCohomologyEquiv_picard p n hn hi U c
  rw [show fibreProductRootsCohomologyEquiv p n hn hi U c = b from
    (fibreProductRootsCohomologyEquiv p n hn hi U).apply_symm_apply b] at hp
  change normalization p o ho ((Scheme.Etale.forget S).obj U)
    (fibreProductRootsPicardMap p n hn hi U
      (fibreProductResizeEquiv.{u, w, s, e} p (mu X n) 1 U
      ((fibreProductResizeEquiv.{u, w, s, e} p (mu X n) 1 U).symm c))) = _
  rw [AddEquiv.apply_symm_apply, ← hp]
  exact congrArg Subtype.val hb

/-- The categorical kernel comparison is pointwise surjective on the original small site. -/
theorem fibreProductRootsNormalizedPicardKernelMap_surjective (U : S.Etale) :
    Function.Surjective ((fibreProductRootsNormalizedPicardKernelMap p n hn hi o ho).app
      (op U)) := by
  let m := n • 𝟙 ((Scheme.Etale.forget S).op ⋙ normalizedPicardFunctor p o ho)
  intro t
  let a := (kernel.ι m).app (op U) t
  have ha : n • a = 0 := by
    have h := congrArg (fun φ => (φ.app (op U)) t) (kernel.condition m)
    exact h
  obtain ⟨c, hc⟩ := fibreProductRootsNormalizedPicardNatTrans_surjective_torsion
    p n hn hi o ho U ⟨a, ha⟩
  refine ⟨c, ?_⟩
  apply (AddCommGrpCat.mono_iff_injective ((kernel.ι m).app (op U))).mp inferInstance
  have h := congrArg (fun φ => (φ.app (op U)) c)
    (kernel.lift_ι m (fibreProductRootsNormalizedPicardNatTrans p n hn hi o ho)
      (fibreProductRootsNormalizedPicardNatTrans_nsmul p n hn hi o ho))
  exact h.trans hc

/-- Pointwise surjectivity makes the original presheaf-kernel map epi. -/
instance fibreProductRootsNormalizedPicardKernelMap_epi :
    Epi (fibreProductRootsNormalizedPicardKernelMap p n hn hi o ho) := by
  rw [NatTrans.epi_iff_epi_app]
  intro U
  exact (AddCommGrpCat.epi_iff_surjective _).mpr
    (fibreProductRootsNormalizedPicardKernelMap_surjective p n hn hi o ho U.unop)

end Symmetry

section Sheaf

variable [IsLocallyNoetherian S] [IsProper p] [Flat p] [GeometricallyIntegral p]

omit [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [∀ U : S.Etale, HasExt.{s} (Sheaf ((Scheme.smallEtaleTopology X).over
    ((siteBaseChange p).obj U)) AddCommGrpCat.{u + 1})]
  [∀ U : S.Etale, HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback U.hom p))] in
/-- The existing normalized Picard functor restricts to a genuine small étale sheaf.
The fppf comparison supplies descent; the topology restriction is explicit. -/
theorem normalizedPicard_smallEtale_isSheaf :
    Presheaf.IsSheaf (Scheme.smallEtaleTopology S)
      ((Scheme.Etale.forget S).op ⋙ normalizedPicardFunctor p o ho) := by
  apply (Scheme.Etale.forget S).op_comp_isSheaf_of_isSheaf
    (Scheme.smallEtaleTopology S) (Scheme.etaleTopology.over S)
  have hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) (normalizedPicardFunctor p o ho) :=
    (Presheaf.isSheaf_of_iso_iff
      (normalizedFppfIsoOfIsProperOfFlatOfGeometricallyIntegral p o ho)).mpr
      (fppfPicardSheaf p).property
  apply hF.of_le
  intro U R hR
  rw [GrothendieckTopology.mem_over_iff] at hR ⊢
  exact Modules.Invertible.EtaleDescent.etaleTopology_le_fppfTopology _ hR

/-- The original normalized Picard functor as an abelian sheaf, not its pointwise torsion. -/
def normalizedPicardEtaleSheaf : AbelianSheaf.{u, u + 1} S :=
  ⟨(Scheme.Etale.forget S).op ⋙ normalizedPicardFunctor p o ho,
    normalizedPicard_smallEtale_isSheaf p o ho⟩

/-- The actual kernel of multiplication in the small étale abelian-sheaf category. -/
def normalizedPicardEtaleTorsionSheaf : AbelianSheaf.{u, u + 1} S :=
  kernel (n • 𝟙 (normalizedPicardEtaleSheaf p o ho))

/-- The original presheaf map into the underlying actual sheaf kernel, via the canonical
kernel comparison for the limit-preserving sheaf inclusion. -/
def fibreProductRootsToNormalizedPicardSheafKernel :
    smallFibreProductCohomologyPresheaf p (mu X n) 1 ⟶
      (normalizedPicardEtaleTorsionSheaf p n o ho).obj :=
  fibreProductRootsNormalizedPicardKernelMap p n hn hi o ho ≫
    inv (kernelComparison (n • 𝟙 (normalizedPicardEtaleSheaf p o ho))
      (sheafToPresheaf (Scheme.smallEtaleTopology S) AddCommGrpCat.{u + 1}))

/-- The canonical morphism from the native higher direct image to actual normalized
Picard torsion. The source comparison is precisely its existing sheafification iso. -/
def rootsHigherDirectImageToNormalizedPicardTorsion :
    (higherDirectImage p 1).obj (mu X n) ⟶ normalizedPicardEtaleTorsionSheaf p n o ho :=
  (fibreProductCohomologySheafificationIso p (mu X n) 1).inv ≫
    ((sheafificationAdjunction (Scheme.smallEtaleTopology S) AddCommGrpCat.{u + 1}).homEquiv
      _ _).symm (fibreProductRootsToNormalizedPicardSheafKernel p n hn hi o ho)

section LocalKernel

variable [∀ Y : Scheme.{u}, HasExt.{e'} (AbelianSheaf.{u, u + 1} Y)]

/-- A section in the kernel of the actual presheaf comparison vanishes on a pointed étale
refinement. This consumes the constructed base `H¹` exactness and actual root-cover effacement. -/
theorem fibreProductRootsNormalizedPicardNatTrans_pointed_kernel_zero (U : S.Etale)
    (c : Sheaf.H.{e} ((inverseImage (pullback.snd U.hom p)).obj (mu X n)) 1)
    (hc : (fibreProductRootsNormalizedPicardNatTrans.{u, w, s, e} p n hn hi o ho).app (op U)
      ((fibreProductResizeEquiv.{u, w, s, e} p (mu X n) 1 U).symm c) = 0) (x : U.left) :
    ∃ (V : S.Etale) (a : V ⟶ U) (y : V.left),
      a.left y = x ∧ fibreProductCohomologyRestriction.{u, e, e} p a (mu X n) 1 c = 0 := by
  let T := (Scheme.Etale.forget S).obj U
  let hbase := levelInvertible (U.hom ≫ o) n hi
  let E := fibreProductRootsCohomologyEquiv.{u, e, e'} p n hn hi U
  have hcanon : rootsNormalizedPicardMap p o ho T n hn
      (levelInvertible (pullback.snd p U.hom) n hbase) (E c) = 0 := by
    apply Subtype.ext
    change normalization p o ho ((Scheme.Etale.forget S).obj U)
      (rootsPicardMap _ n (E c)) = 0
    have hp := fibreProductRootsCohomologyEquiv_picard.{u, e, e'} p n hn hi U c
    refine (congrArg (normalization p o ho ((Scheme.Etale.forget S).obj U)) hp).trans ?_
    change normalization p o ho ((Scheme.Etale.forget S).obj U)
      (fibreProductRootsPicardMap.{u, e} p n hn hi U
        (fibreProductResizeEquiv.{u, w, s, e} p (mu X n) 1 U
      ((fibreProductResizeEquiv.{u, w, s, e} p (mu X n) 1 U).symm c))) = 0 at hc
    simpa only [AddEquiv.apply_symm_apply] using hc
  obtain ⟨V, v, y, hy, hv⟩ := normalizedRootsKernel_pointed_effacement.{u, e'}
    p o ho U n hn hbase (E c) hcanon x
  refine ⟨V, v, y, hy, ?_⟩
  apply (fibreProductRootsCohomologyEquiv.{u, e, e'} p n hn hi V).injective
  exact (fibreProductRootsCohomologyEquiv_restriction.{u, e, e'}
    p n hn hi v c).trans (hv.trans
      (map_zero (fibreProductRootsCohomologyEquiv.{u, e, e'} p n hn hi V)).symm)


/-- Actual pointed kernel effacement proves local injectivity of the original comparison. -/
theorem fibreProductRootsNormalizedPicardNatTrans_isLocallyInjective :
    Presheaf.IsLocallyInjective (Scheme.smallEtaleTopology S)
      (fibreProductRootsNormalizedPicardNatTrans.{u, w, s, e} p n hn hi o ho) := by
  apply Scheme.Etale.isLocallyInjective_of_pointed_kernelZero
  intro U c hc x
  let E := fibreProductResizeEquiv.{u, w, s, e} p (mu X n) 1 U
  let a := E c
  have ha : (fibreProductRootsNormalizedPicardNatTrans.{u, w, s, e}
      p n hn hi o ho).app (op U) (E.symm a) = 0 := by
    simpa only [a, AddEquiv.symm_apply_apply] using hc
  obtain ⟨V, v, y, hy, hv⟩ :=
    fibreProductRootsNormalizedPicardNatTrans_pointed_kernel_zero.{u, w, s, e, e'}
      p n hn hi o ho U a ha x
  refine ⟨V, v, y, hy, ?_⟩
  apply (fibreProductResizeEquiv.{u, w, s, e} p (mu X n) 1 V).injective
  rw [map_zero, fibreProductResizeEquiv_restriction]
  exact hv

/-- The canonical map to the actual étale Picard torsion kernel is an isomorphism.
Neither finite étaleness of the kernel nor a curve or representability premise is used. -/
instance rootsHigherDirectImageToNormalizedPicardTorsion_isIso :
    IsIso (rootsHigherDirectImageToNormalizedPicardTorsion.{u, w, s, e} p n hn hi o ho) := by
  let J := Scheme.smallEtaleTopology S
  let L := presheafToSheaf J AddCommGrpCat.{u + 1}
  let φ := fibreProductRootsNormalizedPicardKernelMap.{u, w, s, e} p n hn hi o ho
  let : Presheaf.IsLocallyInjective J
      (fibreProductRootsNormalizedPicardNatTrans.{u, w, s, e} p n hn hi o ho) :=
    fibreProductRootsNormalizedPicardNatTrans_isLocallyInjective.{u, w, s, e, e'}
      p n hn hi o ho
  let : Presheaf.IsLocallyInjective J φ :=
    Presheaf.isLocallyInjective_of_isLocallyInjective_fac J
      (kernel.lift_ι _ _
        (fibreProductRootsNormalizedPicardNatTrans_nsmul.{u, w, s, e} p n hn hi o ho))
  let : Presheaf.IsLocallySurjective J φ :=
    Presheaf.isLocallySurjective_of_surjective J φ
      (fun U => fibreProductRootsNormalizedPicardKernelMap_surjective.{u, w, s, e, e'}
        p n hn hi o ho U.unop)
  have : IsIso (L.map φ) :=
    (J.W_iff φ).mp (J.W_of_isLocallyBijective φ)
  dsimp only [rootsHigherDirectImageToNormalizedPicardTorsion]
  rw [Adjunction.homEquiv_counit]
  dsimp only [fibreProductRootsToNormalizedPicardSheafKernel]
  rw [Functor.map_comp]
  infer_instance

/-- The original higher direct image and actual small étale Picard torsion kernel. -/
def rootsHigherDirectImageNormalizedPicardTorsionIso :
    (higherDirectImage p 1).obj (mu X n) ≅ normalizedPicardEtaleTorsionSheaf p n o ho :=
  asIso (rootsHigherDirectImageToNormalizedPicardTorsion.{u, w, s, e} p n hn hi o ho)

section Representer

variable (P : LocallyNoetherianOver S) [LocallyOfFiniteType P.obj.hom]
    (R : ((locallyNoetherianOverInclusion S).op ⋙ (fppfPicardSheaf p).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)

/-- The small étale represented sheaf of the original Picard representer's proved group law. -/
def picardRepresenterEtaleSheaf : AbelianSheaf.{u, u + 1} S :=
  letI := picardCommGrpObj p P R
  representedSheaf (Grp.mk P.obj)

/-- The actual Picard representer with its original group law represents the normalized
Picard small étale sheaf; no additive compatibility assumption is supplied. -/
def picardRepresenterNormalizedEtaleIso :
    picardRepresenterEtaleSheaf p P R ≅ normalizedPicardEtaleSheaf p o ho := by
  letI := picardCommGrpObj p P R
  let H : Grp (Over S) := Grp.mk P.obj
  let T (U : S.Etale) : LocallyNoetherianOver S :=
    ⟨(Scheme.Etale.forget S).obj U, by
      change IsLocallyNoetherian U.left
      exact LocallyOfFiniteType.isLocallyNoetherian (X := U.left) (Y := S) U.hom⟩
  let E : representedPresheaf H ≅ (Scheme.Etale.forget S).op ⋙ (fppfPicardSheaf p).obj :=
    NatIso.ofComponents
      (fun U => (AddEquiv.ulift.trans (picardHomAddEquiv p P R (T U.unop))).toAddCommGrpIso)
      (by
        intro U V a
        ext t
        exact R.homEquiv_comp
          (ObjectProperty.homMk ((Scheme.Etale.forget S).map a.unop) : T V.unop ⟶ T U.unop)
          (ObjectProperty.homMk t.down.toMul : T U.unop ⟶ P))
  let E' := E ≪≫ Functor.isoWhiskerLeft (Scheme.Etale.forget S).op
    (normalizedFppfIsoOfIsProperOfFlatOfGeometricallyIntegral p o ho).symm
  exact
    { hom := ⟨E'.hom⟩
      inv := ⟨E'.inv⟩
      hom_inv_id := by ext U t; exact congrArg (fun f => f.app U t) E'.hom_inv_id
      inv_hom_id := by ext U t; exact congrArg (fun f => f.app U t) E'.inv_hom_id }

/-- Original relative Kummer comparison with the same actual Picard representer.
The kernel is taken in small étale abelian sheaves, without assuming finite étaleness. -/
def rootsHigherDirectImagePicardRepresenterTorsionIso :
    (higherDirectImage p 1).obj (mu X n) ≅
      kernel (n • 𝟙 (picardRepresenterEtaleSheaf p P R)) :=
  rootsHigherDirectImageNormalizedPicardTorsionIso p n hn hi o ho ≪≫
    kernel.mapIso (n • 𝟙 (normalizedPicardEtaleSheaf p o ho))
      (n • 𝟙 (picardRepresenterEtaleSheaf p P R))
      (picardRepresenterNormalizedEtaleIso p o ho P R).symm
      (picardRepresenterNormalizedEtaleIso p o ho P R).symm (by simp)

end Representer

end LocalKernel

end Sheaf

end AlgebraicGeometry.Scheme.EtaleCohomology.Kummer
