/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.FiniteLocallyConstant.TriangleCoherence
public import Aglib.AlgebraicGeometry.Cohomology.EtaleH1.PointedCoefficientNaturality
public import Aglib.GroupCohomology.H1.SplitInflation

/-!
Native migration from
`R5Lab.Aglib.AlgebraicGeometry.Cohomology.FiniteLocallyConstant.SectionComparison` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`b3c9125a74c7982aad1802aae9751b40e17437375d0d97a10eb64fa5fbf3d7c4`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

open _root_.AlgebraicGeometry.Scheme.EtaleH1

noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj CategoryTheory.PreGaloisCategory
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (fiberToFinite)
open AlgebraicGeometry.Scheme.EtaleH1
open _root_.AlgebraicGeometry.Scheme.EtaleH1.PointedNaturality
open _root_.AlgebraicGeometry.Scheme.EtaleH1.FundamentalGroupComparison
open _root_.AlgebraicGeometry.Scheme.EtaleFundamentalGroups
open _root_.AlgebraicGeometry.Scheme.FiniteEtale.FiberTorsorActions
open _root_.GroupCohomology _root_.TopologicalGroup
namespace AlgebraicGeometry.Scheme.EtaleH1.SectionComparison
open _root_.AlgebraicGeometry.Scheme.EtaleH1.SheafCoherence
universe u v w wB wK
attribute [local instance] Over.cartesianMonoidalCategory hasSheafifyLarge
/-- The actual inverse-image triangle identifies iterated intrinsic H1 pullback. -/
theorem triangle_pullback {B X Y : Scheme.{u}}
    [HasExt.{wB} (AbelianSheaf.{u, u + 1} B)]
    [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
    [HasExt.{wK} (AbelianSheaf.{u, u + 1} Y)]
    (p : X ⟶ B) (f : Y ⟶ X) (q : Y ⟶ B) (h : f ≫ p = q)
    (L : AbelianSheaf.{u, u + 1} B) (a : H1Etale B L) :
    coefficientMap (AlgebraicGeometry.Scheme.EtaleH1.TriangleCoherence.triangleIso p f q h L).hom
      (h1Pullback f ((inverseImage p).obj L) (h1Pullback p L a)) = h1Pullback q L a := by
  subst q
  simp only [AlgebraicGeometry.Scheme.EtaleH1.TriangleCoherence.triangleIso, Iso.trans_hom,
      Iso.symm_hom,
    Iso.app_inv, eqToIso_refl, Iso.refl_hom, Category.comp_id]
  change (coefficientIso ((inverseImageComp p f).app L)).symm
    (h1Pullback f _ (h1Pullback p L a)) = _
  rw [← h1Pullback_comp p f L a]
  exact (coefficientIso ((inverseImageComp p f).app L)).symm_apply_apply _

section SplitInflation
variable {G E : Type*} [Group G] [Group E]
  [TopologicalSpace G] [TopologicalSpace E] [IsTopologicalGroup E]
  (π : E →ₜ* G) (s : G →ₜ* E) (hs : ∀ g, π (s g) = g)
  (n : ℕ) [TopologicalSpace (ZMod n)] [IsTopologicalAddGroup (ZMod n)]
  [DistribMulAction G (ZMod n)] [ContinuousSMul G (ZMod n)]

/-- The genuine split coordinate equivalence carries group restriction to the existing base
inflation. -/
theorem split_inflation (a : _root_.GroupCohomology.ContinuousH1.H1 G (ZMod n)) :
    letI := _root_.GroupCohomology.ContinuousH1.restrictedAction (ZMod n) π
    letI := _root_.GroupCohomology.ContinuousH1.restrictedAction_continuous (ZMod n) π
    letI := _root_.TopologicalGroup.SplitExtension.kernelAction π.toMonoidHom s.toMonoidHom
    _root_.GroupCohomology.SplitCoordinates.h1AddEquiv (A := ZMod n) π s hs
      (_root_.GroupCohomology.ContinuousH1.restriction (ZMod n) π a) =
        _root_.GroupCohomology.PointedCohomology.baseInflation (N := π.toMonoidHom.ker)
          (_root_.GroupCohomology.SplitCoordinates.sectionH1AddEquiv G (ZMod n) a) := by
  let := _root_.GroupCohomology.ContinuousH1.restrictedAction (ZMod n) π
  let := _root_.GroupCohomology.ContinuousH1.restrictedAction_continuous (ZMod n) π
  let := _root_.TopologicalGroup.SplitExtension.kernelAction π.toMonoidHom s.toMonoidHom
  obtain ⟨c, rfl⟩ := _root_.GroupCohomology.ContinuousH1.classOf_surjective G (ZMod n) a
  change _root_.GroupCohomology.PointedCohomology.continuousH1Mk _ =
      _root_.GroupCohomology.PointedCohomology.continuousH1Mk _
  congr 1
  apply _root_.GroupCohomology.PointedCohomology.ContinuousCocycle.ext
  rintro ⟨k, g⟩
  change c.val (π (_root_.TopologicalGroup.SplitExtension.fromCoordinates π.toMonoidHom
      s.toMonoidHom (k, g))) = c.val g
  exact congrArg c.val (_root_.TopologicalGroup.SplitExtension.projection_fromCoordinates
      π.toMonoidHom s.toMonoidHom hs (k, g))

end SplitInflation

section IdentityRepresentation
variable {B : Scheme.{u}} {L : Type u} [Field L]
  (b : Spec (.of L) ⟶ B)
  [GaloisCategory (Scheme.FiniteEtale B)] [PreGaloisCategory.FiberFunctor (fiberToFinite b)]
  [PreconnectedSpace B] [HasExt.{wB} (AbelianSheaf.{u, u + 1} B)]
  (hAB : Stacks03AJ.{u, wB} B) (hRB : Stacks03RV B)
  (A : Grp (Over B)) [IsCommMonObj A.X] [IsFinite A.X.hom] [Etale A.X.hom]
  (M : Type v) [AddCommGroup M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction (FiberAutGroup b) M] [ContinuousSMul (FiberAutGroup b) M]
  (mark : (Over.mk b ⟶ A.X) ≃* Multiplicative M)
  (hmark : ∀ (γ : FiberAutGroup b) a,
    mark (γ.hom.app (coefficientCover A) a) = Multiplicative.ofAdd (γ • (mark a).toAdd))
  (hc : FiniteCoefficient (representedSheaf A))

/-- The identity additive representation leaves the actual represented H1 comparison unchanged. -/
theorem compare_identityRepresentation (a : H1Etale B (representedSheaf A)) :
    compareH1WithRepresentation b hAB hRB (representedSheaf A) (identityRepresentation A)
      M mark hmark hc a = representedH1AddEquiv b A hAB hRB M mark hmark hc a := by
  change representedH1AddEquiv b A hAB hRB M mark hmark hc
    (coefficientMap (𝟙 (representedSheaf A)) a) = _
  rw [coefficientMap_id]
  rfl

variable {X : Scheme.{u}} (p : X ⟶ B) (o : B ⟶ X) (ho : o ≫ p = 𝟙 _)
  [GaloisCategory (Scheme.FiniteEtale X)] [PreGaloisCategory.FiberFunctor (fiberToFinite (b ≫ o))]
  [PreconnectedSpace X] [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  (hAX : Stacks03AJ.{u, w} X) (hRX : Stacks03RV X)

omit [GaloisCategory (Scheme.FiniteEtale B)]
  [PreGaloisCategory.FiberFunctor (fiberToFinite b)] [PreconnectedSpace B]
  [HasExt.{wB} (AbelianSheaf.{u, u + 1} B)] in
/-- The same identity-representation simplification for the actual pulled-back comparison. -/
-- Retain the original base fibre functor, connectedness and independent Ext-universe input.
@[nolint unusedArguments]
theorem generalBase_identityRepresentation
    [GaloisCategory (Scheme.FiniteEtale B)]
    [PreGaloisCategory.FiberFunctor (fiberToFinite b)] [PreconnectedSpace B]
    [HasExt.{wB} (AbelianSheaf.{u, u + 1} B)] (a : H1Etale X ((inverseImage p).obj
    (representedSheaf A))) :
    letI := _root_.GroupCohomology.ContinuousH1.restrictedAction M (projection b p o ho)
    letI := _root_.GroupCohomology.ContinuousH1.restrictedAction_continuous M (projection b p o ho)
    generalBaseH1AddEquiv b p o ho hAX hRX (representedSheaf A) (identityRepresentation A)
      M mark hmark hc a = baseH1AddEquiv b p o ho hAX hRX A M mark hmark hc a := by
  let := _root_.GroupCohomology.ContinuousH1.restrictedAction M (projection b p o ho)
  let := _root_.GroupCohomology.ContinuousH1.restrictedAction_continuous M (projection b p o ho)
  change baseH1AddEquiv b p o ho hAX hRX A M mark hmark hc
    (coefficientMap ((inverseImage p).map (𝟙 (representedSheaf A))) a) = _
  rw [CategoryTheory.Functor.map_id, coefficientMap_id]
  rfl

/-- Actual section naturality for a represented coefficient, with identity transports already
canceled. -/
theorem represented_origin_square [IsSepClosed L]
    (a : H1Etale X ((inverseImage p).obj (representedSheaf A))) :
    letI := _root_.GroupCohomology.ContinuousH1.restrictedAction M (projection b p o ho)
    letI := _root_.GroupCohomology.ContinuousH1.restrictedAction_continuous M (projection b p o ho)
    representedH1AddEquiv b A hAB hRB M mark hmark hc
      (sectionPullback p o ho (representedSheaf A) a) =
      _root_.GroupCohomology.SplitCoordinates.sectionRestriction (A := M) (projection b p o ho)
          (sectionHom b o)
        (projection_section b p o ho)
        (baseH1AddEquiv b p o ho hAX hRX A M mark hmark hc a) := by
  let := _root_.GroupCohomology.ContinuousH1.restrictedAction M (projection b p o ho)
  let := _root_.GroupCohomology.ContinuousH1.restrictedAction_continuous M (projection b p o ho)
  have hs := general_origin_square b p o ho hAB hAX hRB hRX (representedSheaf A)
    (identityRepresentation A) M mark hmark hc a
  rw [compare_identityRepresentation, generalBase_identityRepresentation] at hs
  exact hs

end IdentityRepresentation

end AlgebraicGeometry.Scheme.EtaleH1.SectionComparison
