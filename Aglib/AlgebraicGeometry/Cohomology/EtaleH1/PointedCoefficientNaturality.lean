/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

/- Current interface basis: 46f53465aaf3b0167049e9c8e9e2294111bb4281.
Original construction and mathematical provenance are retained below. -/
public import Aglib.AlgebraicGeometry.Cohomology.EtaleH1.PointedNaturality
public import Aglib.GroupCohomology.H1.SplitCoordinateNaturality

/-!
# Coefficient naturality for actual pointed étale H¹

Generic A5/A6 support for `K2-018#eq:k2018-coefficient-compatibility` and
`K2-018#eq:k2018-pointed-character`, frozen engineering basis
`7f86e4a1763cc4ec35e9b0a8acd659750355a0de`.
Actual coefficient maps are pulled back as sheaf morphisms. Their geometric
marking square is proved from the actual pullback adjunction. The actual
section kernel is then identified with the common section kernel and the
existing pointed-coordinate presentation by already proved squares.
-/

@[expose] public section

noncomputable section
set_option maxRecDepth 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.PreGaloisCategory
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (fiberToFinite)
open AlgebraicGeometry.Scheme.EtaleFundamentalGroups
open AlgebraicGeometry.Scheme.FiniteEtale.FiberTorsorActions
open AlgebraicGeometry.Scheme.FiniteEtale.GroupBaseChange
namespace AlgebraicGeometry.Scheme.EtaleH1.PointedCoefficientNaturality
open Naturality FundamentalGroupComparison PointedNaturality
open GroupCohomology.SplitCoordinateNaturality
open GroupCohomology.ContinuousH1
universe u v v' w w'
attribute [local instance] Over.cartesianMonoidalCategory hasSheafifyLarge

section PointMarking
variable {X S : Scheme.{u}} {K : Type u} [Field K]
variable (f : S ⟶ X) (s : Spec (CommRingCat.of K) ⟶ S)
variable (x : Spec (CommRingCat.of K) ⟶ X) (hx : s ≫ f = x)
variable (A D : Grp (Over X)) [IsCommMonObj A.X] [IsCommMonObj D.X]
variable [IsFinite A.X.hom] [Etale A.X.hom] [IsFinite D.X.hom] [Etale D.X.hom]
variable (M : Type v) (N : Type v') [AddCommGroup M] [AddCommGroup N]
variable (markA : (Over.mk x ⟶ A.X) ≃* Multiplicative M)
variable (markD : (Over.mk x ⟶ D.X) ≃* Multiplicative N)

/-- Canonical pointed pullback coefficient markings commute with the actual
base-changed group morphism, by the actual pullback adjunction on points. -/
theorem pointedPullbackFiberMark_naturality (q : A ⟶ D) (ψ : M →+ N)
    (hq : ∀ a : Over.mk x ⟶ A.X, (markD (a ≫ q.hom.hom)).toAdd = ψ (markA a).toAdd)
    (a : Over.mk s ⟶ (baseChangedGroup f A).X) :
    (pointedPullbackFiberMark f s x hx D N markD
      (a ≫ ((Over.pullback f).mapGrp.map q).hom.hom)).toAdd =
      ψ (pointedPullbackFiberMark f s x hx A M markA a).toAdd := by
  subst x
  change (markD ((pullbackFiberMulEquiv f s D).symm
    (a ≫ (Over.pullback f).map q.hom.hom))).toAdd =
    ψ (markA ((pullbackFiberMulEquiv f s A).symm a)).toAdd
  have hn : (pullbackFiberMulEquiv f s D).symm
      (a ≫ (Over.pullback f).map q.hom.hom) =
        (pullbackFiberMulEquiv f s A).symm a ≫ q.hom.hom :=
    (Over.mapPullbackAdj f).homEquiv_naturality_right_symm (X := Over.mk s) a q.hom.hom
  rw [hn]
  exact hq _

end PointMarking

section RepresentedCoefficients
variable {B X : Scheme.{u}} {K : Type u} [Field K]
variable (b : Spec (CommRingCat.of K) ⟶ B) (p : X ⟶ B)
variable (o : B ⟶ X) (h : o ≫ p = 𝟙 B)
variable [GaloisCategory (Scheme.FiniteEtale B)] [PreGaloisCategory.FiberFunctor (fiberToFinite b)]
variable [GaloisCategory (Scheme.FiniteEtale X)] [PreGaloisCategory.FiberFunctor
  (fiberToFinite (b ≫ o))]
variable [PreconnectedSpace B] [PreconnectedSpace X]
variable [HasExt.{w} (AbelianSheaf.{u, u + 1} B)] [HasExt.{w'} (AbelianSheaf.{u, u + 1} X)]
variable (hAX : Stacks03AJ.{u, w'} X) (hRX : Stacks03RV X)
variable (A D : Grp (Over B)) [IsCommMonObj A.X] [IsCommMonObj D.X]
variable [IsFinite A.X.hom] [Etale A.X.hom] [IsFinite D.X.hom] [Etale D.X.hom]
variable (M : Type v) (N : Type v') [AddCommGroup M] [AddCommGroup N] [Finite M] [Finite N]
variable [TopologicalSpace M] [TopologicalSpace N] [DiscreteTopology M] [DiscreteTopology N]
variable [DistribMulAction (FiberAutGroup b) M] [ContinuousSMul (FiberAutGroup b) M]
variable [DistribMulAction (FiberAutGroup b) N] [ContinuousSMul (FiberAutGroup b) N]
variable (markA : (Over.mk b ⟶ A.X) ≃* Multiplicative M)
variable (markD : (Over.mk b ⟶ D.X) ≃* Multiplicative N)
variable (hmarkA : ∀ (γ : FiberAutGroup b) a,
  markA (γ.hom.app (coefficientCover A) a) = Multiplicative.ofAdd (γ • (markA a).toAdd))
variable (hmarkD : ∀ (γ : FiberAutGroup b) a,
  markD (γ.hom.app (coefficientCover D) a) = Multiplicative.ofAdd (γ • (markD a).toAdd))
variable (hcoeffA : FiniteCoefficient (representedSheaf A)) (hcoeffD : FiniteCoefficient
  (representedSheaf D))

set_option linter.unusedSectionVars false in
-- Preserve the original auto-included hypotheses and binder order.
/-- The comparison on actual pulled-back represented coefficients is natural
for every actual coefficient group morphism and its genuine base marking. -/
-- Keep the original supplied class/data inputs and binder order of this interface.
@[nolint unusedArguments]
theorem baseH1AddEquiv_coefficient (q : A ⟶ D) (ψ : CoefficientMap (FiberAutGroup b) M N)
    (hq : ∀ a : Over.mk b ⟶ A.X, (markD (a ≫ q.hom.hom)).toAdd = ψ (markA a).toAdd)
    (a : H1Etale.{u, u + 1, w'} X ((inverseImage p).obj (representedSheaf A))) :
    letI := restrictedAction M (projection b p o h)
    letI := restrictedAction N (projection b p o h)
    letI := restrictedAction_continuous M (projection b p o h)
    letI := restrictedAction_continuous N (projection b p o h)
    baseH1AddEquiv b p o h hAX hRX D N markD hmarkD hcoeffD
      (coefficientMap ((inverseImage p).map (representedSheafMap q)) a) =
      (inflatedCoefficientMap (projection b p o h) ψ).onH1
        (baseH1AddEquiv b p o h hAX hRX A M markA hmarkA hcoeffA a) := by
  let := restrictedAction M (projection b p o h)
  let := restrictedAction N (projection b p o h)
  let := restrictedAction_continuous M (projection b p o h)
  let := restrictedAction_continuous N (projection b p o h)
  have hc : coefficientMap (representedSheafBaseChangeIso p D).hom
      (coefficientMap ((inverseImage p).map (representedSheafMap q)) a) =
      coefficientMap (representedSheafMap ((Over.pullback p).mapGrp.map q))
        (coefficientMap (representedSheafBaseChangeIso p A).hom a) := by
    change ((coefficientMap (representedSheafBaseChangeIso p D).hom).comp
      (coefficientMap ((inverseImage p).map (representedSheafMap q)))) a =
      ((coefficientMap (representedSheafMap ((Over.pullback p).mapGrp.map q))).comp
        (coefficientMap (representedSheafBaseChangeIso p A).hom)) a
    rw [← coefficientMap_comp, ← coefficientMap_comp, representedSheafBaseChangeIso_naturality]
  change representedH1AddEquiv (b ≫ o) (baseChangedGroup p D) hAX hRX N
    (pointedPullbackFiberMark p (b ≫ o) b (projection_point b p o h) D N markD)
    (pointedPullbackFiberMark_equivariant p (b ≫ o) b (projection_point b p o h) D N markD hmarkD)
    (pulledBackFiniteCoefficient p D hcoeffD)
    (coefficientMap (representedSheafBaseChangeIso p D).hom
      (coefficientMap ((inverseImage p).map (representedSheafMap q)) a)) = _
  rw [hc]
  exact representedH1AddEquiv_coefficient (b ≫ o) (baseChangedGroup p A) (baseChangedGroup p D)
    hAX hRX M N (pointedPullbackFiberMark p (b ≫ o) b (projection_point b p o h) A M markA)
    (pointedPullbackFiberMark p (b ≫ o) b (projection_point b p o h) D N markD)
    (pointedPullbackFiberMark_equivariant p (b ≫ o) b (projection_point b p o h) A M markA hmarkA)
    (pointedPullbackFiberMark_equivariant p (b ≫ o) b (projection_point b p o h) D N markD hmarkD)
    (pulledBackFiniteCoefficient p A hcoeffA) (pulledBackFiniteCoefficient p D hcoeffD)
    ((Over.pullback p).mapGrp.map q) (inflatedCoefficientMap (projection b p o h) ψ)
    (pointedPullbackFiberMark_naturality p (b ≫ o) b (projection_point b p o h) A D M N
      markA markD q ψ.toAddMonoidHom hq) _

end RepresentedCoefficients

section GeneralCoefficients
variable {B X : Scheme.{u}} {K : Type u} [Field K]
variable (b : Spec (CommRingCat.of K) ⟶ B) (p : X ⟶ B)
variable (o : B ⟶ X) (h : o ≫ p = 𝟙 B)
variable [GaloisCategory (Scheme.FiniteEtale B)] [PreGaloisCategory.FiberFunctor (fiberToFinite b)]
variable [GaloisCategory (Scheme.FiniteEtale X)] [PreGaloisCategory.FiberFunctor
  (fiberToFinite (b ≫ o))]
variable [PreconnectedSpace B] [PreconnectedSpace X]
variable [HasExt.{w} (AbelianSheaf.{u, u + 1} B)] [HasExt.{w'} (AbelianSheaf.{u, u + 1} X)]
variable (hAX : Stacks03AJ.{u, w'} X) (hRX : Stacks03RV X)
variable {L D : AbelianSheaf.{u, u + 1} B} (R : CoefficientRepresentation L) (T :
  CoefficientRepresentation D)
variable (M : Type v) (N : Type v') [AddCommGroup M] [AddCommGroup N] [Finite M] [Finite N]
variable [TopologicalSpace M] [TopologicalSpace N] [DiscreteTopology M] [DiscreteTopology N]
variable [DistribMulAction (FiberAutGroup b) M] [ContinuousSMul (FiberAutGroup b) M]
variable [DistribMulAction (FiberAutGroup b) N] [ContinuousSMul (FiberAutGroup b) N]
variable (markL : (Over.mk b ⟶ R.group.X) ≃* Multiplicative M)
variable (markD : (Over.mk b ⟶ T.group.X) ≃* Multiplicative N)
variable (hmarkL : ∀ (γ : FiberAutGroup b) a,
  markL (γ.hom.app (coefficientCover R.group) a) = Multiplicative.ofAdd (γ • (markL a).toAdd))
variable (hmarkD : ∀ (γ : FiberAutGroup b) a,
  markD (γ.hom.app (coefficientCover T.group) a) = Multiplicative.ofAdd (γ • (markD a).toAdd))
variable (hcoeffL : FiniteCoefficient L) (hcoeffD : FiniteCoefficient D)

/-- The actual inverse-image coefficient square for arbitrary finite locally
constant sheaves, reduced through their genuine additive representing maps. -/
theorem generalBaseH1AddEquiv_coefficient (q : L ⟶ D) (ψ : CoefficientMap (FiberAutGroup b) M N)
    (hq : ∀ a : Over.mk b ⟶ R.group.X,
      (markD (a ≫ (R.map T q).hom.hom)).toAdd = ψ (markL a).toAdd)
    (a : H1Etale.{u, u + 1, w'} X ((inverseImage p).obj L)) :
    letI := restrictedAction M (projection b p o h)
    letI := restrictedAction N (projection b p o h)
    letI := restrictedAction_continuous M (projection b p o h)
    letI := restrictedAction_continuous N (projection b p o h)
    generalBaseH1AddEquiv b p o h hAX hRX D T N markD hmarkD hcoeffD
      (coefficientMap ((inverseImage p).map q) a) =
      (inflatedCoefficientMap (projection b p o h) ψ).onH1
        (generalBaseH1AddEquiv b p o h hAX hRX L R M markL hmarkL hcoeffL a) := by
  let := restrictedAction M (projection b p o h)
  let := restrictedAction N (projection b p o h)
  let := restrictedAction_continuous M (projection b p o h)
  let := restrictedAction_continuous N (projection b p o h)
  have hc : coefficientMap ((inverseImage p).map T.iso.inv)
      (coefficientMap ((inverseImage p).map q) a) =
      coefficientMap ((inverseImage p).map (representedSheafMap (R.map T q)))
        (coefficientMap ((inverseImage p).map R.iso.inv) a) := by
    change ((coefficientMap ((inverseImage p).map T.iso.inv)).comp
      (coefficientMap ((inverseImage p).map q))) a =
      ((coefficientMap ((inverseImage p).map (representedSheafMap (R.map T q)))).comp
        (coefficientMap ((inverseImage p).map R.iso.inv))) a
    rw [← coefficientMap_comp, ← coefficientMap_comp, ← Functor.map_comp,
      ← Functor.map_comp, R.map_square T q]
  change baseH1AddEquiv b p o h hAX hRX T.group N markD hmarkD (hcoeffD.ofIso T.iso)
    (coefficientMap ((inverseImage p).map T.iso.inv)
      (coefficientMap ((inverseImage p).map q) a)) = _
  rw [hc]
  exact baseH1AddEquiv_coefficient b p o h hAX hRX R.group T.group M N markL markD
    hmarkL hmarkD (hcoeffL.ofIso R.iso) (hcoeffD.ofIso T.iso) (R.map T q) ψ hq _

end GeneralCoefficients

section OriginKernel
variable {B X : Scheme.{u}}
variable (p : X ⟶ B) (o : B ⟶ X) (h : o ≫ p = 𝟙 B)
variable [HasExt.{w} (AbelianSheaf.{u, u + 1} B)] [HasExt.{w'} (AbelianSheaf.{u, u + 1} X)]

/-- Actual étale classes whose pullback to the chosen section is zero. -/
def OriginKernel (L : AbelianSheaf.{u, u + 1} B) :
    AddSubgroup (H1Etale.{u, u + 1, w'} X ((inverseImage p).obj L)) :=
  (sectionPullback p o h L).ker

/-- Coefficient maps preserve the actual origin kernel by section naturality. -/
def originKernelCoefficientMap {L D : AbelianSheaf.{u, u + 1} B} (q : L ⟶ D) :
    OriginKernel p o h L →+ OriginKernel p o h D where
  toFun a := ⟨coefficientMap ((inverseImage p).map q) a.val, by
    change sectionPullback p o h D _ = 0
    rw [sectionPullback_coefficient]
    have ha : sectionPullback p o h L a.val = 0 := a.property
    rw [ha, map_zero]⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' a c := Subtype.ext (map_add _ _ _)

/-- The actual origin-kernel map has the prescribed inverse-image coefficient map. -/
@[simp] theorem originKernelCoefficientMap_coe {L D : AbelianSheaf.{u, u + 1} B}
    (q : L ⟶ D) (a : OriginKernel p o h L) :
    (originKernelCoefficientMap p o h q a).val =
      coefficientMap ((inverseImage p).map q) a.val := rfl

end OriginKernel

section OriginComparison
open GroupCohomology TopologicalGroup
variable {B X : Scheme.{u}} {K : Type u} [Field K] [IsSepClosed K]
variable (b : Spec (CommRingCat.of K) ⟶ B) (p : X ⟶ B)
variable (o : B ⟶ X) (h : o ≫ p = 𝟙 B)
variable [GaloisCategory (Scheme.FiniteEtale B)] [PreGaloisCategory.FiberFunctor (fiberToFinite b)]
variable [GaloisCategory (Scheme.FiniteEtale X)] [PreGaloisCategory.FiberFunctor
  (fiberToFinite (b ≫ o))]
variable [PreconnectedSpace B] [PreconnectedSpace X]
variable [HasExt.{w} (AbelianSheaf.{u, u + 1} B)] [HasExt.{w'} (AbelianSheaf.{u, u + 1} X)]
variable (hAB : Stacks03AJ.{u, w} B) (hAX : Stacks03AJ.{u, w'} X)
variable (hRB : Stacks03RV B) (hRX : Stacks03RV X)
variable (L : AbelianSheaf.{u, u + 1} B) (R : CoefficientRepresentation L)
variable (M : Type v) [AddCommGroup M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
variable [DistribMulAction (FiberAutGroup b) M] [ContinuousSMul (FiberAutGroup b) M]
variable (mark : (Over.mk b ⟶ R.group.X) ≃* Multiplicative M)
variable (hmark : ∀ (γ : FiberAutGroup b) a,
  mark (γ.hom.app (coefficientCover R.group) a) = Multiplicative.ofAdd (γ • (mark a).toAdd))
variable (hcoeff : FiniteCoefficient L)

/-- The actual origin kernel is the kernel of continuous restriction along the
actual group section. Both directions are the already constructed comparison
on underlying classes; the kernel proofs use the proved actual origin square. -/
def originKernelComparison : OriginKernel.{u, w, w'} p o h L ≃+
    GroupCohomology.SplitCoordinates.PointedKernel (A := M) (projection b p o h) (sectionHom b o)
      (projection_section b p o h) := by
  letI := restrictedAction M (projection b p o h)
  letI := restrictedAction_continuous M (projection b p o h)
  let κX := generalBaseH1AddEquiv b p o h hAX hRX L R M mark hmark hcoeff
  let κB := compareH1WithRepresentation b hAB hRB L R M mark hmark hcoeff
  exact {
    toFun a := ⟨κX a.val, by
      change GroupCohomology.SplitCoordinates.sectionRestriction (A := M) (projection b p o h)
        (sectionHom b o) (projection_section b p o h) (κX a.val) = 0
      rw [← general_origin_square b p o h hAB hAX hRB hRX L R M mark hmark hcoeff]
      have ha : sectionPullback p o h L a.val = 0 := a.property
      rw [ha, map_zero]⟩
    invFun a := ⟨κX.symm a.val, by
      change sectionPullback p o h L (κX.symm a.val) = 0
      apply κB.injective
      rw [map_zero]
      change compareH1WithRepresentation b hAB hRB L R M mark hmark hcoeff
        (sectionPullback p o h L (κX.symm a.val)) = 0
      rw [general_origin_square b p o h hAB hAX hRB hRX L R M mark hmark hcoeff]
      change GroupCohomology.SplitCoordinates.sectionRestriction (A := M) (projection b p o h)
        (sectionHom b o) (projection_section b p o h) (κX (κX.symm a.val)) = 0
      rw [κX.apply_symm_apply]
      exact a.property⟩
    left_inv a := Subtype.ext (κX.symm_apply_apply a.val)
    right_inv a := Subtype.ext (κX.apply_symm_apply a.val)
    map_add' a c := Subtype.ext (map_add κX a.val c.val) }

/-- The forward kernel comparison is literally the actual pulled-back H1 comparison. -/
@[simp] theorem originKernelComparison_coe (a : OriginKernel p o h L) :
    (originKernelComparison b p o h hAB hAX hRB hRX L R M mark hmark hcoeff a).val =
      generalBaseH1AddEquiv b p o h hAX hRX L R M mark hmark hcoeff a.val := rfl

/-- The actual origin kernel in the frozen common pointed H1 presentation. -/
def originKernelPointedH1Equiv :
    letI := TopologicalGroup.SplitExtension.kernelAction (projection b p o h).toMonoidHom
      (sectionHom b o).toMonoidHom
    OriginKernel.{u, w, w'} p o h L ≃+
      PointedCohomology.PointedH1 (G := FiberAutGroup b)
        (N := (projection b p o h).toMonoidHom.ker) (A := M) := by
  letI := TopologicalGroup.SplitExtension.kernelAction (projection b p o h).toMonoidHom
    (sectionHom b o).toMonoidHom
  exact (originKernelComparison b p o h hAB hAX hRB hRX L R M mark hmark hcoeff).trans
    (GroupCohomology.SplitCoordinates.pointedH1AddEquiv (projection b p o h) (sectionHom b o)
      (projection_section b p o h))

/-- Actual origin-trivial étale classes as genuine continuous equivariant kernel characters. -/
def originKernelCharacterEquiv :
    letI := TopologicalGroup.SplitExtension.kernelAction (projection b p o h).toMonoidHom
      (sectionHom b o).toMonoidHom
    OriginKernel.{u, w, w'} p o h L ≃+
      PointedCohomology.EquivariantCharacter (FiberAutGroup b)
        (projection b p o h).toMonoidHom.ker M := by
  letI := TopologicalGroup.SplitExtension.kernelAction (projection b p o h).toMonoidHom
    (sectionHom b o).toMonoidHom
  exact (originKernelComparison b p o h hAB hAX hRB hRX L R M mark hmark hcoeff).trans
    (GroupCohomology.SplitCoordinates.pointedCharacterEquiv (projection b p o h) (sectionHom b o)
      (projection_section b p o h))

/-- The geometric representative is literal evaluation of the actual common cocycle
on the actual projection kernel, with the fixed positive-displacement convention. -/
theorem originKernelCharacterEquiv_classOf (a : OriginKernel p o h L)
    (c : GroupCohomology.SplitCoordinates.InflatedCocycle (A := M) (projection b p o h))
    (hc : letI := restrictedAction M (projection b p o h)
      letI := restrictedAction_continuous M (projection b p o h)
      generalBaseH1AddEquiv b p o h hAX hRX L R M mark hmark hcoeff a.val =
        classOf (FiberAutGroup (b ≫ o)) M c)
    (n : (projection b p o h).toMonoidHom.ker) :
    letI := TopologicalGroup.SplitExtension.kernelAction (projection b p o h).toMonoidHom
      (sectionHom b o).toMonoidHom
    (originKernelCharacterEquiv b p o h hAB hAX hRB hRX L R M mark hmark hcoeff a).toFun n =
      c.val n := by
  let := restrictedAction M (projection b p o h)
  let := restrictedAction_continuous M (projection b p o h)
  let := TopologicalGroup.SplitExtension.kernelAction (projection b p o h).toMonoidHom
    (sectionHom b o).toMonoidHom
  change (PointedCohomology.geometricH1Hom
    (GroupCohomology.SplitCoordinates.h1AddEquiv (projection b p o h) (sectionHom b o)
      (projection_section b p o h)
      (generalBaseH1AddEquiv b p o h hAX hRX L R M mark hmark hcoeff a.val))).toFun n = _
  rw [hc]
  exact GroupCohomology.SplitCoordinates.geometric_classOf (projection b p o h) (sectionHom b o)
    (projection_section b p o h) c n

variable (D : AbelianSheaf.{u, u + 1} B) (T : CoefficientRepresentation D)
variable (N : Type v') [AddCommGroup N] [Finite N] [TopologicalSpace N] [DiscreteTopology N]
variable [DistribMulAction (FiberAutGroup b) N] [ContinuousSMul (FiberAutGroup b) N]
variable (markD : (Over.mk b ⟶ T.group.X) ≃* Multiplicative N)
variable (hmarkD : ∀ (γ : FiberAutGroup b) a,
  markD (γ.hom.app (coefficientCover T.group) a) = Multiplicative.ofAdd (γ • (markD a).toAdd))
variable (hcoeffD : FiniteCoefficient D)
variable (q : L ⟶ D) (ψ : CoefficientMap (FiberAutGroup b) M N)
variable (hq : ∀ a : Over.mk b ⟶ R.group.X,
  (markD (a ≫ (R.map T q).hom.hom)).toAdd = ψ (mark a).toAdd)

include hq

/-- Actual origin-kernel comparison commutes with every genuinely marked coefficient map. -/
theorem originKernelComparison_coefficient (a : OriginKernel p o h L) :
    originKernelComparison b p o h hAB hAX hRB hRX D T N markD hmarkD hcoeffD
      (originKernelCoefficientMap p o h q a) =
      pointedKernelMap (projection b p o h) (sectionHom b o) (projection_section b p o h) ψ
        (originKernelComparison b p o h hAB hAX hRB hRX L R M mark hmark hcoeff a) := by
  apply Subtype.ext
  exact generalBaseH1AddEquiv_coefficient b p o h hAX hRX R T M N mark markD
    hmark hmarkD hcoeff hcoeffD q ψ hq a.val

/-- The coefficient square in the frozen pointed common-H1 presentation. -/
theorem originKernelPointedH1Equiv_coefficient (a : OriginKernel p o h L) :
    letI := TopologicalGroup.SplitExtension.kernelAction (projection b p o h).toMonoidHom
      (sectionHom b o).toMonoidHom
    originKernelPointedH1Equiv b p o h hAB hAX hRB hRX D T N markD hmarkD hcoeffD
      (originKernelCoefficientMap p o h q a) =
      CoefficientFunctoriality.pointedH1Map ψ.toAddMonoidHom ψ.continuous ψ.map_smul
        (originKernelPointedH1Equiv b p o h hAB hAX hRB hRX L R M mark hmark hcoeff a) := by
  let := TopologicalGroup.SplitExtension.kernelAction (projection b p o h).toMonoidHom
    (sectionHom b o).toMonoidHom
  change GroupCohomology.SplitCoordinates.pointedH1AddEquiv (projection b p o h) (sectionHom b o)
    (projection_section b p o h)
    (originKernelComparison b p o h hAB hAX hRB hRX D T N markD hmarkD hcoeffD
      (originKernelCoefficientMap p o h q a)) = _
  rw [originKernelComparison_coefficient b p o h hAB hAX hRB hRX L R M mark hmark hcoeff
    D T N markD hmarkD hcoeffD q ψ hq]
  exact pointedH1AddEquiv_naturality (projection b p o h) (sectionHom b o)
    (projection_section b p o h) ψ _

/-- Actual origin-trivial étale coefficient change acts on characters by ψ. -/
theorem originKernelCharacterEquiv_coefficient (a : OriginKernel p o h L) :
    letI := TopologicalGroup.SplitExtension.kernelAction (projection b p o h).toMonoidHom
      (sectionHom b o).toMonoidHom
    originKernelCharacterEquiv b p o h hAB hAX hRB hRX D T N markD hmarkD hcoeffD
      (originKernelCoefficientMap p o h q a) =
      CoefficientFunctoriality.characterMap ψ.toAddMonoidHom ψ.continuous ψ.map_smul
        (originKernelCharacterEquiv b p o h hAB hAX hRB hRX L R M mark hmark hcoeff a) := by
  let := TopologicalGroup.SplitExtension.kernelAction (projection b p o h).toMonoidHom
    (sectionHom b o).toMonoidHom
  change GroupCohomology.SplitCoordinates.pointedCharacterEquiv (projection b p o h) (sectionHom
    b o)
    (projection_section b p o h)
    (originKernelComparison b p o h hAB hAX hRB hRX D T N markD hmarkD hcoeffD
      (originKernelCoefficientMap p o h q a)) = _
  rw [originKernelComparison_coefficient b p o h hAB hAX hRB hRX L R M mark hmark hcoeff
    D T N markD hmarkD hcoeffD q ψ hq]
  exact pointedCharacterEquiv_naturality (projection b p o h) (sectionHom b o)
    (projection_section b p o h) ψ _

end OriginComparison

section BaseGeometricRestriction
open CategoryTheory.Limits
open AlgebraicGeometry.Scheme.FiniteEtale.GeometricKernel
universe w''
variable {B X : Scheme.{u}} {K : Type u} [Field K]
variable (b : Spec (CommRingCat.of K) ⟶ B) (p : X ⟶ B)
variable (o : B ⟶ X) (h : o ≫ p = 𝟙 B)
variable [GaloisCategory (Scheme.FiniteEtale B)] [PreGaloisCategory.FiberFunctor (fiberToFinite b)]
variable [GaloisCategory (Scheme.FiniteEtale X)] [PreGaloisCategory.FiberFunctor
  (fiberToFinite (b ≫ o))]
variable [GaloisCategory (Scheme.FiniteEtale (pullback p b))]
variable [PreGaloisCategory.FiberFunctor (fiberToFinite (baseChangePoint b p o h))]
variable [PreconnectedSpace B] [PreconnectedSpace X]
variable [PreconnectedSpace (pullback p b : Scheme.{u})]
variable [HasExt.{w} (AbelianSheaf.{u, u + 1} B)]
variable [HasExt.{w'} (AbelianSheaf.{u, u + 1} X)]
variable [HasExt.{w''} (AbelianSheaf.{u, u + 1} (pullback p b))]
variable (hAX : Stacks03AJ.{u, w'} X) (hAG : Stacks03AJ.{u, w''} (pullback p b))
variable (hRX : Stacks03RV X) (hRG : Stacks03RV (pullback p b))
variable (L : AbelianSheaf.{u, u + 1} B) (R : CoefficientRepresentation L)
variable (M : Type v) [AddCommGroup M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
variable [DistribMulAction (FiberAutGroup b) M] [ContinuousSMul (FiberAutGroup b) M]
variable (mark : (Over.mk b ⟶ R.group.X) ≃* Multiplicative M)
variable (hmark : ∀ (γ : FiberAutGroup b) a,
  mark (γ.hom.app (coefficientCover R.group) a) = Multiplicative.ofAdd (γ • (mark a).toAdd))
variable (hcoeff : FiniteCoefficient L)

/-- Restriction of actual base-pulled coefficients to the geometric scheme
uses the actual geometric inclusion and the canonical pulled-back marking.
The geometric group is not identified with the projection kernel here. -/
theorem base_geometric_restriction
    (a : H1Etale.{u, u + 1, w'} X ((inverseImage p).obj L)) :
    letI := restrictedAction M (projection b p o h)
    letI := restrictedAction_continuous M (projection b p o h)
    letI := restrictedAction M (geometricInclusion b p o h)
    letI := restrictedAction_continuous M (geometricInclusion b p o h)
    generalGeometricH1AddEquiv b p o h hAG hRG ((inverseImage p).obj L)
      (pulledBackRepresentation p R) M
      (pointedPullbackFiberMark p (b ≫ o) b (projection_point b p o h) R.group M mark)
      (pointedPullbackFiberMark_equivariant p (b ≫ o) b (projection_point b p o h)
        R.group M mark hmark) (hcoeff.pullback p)
      (h1Pullback (pullback.fst p b) ((inverseImage p).obj L) a) =
      restriction M (geometricInclusion b p o h)
        (generalBaseH1AddEquiv b p o h hAX hRX L R M mark hmark hcoeff a) := by
  let := restrictedAction M (projection b p o h)
  let := restrictedAction_continuous M (projection b p o h)
  let := restrictedAction M (geometricInclusion b p o h)
  let := restrictedAction_continuous M (geometricInclusion b p o h)
  have hn := general_geometric_restriction b p o h hAX hAG hRX hRG ((inverseImage p).obj L)
    (pulledBackRepresentation p R) M
    (pointedPullbackFiberMark p (b ≫ o) b (projection_point b p o h) R.group M mark)
    (pointedPullbackFiberMark_equivariant p (b ≫ o) b (projection_point b p o h)
      R.group M mark hmark) (hcoeff.pullback p) a
  exact hn.trans (congrArg (restriction M (geometricInclusion b p o h))
    (generalBaseH1AddEquiv_representation b p o h hAX hRX L R M mark hmark hcoeff a).symm)

end BaseGeometricRestriction

end AlgebraicGeometry.Scheme.EtaleH1.PointedCoefficientNaturality

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 d46b93b6ab5345170d8c337e1072a8301f684396b1372560a01928d462810ac1.
Definitions, hypotheses and universes are retained modulo native names. -/
