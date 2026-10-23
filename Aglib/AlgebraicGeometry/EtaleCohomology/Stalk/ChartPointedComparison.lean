/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.ChartStrictLocalComparison
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.PointedCohomologyLeg
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.FibreProductGermRestriction
/-! # Original strict-local comparison at every pointed etale neighborhood -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Stalk
universe u w s e
attribute [local instance] hasSheafifyLarge
open Continuity Finite.GeometricNeighborhood
section ScalarComposition
universe v
/-- Forget categorical packaging of an original group-map square before specialization. -/
theorem pointedLeg_comp_hom {A B C : AddCommGrpCat.{v}}
    (r : A →+ B) (l : B ⟶ C) (l' : A ⟶ C)
    (h : AddCommGrpCat.ofHom r ≫ l = l') : l.hom.comp r = l'.hom :=
  congrArg (fun t => t.hom) h

universe vM vN vP vQ
/-- Compose a restriction square at the level of complete original additive maps. -/
theorem pointedComparison_hom_square
    {M : Type vM} {N : Type vN} {P : Type vP} {Q : Type vQ}
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [AddCommGroup Q]
    (r : M →+ N) (gM : M →+ P) (gN : N →+ P)
    (lM : M →+ Q) (lN : N →+ Q) (φ : P →+ Q)
    (hg : gN.comp r = gM) (hl : lN.comp r = lM) (hc : φ.comp gN = lN) :
    φ.comp gM = lM :=
  (congrArg (fun g => φ.comp g) hg.symm).trans
    ((congrArg (fun l => l.comp r) hc).trans hl)

universe vA vB
/-- Evaluate a whole lifted comparison square at an original, unlifted class. -/
theorem pointedUliftComparison_apply
    {A : AddCommGrpCat.{vA}} {B C : AddCommGrpCat.{vB}}
    (E : AddCommGrpCat.uliftFunctor.{vB, vA}.obj A ≅
      AddCommGrpCat.uliftFunctor.{vA, vB}.obj B)
    (t : AddCommGrpCat.uliftFunctor.{vA, vB}.obj C ⟶
      AddCommGrpCat.uliftFunctor.{vB, vA}.obj A)
    (p : C ⟶ B) (h : t ≫ E.hom = AddCommGrpCat.uliftFunctor.map p)
    (x : C) (z : A) (hz : t (ULift.up x) = ULift.up z) :
    (AddEquiv.ulift.symm.trans
      (E.addCommGroupIsoToAddEquiv.trans AddEquiv.ulift)) z = p x := by
  have hv := ConcreteCategory.congr_hom h (ULift.up x)
  exact congrArg ULift.down ((congrArg E.hom hz).symm.trans hv)
end ScalarComposition

variable (R Ω : Type u) [CommRing R] [Field Ω] [Algebra R Ω] [IsSepClosed Ω]
  {X S : Scheme.{u}} (j : Spec (.of R) ⟶ S) [Etale j] [Mono j]
  (η : Spec (.of Ω) ⟶ S) (hη : Spec.algebraMap R Ω ≫ j = η) (f : X ⟶ S)
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [∀ U : S.Etale, HasExt.{s} (Sheaf ((Scheme.smallEtaleTopology X).over
    ((siteBaseChange f).obj U)) AddCommGrpCat.{u + 1})]
  [∀ U : S.Etale, HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback U.hom f))]
  [HasExt.{e} (AbelianSheaf.{u, u + 1}
    (pullback (Spec.algebraMap R (GeometricEtaleColimit R Ω) ≫ j) f))]
  [QuasiCompact f] [QuasiSeparated f]
  [HasColimitsOfShape (GeometricEtaleNeighborhood R Ω) AddCommGrpCat.{e}]
  (F : AbelianSheaf.{u, u + 1} X) (q : ℕ)

local instance chartPointedConnected : IsConnected (GeometricEtaleNeighborhood R Ω) :=
  IsFiltered.isConnected (GeometricEtaleNeighborhood R Ω)

local instance chartPointedRawStageExt (U : GeometricEtaleNeighborhood R Ω) :
    HasExt.{e} (AbelianSheaf.{u, u + 1}
      (pullback (Spec.algebraMap R U.algebra ≫ j) f)) :=
  inferInstanceAs (HasExt.{e} (AbelianSheaf.{u, u + 1}
    (pullback ((Scheme.EtalePointOpen.postcompose j).obj (etaleObject R Ω U)).hom f)))

local instance chartPointedDiagramStageExt (U : GeometricEtaleNeighborhood R Ω) :
    HasExt.{e} (AbelianSheaf.{u, u + 1} ((chartCoefficientDiagram R Ω j f).obj U).unop) :=
  inferInstanceAs (HasExt.{e} (AbelianSheaf.{u, u + 1}
    (pullback (Spec.algebraMap R U.algebra ≫ j) f)))

local instance chartPointedLimitExt :
    HasExt.{e} (AbelianSheaf.{u, u + 1} (chartCoefficientLimitCocone R Ω j f).pt.unop) :=
  inferInstanceAs (HasExt.{e} (AbelianSheaf.{u, u + 1}
    (pullback (Spec.algebraMap R (GeometricEtaleColimit R Ω) ≫ j) f)))


/-- The chart germ formula expressed in the native full pointed-limit cone. -/
theorem chartStrictLocalCohomologyAddEquiv_chartPointedGerm
    (U : GeometricEtaleNeighborhood R Ω)
    (x : Sheaf.H.{e} ((inverseImage (pullback.snd
      ((Scheme.EtalePointOpen.postcompose j).obj (etaleObject R Ω U)).hom f)).obj F) q) :
    chartStrictLocalCohomologyAddEquiv R Ω j η hη f F q
      (fibreProductCohomologyGerm f
        ((Scheme.EtalePointOpen.postcompose j).obj (etaleObject R Ω U)) F q η
        (chartStagePoint R Ω j η hη U) x) =
      pointedCohomologyLeg R Ω j η hη f F q
        ((chartToPointElements R Ω j η hη).obj (op U)) x := by
  have h := (chartStrictLocalComparisonUliftIso_leg R Ω j η hη f F q U).trans
    (congrArg (fun t => AddCommGrpCat.uliftFunctor.{u + 1, e}.map t)
      (pointedCohomologyLeg_chart R Ω j η hη f F q U).symm)
  exact pointedUliftComparison_apply
    (chartStrictLocalComparisonUliftIso R Ω j η hη f F q)
    ((chartOriginalStalkCocone R Ω j η hη f F q).ι.app U)
    (pointedCohomologyLeg R Ω j η hη f F q
      ((chartToPointElements R Ω j η hη).obj (op U))) h x
    (fibreProductCohomologyGerm f
      ((Scheme.EtalePointOpen.postcompose j).obj (etaleObject R Ω U)) F q η
      (chartStagePoint R Ω j η hη U) x)
    (chartOriginalStalkCocone_apply R Ω j η hη f F q U x)

/-- The chart comparison is an equality of the original additive maps. -/
theorem chartStrictLocalCohomologyAddEquiv_chartPointedHom
    (U : GeometricEtaleNeighborhood R Ω) :
    (chartStrictLocalCohomologyAddEquiv R Ω j η hη f F q).toAddMonoidHom.comp
      (fibreProductCohomologyGerm f
        ((Scheme.EtalePointOpen.postcompose j).obj (etaleObject R Ω U)) F q η
        (chartStagePoint R Ω j η hη U)) =
      (pointedCohomologyLeg R Ω j η hη f F q
        ((chartToPointElements R Ω j η hη).obj (op U))).hom := by
  ext x
  exact chartStrictLocalCohomologyAddEquiv_chartPointedGerm R Ω j η hη f F q U x

omit [Mono j]
  [HasExt.{e} (AbelianSheaf.{u, u + 1}
    (pullback (Spec.algebraMap R (GeometricEtaleColimit R Ω) ≫ j) f))]
  [QuasiCompact f] [QuasiSeparated f]
  [HasColimitsOfShape (GeometricEtaleNeighborhood R Ω) AddCommGrpCat.{e}] in
/-- The original germ square for a complete pointed refinement map. -/
theorem chartPointedGermRestriction_hom (U : GeometricEtaleNeighborhood R Ω)
    (d : (pointSmallEtale η).fiber.Elements)
    (a : (chartToPointElements R Ω j η hη).obj (op U) ⟶ d) :
    (fibreProductCohomologyGerm f
      ((Scheme.EtalePointOpen.postcompose j).obj (etaleObject R Ω U)) F q η
      (chartStagePoint R Ω j η hη U)).comp
        (fibreProductCohomologyRestriction f a.hom F q) =
      fibreProductCohomologyGerm f d.obj F q η d.val := by
  ext x
  exact fibreProductCohomologyGerm_restriction f F q η a.hom
    (chartStagePoint R Ω j η hη U) d.val a.map_val x

omit [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [∀ U : S.Etale, HasExt.{s} (Sheaf ((Scheme.smallEtaleTopology X).over
    ((siteBaseChange f).obj U)) AddCommGrpCat.{u + 1})]
  [QuasiCompact f] [QuasiSeparated f]
  [HasColimitsOfShape (GeometricEtaleNeighborhood R Ω) AddCommGrpCat.{e}] in
/-- Original additive-map compatibility at arbitrary native pointed objects. -/
theorem pointedCohomologyLeg_restriction_hom
    {d d' : (pointSmallEtale η).fiber.Elements} (a : d ⟶ d') :
    (pointedCohomologyLeg R Ω j η hη f F q d).hom.comp
      (fibreProductCohomologyRestriction f a.hom F q) =
      (pointedCohomologyLeg R Ω j η hη f F q d').hom :=
  congrArg (fun t => t.hom)
    (pointedCohomologyLeg_restriction R Ω j η hη f F q (d := d) (d' := d') a)

/-- The original comparison on a neighborhood with an actual chart refinement. -/
theorem chartStrictLocalCohomologyAddEquiv_pointedGerm_of_refinement
    (U : GeometricEtaleNeighborhood R Ω)
    (d : (pointSmallEtale η).fiber.Elements)
    (a : (chartToPointElements R Ω j η hη).obj (op U) ⟶ d)
    (x : Sheaf.H.{e} ((inverseImage (pullback.snd d.obj.hom f)).obj F) q) :
    chartStrictLocalCohomologyAddEquiv R Ω j η hη f F q
      (fibreProductCohomologyGerm f d.obj F q η d.val x) =
      pointedCohomologyLeg R Ω j η hη f F q d x := by
  have hr := pointedCohomologyLeg_restriction_hom R Ω j η hη f F q
    (d := (chartToPointElements R Ω j η hη).obj (op U)) (d' := d) a
  have h := pointedComparison_hom_square
    (fibreProductCohomologyRestriction f a.hom F q)
    (fibreProductCohomologyGerm f d.obj F q η d.val)
    (fibreProductCohomologyGerm f
      ((Scheme.EtalePointOpen.postcompose j).obj (etaleObject R Ω U)) F q η
      (chartStagePoint R Ω j η hη U))
    (pointedCohomologyLeg R Ω j η hη f F q d).hom
    (pointedCohomologyLeg R Ω j η hη f F q
      ((chartToPointElements R Ω j η hη).obj (op U))).hom
    (chartStrictLocalCohomologyAddEquiv R Ω j η hη f F q).toAddMonoidHom
    (chartPointedGermRestriction_hom R Ω j η hη f F q U d a) hr
    (chartStrictLocalCohomologyAddEquiv_chartPointedHom R Ω j η hη f F q U)
  exact DFunLike.congr_fun h x

/-- The canonical comparison preserves the map from every original pointed neighborhood. -/
theorem chartStrictLocalCohomologyAddEquiv_pointedGerm
    (d : (pointSmallEtale η).fiber.Elements)
    (x : Sheaf.H.{e} ((inverseImage (pullback.snd d.obj.hom f)).obj F) q) :
    chartStrictLocalCohomologyAddEquiv R Ω j η hη f F q
      (fibreProductCohomologyGerm f d.obj F q η d.val x) =
      pointedCohomologyLeg R Ω j η hη f F q d x := by
  let a : CostructuredArrow (chartToPointElements R Ω j η hη) d :=
    Classical.choice inferInstance
  exact chartStrictLocalCohomologyAddEquiv_pointedGerm_of_refinement R Ω j η hη f F q
    a.left.unop d a.hom x

end AlgebraicGeometry.Scheme.EtaleCohomology.Stalk
