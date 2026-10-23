/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.ChartPointedComparison
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.FibreProductGermZero
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.PullbackLimitLegZero

/-! # Original degree-zero normalization of strict-local stalk comparison -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Stalk
universe u w s e
attribute [local instance] hasSheafifyLarge
open Continuity Finite.GeometricNeighborhood

/-- Degree-zero relative transfer is the original relative section map. -/
theorem relativeCohomologyTransfer_equiv₀ {X : Scheme.{u}}
    (F : AbelianSheaf.{u, u + 1} X) {A B : Over X}
    [HasExt.{e} (AbelianSheaf.{u, u + 1} A.left)]
    [HasExt.{e} (AbelianSheaf.{u, u + 1} B.left)]
    (a : A ⟶ B) (x : Sheaf.H.{e} ((inverseImage B.hom).obj F) 0) :
    Sheaf.H.equiv₀ ((inverseImage A.hom).obj F) (etaleTerminalIsTerminal A.left)
        (relativeCohomologyTransfer F 0 a x) =
      pullbackSectionsMap F a
        (Sheaf.H.equiv₀ ((inverseImage B.hom).obj F) (etaleTerminalIsTerminal B.left) x) :=
  cohomologyTransfer_equiv₀ a.left
    ((pullbackTriangleIso A.hom B.hom a.left (Over.w a)).inv.app F) x

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
  (F : AbelianSheaf.{u, u + 1} X)

local instance chartZeroConnected : IsConnected (GeometricEtaleNeighborhood R Ω) :=
  IsFiltered.isConnected (GeometricEtaleNeighborhood R Ω)

local instance chartZeroRawStageExt (U : GeometricEtaleNeighborhood R Ω) :
    HasExt.{e} (AbelianSheaf.{u, u + 1}
      (pullback (Spec.algebraMap R U.algebra ≫ j) f)) :=
  inferInstanceAs (HasExt.{e} (AbelianSheaf.{u, u + 1}
    (pullback ((Scheme.EtalePointOpen.postcompose j).obj (etaleObject R Ω U)).hom f)))

local instance chartZeroDiagramStageExt (U : GeometricEtaleNeighborhood R Ω) :
    HasExt.{e} (AbelianSheaf.{u, u + 1} ((chartCoefficientDiagram R Ω j f).obj U).unop) :=
  inferInstanceAs (HasExt.{e} (AbelianSheaf.{u, u + 1}
    (pullback (Spec.algebraMap R U.algebra ≫ j) f)))

local instance chartZeroLimitExt :
    HasExt.{e} (AbelianSheaf.{u, u + 1} (chartCoefficientLimitCocone R Ω j f).pt.unop) :=
  inferInstanceAs (HasExt.{e} (AbelianSheaf.{u, u + 1}
    (pullback (Spec.algebraMap R (GeometricEtaleColimit R Ω) ≫ j) f)))


local instance chartZeroPointedStageExt (d : (pointSmallEtale η).fiber.Elements) :
    HasExt.{e} (AbelianSheaf.{u, u + 1}
      ((pointedNeighborhoodBaseChangedDiagram Ω η f).obj d).left) :=
  inferInstanceAs (HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback d.obj.hom f)))

local instance chartZeroPointedApexExt : HasExt.{e} (AbelianSheaf.{u, u + 1}
    (pointedNeighborhoodBaseChangedCone R Ω j η hη f).pt.left) :=
  inferInstanceAs (HasExt.{e} (AbelianSheaf.{u, u + 1}
    (pullback (Spec.algebraMap R (GeometricEtaleColimit R Ω) ≫ j) f)))

/-- On every original section germ, q=0 is actual pullback to the pointed limit. -/
theorem chartStrictLocalCohomologyAddEquiv_zero
    (d : (pointSmallEtale η).fiber.Elements)
    (z : (globalSections (pullback d.obj.hom f)).obj
      ((inverseImage (pullback.snd d.obj.hom f)).obj F)) :
    Sheaf.H.equiv₀ ((inverseImage
        (pullback.snd (Spec.algebraMap R (GeometricEtaleColimit R Ω) ≫ j) f)).obj F)
      (etaleTerminalIsTerminal
        (pullback (Spec.algebraMap R (GeometricEtaleColimit R Ω) ≫ j) f))
      (chartStrictLocalCohomologyAddEquiv R Ω j η hη f F 0
        (((pointSmallEtale η).sheafFiber (A := AddCommGrpCat.{u + 1})).map
          ((directImage f).toRightDerivedZero.app F)
          ((pointSmallEtale η).toPresheafFiber d.obj d.val ((directImage f).obj F).obj
            ((pullbackSectionsEtaleEvaluationIso F ((siteBaseChange f).obj d.obj)).hom z)))) =
      pullbackSectionsMap F ((pointedNeighborhoodBaseChangedCone R Ω j η hη f).π.app d) z := by
  let x := (Sheaf.H.equiv₀ ((inverseImage (pullback.snd d.obj.hom f)).obj F)
    (etaleTerminalIsTerminal (pullback d.obj.hom f))).symm z
  have hzero := fibreProductCohomologyGerm_equiv₀_symm f d.obj F η d.val z
  have hcomparison := chartStrictLocalCohomologyAddEquiv_pointedGerm
    R Ω j η hη f F 0 d x
  have h := (congrArg (chartStrictLocalCohomologyAddEquiv R Ω j η hη f F 0)
    hzero.symm).trans hcomparison
  have hleg := relativeCohomologyTransfer_equiv₀ F
    (A := (pointedNeighborhoodBaseChangedCone R Ω j η hη f).pt)
    (B := (pointedNeighborhoodBaseChangedDiagram Ω η f).obj d)
    ((pointedNeighborhoodBaseChangedCone R Ω j η hη f).π.app d) x
  exact (congrArg (Sheaf.H.equiv₀ ((inverseImage
      (pullback.snd (Spec.algebraMap R (GeometricEtaleColimit R Ω) ≫ j) f)).obj F)
    (etaleTerminalIsTerminal
      (pullback (Spec.algebraMap R (GeometricEtaleColimit R Ω) ≫ j) f))) h).trans
    (hleg.trans (congrArg
      (pullbackSectionsMap F ((pointedNeighborhoodBaseChangedCone R Ω j η hη f).π.app d))
      ((Sheaf.H.equiv₀ ((inverseImage (pullback.snd d.obj.hom f)).obj F)
        (etaleTerminalIsTerminal (pullback d.obj.hom f))).apply_symm_apply z)))
end AlgebraicGeometry.Scheme.EtaleCohomology.Stalk
