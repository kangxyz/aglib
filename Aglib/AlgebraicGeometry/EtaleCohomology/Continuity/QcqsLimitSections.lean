/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.AffineLimitSections
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.PullbackSectionsBase
public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.RelativeChartTailCone
public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.QcqsHypercover
public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.FiniteMatchingCocone
public import Aglib.CategoryTheory.Limits.ConeTriangle
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Filtered.Final

/-! # Original sections on qcqs inverse scheme limits

A finite affine one-hypercover at one stage reduces the original section
cocone to actual affine chart tails. No section-continuity or target-colimit
certificate is an input.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity

universe u

open EtaleAffineBasis
attribute [local instance] hasSheafifyLarge

/-- Contravariant section cocones retain an actual cone triangle. -/
def presheafCoconeIsoOfConeTriangle
    {J K C A : Type*} [Category J] [Category K] [Category C] [Category A]
    (D : J ⥤ C) (c : Cone D) (R : K ⥤ J) (T : K ⥤ C) (t : Cone T)
    (d : T ≅ R ⋙ D) (e : t.pt ≅ c.pt)
    (hw : ∀ k, t.π.app k ≫ d.hom.app k = e.hom ≫ c.π.app (R.obj k))
    (P : Cᵒᵖ ⥤ A) :
    (Cocone.precompose (Functor.isoWhiskerRight (NatIso.op d) P).hom).obj
      (P.mapCocone t.op) ≅ (P.mapCocone c.op).whisker R.op :=
  ConeTriangle.presheafCoconeIsoOfConeTriangle D c R T t d e hw P

/-- Evaluate a whole contravariant section cocone before specializing its coefficients. -/
def isColimitFunctorConeOpEvaluationEquiv
    {J C B A : Type*} [Category J] [Category C] [Category B] [Category A]
    (H : J ⥤ C ⥤ B) (c : Cone H) (P : Bᵒᵖ ⥤ A) (U : C) :
    IsColimit (((CategoryTheory.evaluation Cᵒᵖ A).obj (op U)).mapCocone
      ((Functor.opHom C B ⋙
        (Functor.whiskeringRight Cᵒᵖ Bᵒᵖ A).obj P).mapCocone c.op)) ≃
      IsColimit (P.mapCocone (((CategoryTheory.evaluation C B).obj U).mapCone c).op) :=
  ConeTriangle.isColimitFunctorConeOpEvaluationEquiv H c P U

/-- Apply the original relative section functor to a chart-variable relative scheme. -/
def relativeChartSectionsFunctor (S X : Scheme.{u})
    (F : AbelianSheaf.{u, u + 1} X) :
    (S.Etale ⥤ Over X)ᵒᵖ ⥤ S.Etaleᵒᵖ ⥤ Ab.{u + 1} :=
  Functor.opHom S.Etale (Over X) ⋙
    (Functor.whiskeringRight S.Etaleᵒᵖ (Over X)ᵒᵖ Ab.{u + 1}).obj
      (pullbackSectionsFunctor F)

section Relative

variable {I : Type u} [Category.{u} I] {X : Scheme.{u}}
  (D : I ⥤ Over X) (c : Cone D) (i : I) (F : AbelianSheaf.{u, u + 1} X)

/-- Actual relative chart tails, viewed as presheaves on the original stage site. -/
def nativeChartSectionsDiagram :
    (Over i)ᵒᵖ ⥤ (D.obj i).left.Etaleᵒᵖ ⥤ Ab.{u + 1} :=
  (relativeChartTails D i).flip.op ⋙ relativeChartSectionsFunctor (D.obj i).left X F

/-- The original chart-variable cone gives its actual relative-section cocone. -/
def nativeChartSectionsCocone : Cocone (nativeChartSectionsDiagram D i F) :=
  (relativeChartSectionsFunctor (D.obj i).left X F).mapCocone
    (nativeChartTailsCone D c i).op

/-- Every original stage member is an actual direct image of the native pullback sheaf. -/
def nativeChartSectionsStageIso (j : Over i) :
    (nativeChartSectionsDiagram D i F).obj (op j) ≅
      (siteBaseChange (D.map j.hom).left).op ⋙
        ((inverseImage (D.obj j.left).hom).obj F).obj :=
  Functor.isoWhiskerRight (NatIso.op (nativeStageChartsIso D i j)) (pullbackSectionsFunctor F) ≪≫
    Functor.associator (siteBaseChange (D.map j.hom).left).op
      (Etale.forget (D.obj j.left).left ⋙ Over.map (D.obj j.left).hom).op
      (pullbackSectionsFunctor F) ≪≫
    Functor.isoWhiskerLeft (siteBaseChange (D.map j.hom).left).op
      (pullbackSectionsBaseEtaleIso (D.obj j.left).hom F)

/-- The original limit point is an actual direct image of the native pullback sheaf. -/
def nativeChartSectionsPointIso :
    (nativeChartSectionsCocone D c i F).pt ≅
      (siteBaseChange (c.π.app i).left).op ⋙ ((inverseImage c.pt.hom).obj F).obj :=
  Functor.associator (siteBaseChange (c.π.app i).left).op
      (Etale.forget c.pt.left ⋙ Over.map c.pt.hom).op (pullbackSectionsFunctor F) ≪≫
    Functor.isoWhiskerLeft (siteBaseChange (c.π.app i).left).op
      (pullbackSectionsBaseEtaleIso c.pt.hom F)

/-- Sheaf matching at a tail stage is supplied by the original inverse image. -/
theorem nativeChartSectionsStage_isSheaf (j : Over i) :
    Presheaf.IsSheaf (D.obj i).left.smallEtaleTopology
      ((nativeChartSectionsDiagram D i F).obj (op j)) := by
  rw [Presheaf.isSheaf_of_iso_iff (nativeChartSectionsStageIso D i F j)]
  exact (siteBaseChange (D.map j.hom).left).op_comp_isSheaf
    (D.obj i).left.smallEtaleTopology (D.obj j.left).left.smallEtaleTopology
    ((inverseImage (D.obj j.left).hom).obj F)

/-- Sheaf matching at the limit point is supplied by the original inverse image. -/
theorem nativeChartSectionsPoint_isSheaf :
    Presheaf.IsSheaf (D.obj i).left.smallEtaleTopology
      (nativeChartSectionsCocone D c i F).pt := by
  rw [Presheaf.isSheaf_of_iso_iff (nativeChartSectionsPointIso D c i F)]
  let f : c.pt.left ⟶ (D.obj i).left := (c.π.app i).left
  have : (siteBaseChange f).IsContinuous (D.obj i).left.smallEtaleTopology
      c.pt.left.smallEtaleTopology := inferInstance
  exact (siteBaseChange f).op_comp_isSheaf
    (D.obj i).left.smallEtaleTopology c.pt.left.smallEtaleTopology
    ((inverseImage c.pt.hom).obj F)

/-- Terminal chart normalization retains every original relative cocone leg. -/
def terminalChartSectionsCoconeIso :
    (Cocone.precompose (Functor.isoWhiskerRight (NatIso.op (terminalChartTailIso D i))
      (pullbackSectionsFunctor F)).hom).obj
      (pullbackSectionsCocone (relativeChartTail D i (etaleTerminal (D.obj i).left))
        (nativeChartTailCone D c i (etaleTerminal (D.obj i).left)) F) ≅
      (pullbackSectionsCocone D c F).whisker (Over.forget i).op := by
  exact presheafCoconeIsoOfConeTriangle D c (Over.forget i)
    (relativeChartTail D i (etaleTerminal (D.obj i).left))
    (nativeChartTailCone D c i (etaleTerminal (D.obj i).left))
    (terminalChartTailIso D i) (terminalLimitChartIso D c i)
    (terminalChartTailCone_triangle D c i) (pullbackSectionsFunctor F)

variable [IsCofiltered I] (hc : IsLimit ((Over.forget X).mapCone c))
  [∀ {j k} (a : j ⟶ k), IsAffineHom (D.map a).left]

include hc

/-- Evaluation on an affine chart is the genuinely colimiting original affine tail. -/
def nativeChartSectionsAffineIsColimit (U : (D.obj i).left.Etale) [IsAffine U.left] :
    IsColimit (((CategoryTheory.evaluation (D.obj i).left.Etaleᵒᵖ Ab.{u + 1}).obj
      (op U)).mapCocone (nativeChartSectionsCocone D c i F)) := by
  exact (isColimitFunctorConeOpEvaluationEquiv (relativeChartTails D i).flip
    (nativeChartTailsCone D c i) (pullbackSectionsFunctor F) U).symm
      (affinePullbackSectionsCoconeIsColimit (relativeChartTail D i U)
        (nativeChartTailCone D c i U) (nativeChartTailConeIsLimit D c hc i U) F)

/-- A finite original affine one-hypercover makes the terminal chart cocone colimiting. -/
def nativeChartSectionsTerminalIsColimit
    [CompactSpace (D.obj i).left] [QuasiSeparatedSpace (D.obj i).left] :
    IsColimit (((CategoryTheory.evaluation (D.obj i).left.Etaleᵒᵖ Ab.{u + 1}).obj
      (op (etaleTerminal (D.obj i).left))).mapCocone (nativeChartSectionsCocone D c i F)) := by
  classical
  apply Classical.choice
  have : AB5OfSize.{u, u} Ab.{u + 1} :=
    AB5OfSize_of_univLE.{u, u, u + 1, u + 1} Ab.{u + 1}
  have : CompactSpace (etaleTerminal (D.obj i).left).left :=
    inferInstanceAs (CompactSpace (D.obj i).left)
  have : QuasiSeparatedSpace (etaleTerminal (D.obj i).left).left :=
    inferInstanceAs (QuasiSeparatedSpace (D.obj i).left)
  obtain ⟨E, h₀, h₁, hX, hY, _⟩ := exists_finite_affine_oneHypercover
    (etaleTerminal (D.obj i).left) ⊤
    ((D.obj i).left.smallEtaleTopology.top_mem _)
  have : Finite E.I₀ := h₀
  have (j k : E.I₀) : Finite (E.I₁ j k) := h₁ j k
  have (j : E.I₀) : IsAffine (E.X j).left := hX j
  have (j k : E.I₀) (a : E.I₁ j k) : IsAffine (E.Y a).left := hY j k a
  exact ⟨E.isColimitEvaluationOfFiniteMatching (nativeChartSectionsDiagram D i F)
    (nativeChartSectionsCocone D c i F)
    (fun j ↦ nativeChartSectionsStage_isSheaf D i F j.unop)
    (nativeChartSectionsPoint_isSheaf D c i F)
    (fun j ↦ nativeChartSectionsAffineIsColimit D c i F hc (E.X j))
    (fun j k a ↦ nativeChartSectionsAffineIsColimit D c i F hc (E.Y a))⟩

/-- Actual finite chart descent proves the original fixed-coefficient section cocone
colimiting for a qcqs inverse system with affine transitions. -/
def qcqsPullbackSectionsCoconeIsColimit
    [∀ j, CompactSpace (D.obj j).left] [∀ j, QuasiSeparatedSpace (D.obj j).left] :
    IsColimit (pullbackSectionsCocone D c F) := by
  classical
  have : Nonempty I := IsCofiltered.nonempty
  let i : I := Classical.arbitrary I
  have hT := isColimitFunctorConeOpEvaluationEquiv (relativeChartTails D i).flip
    (nativeChartTailsCone D c i) (pullbackSectionsFunctor F)
    (etaleTerminal (D.obj i).left)
    (nativeChartSectionsTerminalIsColimit D c i F hc)
  let e := Functor.isoWhiskerRight (NatIso.op (terminalChartTailIso D i))
    (pullbackSectionsFunctor F)
  have hT' := (IsColimit.precomposeHomEquiv e _).symm hT
  exact Functor.Final.isColimitWhiskerEquiv (Over.forget i).op
    (pullbackSectionsCocone D c F)
    (hT'.ofIsoColimit (terminalChartSectionsCoconeIso D c i F))

end Relative

section Compatible

variable {I : Type u} [Category.{u} I] [IsFiltered I]
  (X : I ⥤ Scheme.{u}ᵒᵖ) (c : Cocone X) (hc : IsColimit c)
  [∀ i, CompactSpace (X.obj i).unop] [∀ i, QuasiSeparatedSpace (X.obj i).unop]
  [∀ {i j} (a : i ⟶ j), IsAffineHom (X.map a).unop]
  (F : DiagramCoefficientSystem X)

/-- Finite affine chart descent proves the original section cocone for every
compatible coefficient system on a qcqs inverse scheme limit. -/
def isColimitCompatibleSectionsOfQcqsStages :
    IsColimit (compatibleSectionsCocone X F c) := by
  classical
  let D₀ := X.leftOp
  let c₀ := coneLeftOpOfCocone c
  let h₀ := isLimitConeLeftOpOfCocone X hc
  have (i : Iᵒᵖ) : CompactSpace (D₀.obj i) :=
    inferInstanceAs (CompactSpace (X.obj i.unop).unop)
  have (i : Iᵒᵖ) : QuasiSeparatedSpace (D₀.obj i) :=
    inferInstanceAs (QuasiSeparatedSpace (X.obj i.unop).unop)
  have {i j : Iᵒᵖ} (a : i ⟶ j) : IsAffineHom (D₀.map a) :=
    inferInstanceAs (IsAffineHom (X.map a.unop).unop)
  have : CompactSpace c.pt.unop := Scheme.compactSpace_of_isLimit D₀ c₀ h₀
  have : Nonempty I := IsFiltered.nonempty
  let i₀ : I := Classical.arbitrary I
  have : IsAffineHom (c₀.π.app (op i₀)) := isAffineHom_π_app D₀ c₀ h₀ (op i₀)
  have : QuasiSeparatedSpace c.pt.unop :=
    quasiSeparatedSpace_of_quasiSeparated (c₀.π.app (op i₀))
  apply isColimitCompatibleSectionsOfNativeTails X F c
  intro i
  let D := (relativeSchemeTail X i).leftOp
  have (j : (Under i)ᵒᵖ) : CompactSpace (D.obj j).left :=
    inferInstanceAs (CompactSpace (X.obj j.unop.right).unop)
  have (j : (Under i)ᵒᵖ) : QuasiSeparatedSpace (D.obj j).left :=
    inferInstanceAs (QuasiSeparatedSpace (X.obj j.unop.right).unop)
  have {j k : (Under i)ᵒᵖ} (a : j ⟶ k) : IsAffineHom (D.map a).left :=
    inferInstanceAs (IsAffineHom (X.map a.unop.right).unop)
  exact qcqsPullbackSectionsCoconeIsColimit D (relativeSchemeTailCone X c i) (F.obj i)
    (isLimitRelativeSchemeTailUnderlying X c hc i)

end Compatible

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
