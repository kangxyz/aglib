/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramTestRightTailCocone
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramTestTailSections
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.QcqsLimitSections

/-! # Original evaluated right-tail colimits on qcqs étale test objects

Every fixed-source column is the original fixed-coefficient section cocone on
an actual inverse scheme limit. Geometric degree-zero continuity gives those
columns. Fixed-site qcqs evaluation gives the outer colimit. The original
diagonal theorem and exact chart/adjoint leg comparison then give the literal
evaluated right-tail cocone. No continuity certificate is a hypothesis.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
universe u
attribute [local instance] hasSheafifyLarge

variable {I : Type u} [Category.{u} I] [IsFiltered I]
  (X : I ⥤ Scheme.{u}ᵒᵖ) (c : Cocone X) (hc : IsColimit c)
  [hAffine : ∀ {j k} (m : j ⟶ k), IsAffineHom (X.map m).unop]
  (i : I) (T : (X.obj i).unop.Etale)

include hc hAffine

/-- The native limit test chart is qc whenever the original stage test is qc. -/
theorem diagramEtaleTestLimitChart_compactSpace [CompactSpace T.left] :
    CompactSpace (diagramEtaleTestLimitChart X i T c).left := by
  have {j k : Iᵒᵖ} (m : j ⟶ k) : IsAffineHom (X.leftOp.map m) :=
    inferInstanceAs (IsAffineHom (X.map m.unop).unop)
  have : IsAffineHom (c.ι.app i).unop :=
    isAffineHom_π_app X.leftOp (coneLeftOpOfCocone c)
      (isLimitConeLeftOpOfCocone X hc) (op i)
  have hπ : IsAffineHom (pullback.snd (c.ι.app i).unop T.hom) :=
    @MorphismProperty.IsStableUnderBaseChange.of_isPullback
      Scheme.{u} _ (@IsAffineHom) isAffineHom_isStableUnderBaseChange
      T.left c.pt.unop (pullback (c.ι.app i).unop T.hom) (X.obj i).unop
      T.hom (c.ι.app i).unop
      (pullback.fst (c.ι.app i).unop T.hom) (pullback.snd (c.ι.app i).unop T.hom)
      (IsPullback.of_hasPullback (c.ι.app i).unop T.hom)
      (inferInstanceAs (IsAffineHom (c.ι.app i).unop))
  have hqc : QuasiCompact (pullback.snd (c.ι.app i).unop T.hom) :=
    quasiCompact_iff_forall_isAffineOpen.mpr fun U hU => (hπ.isAffine_preimage U hU).isCompact
  exact @QuasiCompact.compactSpace_of_compactSpace
    (pullback (c.ι.app i).unop T.hom) T.left (pullback.snd (c.ι.app i).unop T.hom)
    hqc inferInstance

/-- The native limit test chart is quasi-separated whenever the stage test is. -/
theorem diagramEtaleTestLimitChart_quasiSeparatedSpace [QuasiSeparatedSpace T.left] :
    QuasiSeparatedSpace (diagramEtaleTestLimitChart X i T c).left := by
  have {j k : Iᵒᵖ} (m : j ⟶ k) : IsAffineHom (X.leftOp.map m) :=
    inferInstanceAs (IsAffineHom (X.map m.unop).unop)
  have : IsAffineHom (c.ι.app i).unop :=
    isAffineHom_π_app X.leftOp (coneLeftOpOfCocone c)
      (isLimitConeLeftOpOfCocone X hc) (op i)
  have : QuasiSeparated (pullback.snd (c.ι.app i).unop T.hom) := inferInstance
  exact @quasiSeparatedSpace_of_quasiSeparated
    (pullback (c.ι.app i).unop T.hom) T.left
    (pullback.snd (c.ι.app i).unop T.hom) inferInstance inferInstance

variable (F : DiagramCoefficientSystem X)
  [CompactSpace T.left] [QuasiSeparatedSpace T.left]

/-- Genuine fixed-coefficient qcqs continuity supplies each actual source-fixed test row. -/
def isColimitDiagramTestTailOfQcqs (a : Under i) :
    IsColimit (diagramTestTailSectionsCocone X F c i T a) := by
  let D := (diagramTestRelativeTail X i T a).leftOp
  have (b : (Under a)ᵒᵖ) : CompactSpace (D.obj b).left :=
    inferInstanceAs (CompactSpace ((diagramEtaleTest X i T).obj b.unop.right).unop)
  have (b : (Under a)ᵒᵖ) : QuasiSeparatedSpace (D.obj b).left :=
    inferInstanceAs (QuasiSeparatedSpace ((diagramEtaleTest X i T).obj b.unop.right).unop)
  have {b d : (Under a)ᵒᵖ} (m : b ⟶ d) : IsAffineHom (D.map m).left :=
    inferInstanceAs (IsAffineHom ((diagramEtaleTest X i T).map m.unop.right).unop)
  exact isColimitDiagramTestTailOfNative X F c i T a
    (qcqsPullbackSectionsCoconeIsColimit D (diagramTestRelativeTailCone X c i T a)
      (F.obj a.right) (isLimitDiagramTestRelativeTail X c i T a
        (diagramEtaleTestCoconeIsColimit X i T c hc)))

variable [HasColimit (coneCoefficientFunctor X c F)]

/-- The literal right-tail cocone is colimiting after evaluation on an original qcqs stage test. -/
def isColimitDiagramRightTailEvaluation :
    IsColimit (((sheafSections (X.obj i).unop.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (op T)).mapCocone (diagramRightTailCocone X F c i)) := by
  have : CompactSpace (diagramEtaleTestLimitChart X i T c).left :=
    diagramEtaleTestLimitChart_compactSpace X c hc i T
  have : QuasiSeparatedSpace (diagramEtaleTestLimitChart X i T c).left :=
    diagramEtaleTestLimitChart_quasiSeparatedSpace X c hc i T
  have hD : IsColimit (diagramTestDiagonalCocone X F c i T) :=
    SchemeSystemColimits.isColimitDiagonal (diagramTestArrowSectionsFunctor X F i T)
      (diagramTestConeSectionsFunctor X F c i T) (diagramTestConeSectionsNatTrans X F c i T)
      (fun a => isColimitDiagramTestTailOfQcqs X c hc i T F a)
      (diagramTestConeSectionsCocone X F c i T)
      (isColimitDiagramTestConeSections X F c i T)
  exact IsColimit.precomposeHomEquiv (diagramTestDiagonalRightTailIso X F i T) _
    (IsColimit.ofIsoColimit hD (diagramTestDiagonalRightTailCoconeIso X F c i T))

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
