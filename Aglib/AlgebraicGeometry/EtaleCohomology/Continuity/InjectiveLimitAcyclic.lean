/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.FamilyTailCochains
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.StageSupport.FiniteRefinements

/-! # Compatible injective limit acyclicity from original test-section cocones

The actual finite supported families descend to a common stage. Their qcqs
tuple models and the original fixed-stage cochain cocone give supported-family
acyclicity of the original limit coefficient. The native supported-family
dimension shift then annihilates positive original `Sheaf.H`.

The genuine degree-zero input is kept explicit: the original right-tail
coefficient cocone must be colimiting after evaluation at every qcqs stage
étale test object. This file does not prove that input and does not assert an
unconditional scheme-limit continuity theorem.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Sheaf.ModuleCoefficients

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity

universe u e

attribute [local instance] hasSheafifyLarge

variable {I : Type u} [Category.{u} I] [IsFiltered I]
  (X : I ⥤ Scheme.{u}ᵒᵖ) (c : Cocone X) (hc : IsColimit c)
  [∀ i, CompactSpace (X.obj i).unop] [∀ i, QuasiSeparatedSpace (X.obj i).unop]
  [∀ {i j} (a : i ⟶ j), IsAffineHom (X.map a).unop]
  (F : DiagramCoefficientSystem X) [∀ i, Injective (F.obj i)]
  [HasColimit (coneCoefficientFunctor X c F)]

include hc in
/-- Actual descended finite-family models reduce supported acyclicity of the
limit coefficient to the literal qcqs evaluated right-tail colimit certificates. -/
theorem injectiveLimit_supportedFamilyCechAcyclic
    (hqcqsSectionCocones : ∀ (i : I) (T : (X.obj i).unop.Etale),
      (CompactSpace T.left ∧ QuasiSeparatedSpace T.left) → IsColimit
        (((sheafSections (X.obj i).unop.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
          (op T)).mapCocone (diagramRightTailCocone X F c i))) :
    SupportedFamilyCechAcyclic (stageDescendedQcqsObjects X c)
      (colimit (coneCoefficientFunctor X c F)) := by
  intro W hW J _ U hU n
  obtain ⟨i, ⟨M⟩⟩ := StageSupport.exists_familyModel hc hW U hU
  exact M.limitCochains_exactAt F (fun m a => hqcqsSectionCocones i
    (∏ᶜ fun k => M.family (a k)).left
    ⟨(M.tupleModel a).compactSpace, (M.tupleModel a).quasiSeparatedSpace⟩) n

variable [HasExt.{e} (AbelianSheaf.{u, u + 1} c.pt.unop)]

include hc in
/-- Positive original cohomology of the actual compatible injective limit
vanishes once its original qcqs test-section cocones are known to be colimiting.
The Ext universe is independent of the scheme and coefficient universes. -/
theorem injectiveLimit_cohomology_eq_zero
    (hqcqsSectionCocones : ∀ (i : I) (T : (X.obj i).unop.Etale),
      (CompactSpace T.left ∧ QuasiSeparatedSpace T.left) → IsColimit
        (((sheafSections (X.obj i).unop.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
          (op T)).mapCocone (diagramRightTailCocone X F c i)))
    (n : ℕ) (x : Sheaf.H.{e} (colimit (coneCoefficientFunctor X c F)) (n + 1)) : x = 0 := by
  let : EnoughInjectives (AbelianSheaf.{u, u + 1} c.pt.unop) :=
    abelianSheaf_enoughInjectives c.pt.unop
  have hF := injectiveLimit_supportedFamilyCechAcyclic X c hc F hqcqsSectionCocones
  exact hF.cohomology_eq_zero
    (stageDescendedQcqsObjects X c)
    (stageDescendedQcqsObjects_finiteRefinements X c hc)
    (stageDescendedQcqsObjects_tupleProducts X c hc)
    (stageDescendedQcqsObjects_terminal X c) (etaleTerminalIsTerminal c.pt.unop) n x

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
