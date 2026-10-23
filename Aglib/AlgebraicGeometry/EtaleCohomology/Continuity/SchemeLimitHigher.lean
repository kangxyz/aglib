/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramDimensionShift

/-! # Higher scheme-limit continuity reduced to original degree-zero cocones

The result concerns the literal `schemeLimitCohomologyComparison`, whose
components are the original pullback followed by coefficient-colimit maps.
Induction uses the actual compatible injective replacement and its pointwise
cokernel, not an auxiliary abelian category of coefficient systems.

Two genuine degree-zero inputs remain explicit: the original global H-zero
cocones for all systems, and the original qcqs evaluated right-tail cocones
for objectwise-injective systems. Consequently this is a higher-continuity
reduction, not an unconditional geometric degree-zero producer.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity

universe u e

attribute [local instance] hasSheafifyLarge

variable {I : Type u} [Category.{u} I] [IsFiltered I]
  (X : I ⥤ Scheme.{u}ᵒᵖ) (c : Cocone X) (hc : IsColimit c)
  [∀ i, CompactSpace (X.obj i).unop] [∀ i, QuasiSeparatedSpace (X.obj i).unop]
  [∀ {i j} (a : i ⟶ j), IsAffineHom (X.map a).unop]
  [∀ i, HasExt.{e} (AbelianSheaf.{u, u + 1} (X.obj i).unop)]
  [HasExt.{e} (AbelianSheaf.{u, u + 1} c.pt.unop)]
  [HasColimitsOfShape I AddCommGrpCat.{e}]

include hc in
/-- Original degree-zero cocone certificates imply invertibility of the
original comparison in all degrees. The two outstanding degree-zero inputs
are explicit; no higher comparison or higher vanishing is a hypothesis. -/
theorem isIso_schemeLimitCohomologyComparison_of_sectionCocones
    (hzero : ∀ F : DiagramCoefficientSystem X,
      IsColimit (diagramCohomologyCocone X c F 0))
    (hqcqsSectionCocones : ∀ (Q : DiagramCoefficientSystem X),
      (∀ i, Injective (Q.obj i)) → ∀ (i : I) (T : (X.obj i).unop.Etale),
        (CompactSpace T.left ∧ QuasiSeparatedSpace T.left) → IsColimit
          (((sheafSections (X.obj i).unop.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
            (op T)).mapCocone (diagramRightTailCocone X Q c i)))
    (n : ℕ) (F : DiagramCoefficientSystem X) :
    IsIso (schemeLimitCohomologyComparison X c F n) := by
  induction n generalizing F with
  | zero =>
      exact (IsColimit.nonempty_isColimit_iff_isIso_desc
        (colimit.isColimit (diagramCohomologyFunctor X F 0))).mp ⟨hzero F⟩
  | succ n ih =>
      let Q : DiagramCoefficientSystem X := diagramInjectiveReplacement X F
      let η : InjectiveSystem.System.Hom (diagramAdjunctionData X) F Q :=
        diagramInjectiveEmbedding X F
      have hη : ∀ i, Mono (η.app i) := fun i => diagramInjectiveEmbedding_mono X F i
      have (i : I) : Injective (Q.obj i) := diagramInjectiveReplacement_injective X F i
      have : IsIso (schemeLimitCohomologyComparison X c Q n) := ih Q
      have : IsIso (schemeLimitCohomologyComparison X c (diagramCokernelSystem X η) n) :=
        ih (diagramCokernelSystem X η)
      exact isIso_schemeLimitCohomologyComparison_succ_of_sectionCocones X c hc η hη n
        (hqcqsSectionCocones Q (fun _ => inferInstance))

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
