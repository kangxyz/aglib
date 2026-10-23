/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramCohomologyExact
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.InjectiveLimitAcyclic
public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.CoefficientDimensionShift

/-! # The original scheme-limit comparison's dimension-shift step

The source and target are the existing original connecting rows. Pointwise
injectivity gives the source boundary epimorphism. The target boundary is
epic by the proved injective-limit acyclicity reduction, whose genuine qcqs
evaluated-cocone input remains explicit. The original comparison morphism
and the native abelian diagram lemma then advance the induction by one degree.
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
  {F Q : DiagramCoefficientSystem X} [∀ i, Injective (Q.obj i)]
  (η : InjectiveSystem.System.Hom (diagramAdjunctionData X) F Q)
  (hη : ∀ i, Mono (η.app i)) (n : ℕ)

include hc hη in
/-- Lower-degree comparison maps and genuine test-section colimit certificates
advance the original comparison by one degree. Vanishing of the injective
limit is proved from those certificates, not assumed. -/
theorem isIso_schemeLimitCohomologyComparison_succ_of_sectionCocones
    (hqcqsSectionCocones : ∀ (i : I) (T : (X.obj i).unop.Etale),
      (CompactSpace T.left ∧ QuasiSeparatedSpace T.left) → IsColimit
        (((sheafSections (X.obj i).unop.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
          (op T)).mapCocone (diagramRightTailCocone X Q c i)))
    [Epi (schemeLimitCohomologyComparison X c Q n)]
    [IsIso (schemeLimitCohomologyComparison X c (diagramCokernelSystem X η) n)] :
    IsIso (schemeLimitCohomologyComparison X c F (n + 1)) := by
  have hvan (i : I) (x : Sheaf.H.{e} (Q.obj i) (n + 1)) : x = 0 :=
    Subsingleton.elim x 0
  have (i : I) : Epi ((diagramCohomologyConnectingComplex X η hη n).g.app i) :=
    Sheaf.H.connecting_epi n (diagramCokernelComplex_shortExact X η hη i) (hvan i)
  have : Epi (diagramCohomologyConnectingComplex X η hη n).g :=
    NatTrans.epi_of_epi_app _
  have hlim : ∀ x : Sheaf.H.{e} (colimit (coneCoefficientFunctor X c Q)) (n + 1),
      x = 0 := injectiveLimit_cohomology_eq_zero X c hc Q hqcqsSectionCocones n
  have : Epi (limitCohomologyConnectingComplex X η hη n c).g :=
    Sheaf.H.connecting_epi n (coneCoefficientColimitCokernelComplex_shortExact X c η hη) hlim
  let φ := diagramCohomologyConnectingComparison X η hη n c
  refine Abelian.isIso_of_epi_of_isIso (ShortComplex.mapToComposableArrows φ)
    (diagramCohomologyConnectingComplex_colimit_exact X η hη n).exact_toComposableArrows
    (limitCohomologyConnectingComplex_exact X η hη n c).exact_toComposableArrows
    ?_ ?_ ?_ ?_
  · change Epi (colim.map (diagramCohomologyConnectingComplex X η hη n).g)
    infer_instance
  · change Epi (limitCohomologyConnectingComplex X η hη n c).g
    infer_instance
  · change Epi (schemeLimitCohomologyComparison X c Q n)
    infer_instance
  · change IsIso (schemeLimitCohomologyComparison X c (diagramCokernelSystem X η) n)
    infer_instance

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
