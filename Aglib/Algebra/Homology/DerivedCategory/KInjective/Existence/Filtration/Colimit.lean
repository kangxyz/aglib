/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.KInjective.Existence.Filtration.Continuity

/-!
# The original acyclic complex is the actual filtration colimit

The canonical cocone consists of the original stage inclusions. Its colimit
comparison is monic by the native filtered-subobject theorem and epic because
the proved exhaustive endpoint is already the top subobject.
-/

@[expose] public noncomputable section

universe w v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.IsGrothendieckAbelian
  HomologicalComplex

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  {G : C} (hG : IsSeparator G) (M : CochainComplex C ℤ) (hM : M.Acyclic)

/-- The actual small well-ordered exhaustive diagram of native complexes. -/
abbrev acyclicFiltration : acyclicFiltrationIndex hG M hM ⥤ CochainComplex C ℤ :=
  acyclicComplexStages hG M hM

/-- The original ambient inclusions form the canonical filtration cocone. -/
def acyclicFiltrationCocone : Cocone (acyclicFiltration hG M hM) where
  pt := M
  ι :=
    { app j := (acyclicStages hG M hM j).arrow
      naturality i j f := by
        change ((acyclicStagesFunctor hG M hM).map f).hom.left ≫
            (acyclicStages hG M hM j).arrow = (acyclicStages hG M hM i).arrow ≫ 𝟙 M
        rw [Category.comp_id]
        exact MonoOver.w ((acyclicStagesFunctor hG M hM).map f) }

/-- The actual exhaustive cocone is a colimit. -/
def acyclicFiltrationCoconeIsColimit : IsColimit (acyclicFiltrationCocone hG M hM) := by
  let F := acyclicFiltration hG M hM
  let c := acyclicFiltrationCocone hG M hM
  let p : colimit F ⟶ M := colimit.desc F c
  have : Mono p := mono_of_isColimit_monoOver (acyclicStagesFunctor hG M hM)
    (colimit.isColimit F) p (fun j ↦ colimit.ι_desc c j)
  have he : IsIso (acyclicStages hG M hM (acyclicFiltrationEndpoint hG M hM)).arrow :=
    (Subobject.isIso_arrow_iff_eq_top _).2 (acyclicFiltrationEndpoint_eq_top hG M hM)
  have hcomp : Epi (colimit.ι F (acyclicFiltrationEndpoint hG M hM) ≫ p) := by
    change Epi (colimit.ι F (acyclicFiltrationEndpoint hG M hM) ≫ colimit.desc F c)
    rw [colimit.ι_desc]
    exact inferInstanceAs
      (Epi (acyclicStages hG M hM (acyclicFiltrationEndpoint hG M hM)).arrow)
  have : Epi p := epi_of_epi (colimit.ι F (acyclicFiltrationEndpoint hG M hM)) p
  have : IsIso p := isIso_of_mono_of_epi p
  have : IsIso ((colimit.isColimit F).desc c) := inferInstanceAs (IsIso p)
  change IsColimit c
  exact (colimit.isColimit F).ofPointIso

/-- The specified native colimit comparison identifies the filtration with M. -/
def acyclicFiltrationColimitIso : colimit (acyclicFiltration hG M hM) ≅ M :=
  (colimit.isColimit _).coconePointUniqueUpToIso (acyclicFiltrationCoconeIsColimit hG M hM)

end CochainComplex
