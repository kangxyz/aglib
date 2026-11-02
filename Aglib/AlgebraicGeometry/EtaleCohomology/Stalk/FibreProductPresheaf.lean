/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.FibreProductOriginalDiagram

/-! # The actual fibre-product scheme cohomology presheaf -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

universe u w s t

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

variable {X S : Scheme.{u}} (f : X ⟶ S)
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [∀ U : S.Etale, HasExt.{s} (Sheaf ((Scheme.smallEtaleTopology X).over
    ((siteBaseChange f).obj U)) AddCommGrpCat.{u + 1})]
  [∀ U : S.Etale, HasExt.{t} (AbelianSheaf.{u, u + 1} (pullback U.hom f))]
  (F : AbelianSheaf.{u, u + 1} X) (q : ℕ)

/-- The original scheme cohomology groups are small in the coefficient universe.
Only these groups will be resized; the coefficient sheaf is unchanged. -/
instance fibreProductCohomology_small (U : S.Etale) :
    Small.{u + 1} (Sheaf.H.{t} ((inverseImage (pullback.snd U.hom f)).obj F) q) := by
  let : Small.{u + 1} (Sheaf.LargeCohomology.H.{w, u + 1, u, u + 1}
      (Scheme.smallEtaleTopology X) F q ((siteBaseChange f).obj U)) :=
    originalCohomologyPresheaf_small f F q (op U)
  exact small_of_injective (fibreProductCohomologyEquiv f U F q).symm.injective

/-- The original unresized diagram has the same proved group smallness. -/
instance Stalk.originalFibreProductCohomologyPresheaf_small (U : S.Etaleᵒᵖ) :
    Small.{u + 1} ((Stalk.originalFibreProductCohomologyPresheaf f F q).obj U) :=
  inferInstanceAs (Small.{u + 1}
    (Sheaf.H.{t} ((inverseImage (pullback.snd U.unop.hom f)).obj F) q))

/-- Original cohomology on the actual fibre products, with original scheme pullbacks. -/
def smallFibreProductCohomologyPresheaf : S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  CategoryTheory.resizeAdditiveDiagram.{u + 1}
    (Stalk.originalFibreProductCohomologyPresheaf f F q)

/-- The actual scheme-cohomology diagram is naturally the original represented diagram. -/
def smallFibreProductOriginalIso :
    smallFibreProductCohomologyPresheaf f F q ≅ smallOriginalCohomologyPresheaf f F q :=
  CategoryTheory.resizeAdditiveDiagramIsoOfAddEquiv
    (F := Stalk.originalFibreProductCohomologyPresheaf f F q)
    (G := originalCohomologyPresheaf f F q)
    (fun U => (fibreProductCohomologyEquiv f U.unop F q).symm)
    (fun {U V} (g : U ⟶ V) x =>
      fibreProductCohomologyRestriction_original f F q g.unop x)

end AlgebraicGeometry.Scheme.EtaleCohomology
