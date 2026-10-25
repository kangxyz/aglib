/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.FibreProductOriginalDiagram
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.ChartCohomologyDiagram
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.ChartGeometricStalkIndex

/-! # Whole original cohomology diagrams on arbitrary-base chart neighborhoods -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Stalk
universe u w s e
attribute [local instance] hasSheafifyLarge
open Continuity Finite.GeometricNeighborhood

variable (R Ω : Type u) [CommRing R] [Field Ω] [Algebra R Ω] [IsSepClosed Ω]
  {X S : Scheme.{u}} (j : Spec (.of R) ⟶ S) [Etale j]
  (η : Spec (.of Ω) ⟶ S) (hη : Spec.algebraMap R Ω ≫ j = η) (f : X ⟶ S)
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [∀ U : S.Etale, HasExt.{s} (Sheaf ((Scheme.smallEtaleTopology X).over
    ((siteBaseChange f).obj U)) AddCommGrpCat.{u + 1})]
  [∀ U : S.Etale,
    HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback U.hom f))]
  (F : AbelianSheaf.{u, u + 1} X) (q : ℕ)

local instance (U : GeometricEtaleNeighborhood R Ω) :
    HasExt.{e} (AbelianSheaf.{u, u + 1} ((chartCoefficientDiagram R Ω j f).obj U).unop) :=
  inferInstanceAs (HasExt.{e} (AbelianSheaf.{u, u + 1}
    (pullback ((Scheme.EtalePointOpen.postcompose j).obj (etaleObject R Ω U)).hom f)))

/-- Restrict the original unresized fibre-product diagram to the actual geometric index. -/
def chartOriginalCohomologyDiagram :
    GeometricEtaleNeighborhood R Ω ⥤ AddCommGrpCat.{e} :=
  chartToStalkIndex R Ω j η hη ⋙
    (Functor.Elements.π (pointSmallEtale η).fiber).op ⋙
      originalFibreProductCohomologyPresheaf f F q

/-- The actual system and original scheme-H diagrams agree before any resizing. -/
def chartOriginalCohomologyIso :
    diagramCohomologyFunctor (chartCoefficientDiagram R Ω j f)
        (chartPullbackCoefficientSystem R Ω j f F) q ≅
      chartOriginalCohomologyDiagram R Ω j η hη f F q :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro U V a
    exact (Category.comp_id _).trans
      ((chartDiagramCohomologyMap_eq R Ω j f F q a).trans (Category.id_comp _).symm))

end AlgebraicGeometry.Scheme.EtaleCohomology.Stalk
