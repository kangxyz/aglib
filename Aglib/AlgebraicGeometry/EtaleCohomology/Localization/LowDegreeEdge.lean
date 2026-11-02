/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.LowDegreeEdge
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.SingleCounit
public import Aglib.AlgebraicGeometry.EtaleCohomology.PullbackComposition

/-! # The original low-degree direct-image edge

The edge is literally original cohomological pullback followed by the original
inverse-image/direct-image coefficient counit. Lower higher-image vanishing
implies injectivity; vanishing in the degree being proved is never assumed.
This applies to every scheme morphism and in particular to an open immersion.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u eX eY dX dY dA

attribute [local instance] hasSheafifyLarge

variable {X Y : Scheme.{u}}
  [HasExt.{eX} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{eY} (AbelianSheaf.{u, u + 1} Y)]

/-- The original edge uses the original cohomological pullback and counit. -/
def cohomologyDirectImageEdge (f : Y ⟶ X) (A : AbelianSheaf.{u, u + 1} Y) (q : ℕ) :
    Sheaf.H.{eX} ((directImage f).obj A) q →+ Sheaf.H.{eY} A q :=
  (Sheaf.H.map ((inverseImageAdjunction f).counit.app A) q).comp
    (cohomologyPullback f ((directImage f).obj A) q)

/-- No separately chosen edge map is used. -/
theorem cohomologyDirectImageEdge_apply (f : Y ⟶ X)
    (A : AbelianSheaf.{u, u + 1} Y) (q : ℕ)
    (x : Sheaf.H.{eX} ((directImage f).obj A) q) :
    cohomologyDirectImageEdge f A q x =
      Sheaf.H.map ((inverseImageAdjunction f).counit.app A) q
        (cohomologyPullback f ((directImage f).obj A) q x) := rfl

variable [HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{dY} (AbelianSheaf.{u, u + 1} Y)]
  [HasDerivedCategory.{dA} AddCommGrpCat.{u + 1}]

/-- The first possibly nonzero higher-image degree gives an injection of the
original cohomology groups. The two Ext and three derived universes are independent. -/
theorem cohomologyDirectImageEdge_injective (f : Y ⟶ X)
    (A : AbelianSheaf.{u, u + 1} Y) (q : ℕ) (hq : 0 < q)
    (hvan : ∀ a : ℕ, 1 ≤ a → a < q → IsZero ((higherDirectImage f a).obj A)) :
    Function.Injective (cohomologyDirectImageEdge f A q) := by
  let p := rightDerivedGlobalSectionsPullback f ((directImage f).obj A) q ≫
    ((globalSections Y).rightDerived q).map ((inverseImageAdjunction f).counit.app A)
  have hp : p =
      ((globalSections X).rightDerivedSingleHomologyIso q).hom.app ((directImage f).obj A) ≫
        (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} (q : ℤ)).map
          ((derivedGlobalSections X).map ((directImage f).rightDerivedSingleUnit A) ≫
            (derivedDirectImageGlobalSectionsIso f).hom.app
              ((DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} Y) 0).obj A)) ≫
        ((globalSections Y).rightDerivedSingleHomologyIso q).inv.app A :=
    Adjunction.rightDerivedUnitSectionsPullback_counit (inverseImageAdjunction f)
      (globalSections X) (directImageGlobalSectionsIso f) A q
  let : Mono ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} (q : ℤ)).map
      ((derivedGlobalSections X).map ((directImage f).rightDerivedSingleUnit A))) :=
    (globalSections X).mono_homology_rightDerived_singleUnit (directImage f) A q hq hvan
  have hpmono : Mono p := by
    rw [hp, Functor.map_comp]
    infer_instance
  have hpinj : Function.Injective p := (AddCommGrpCat.mono_iff_injective p).mp hpmono
  have he (x : Sheaf.H.{eX} ((directImage f).obj A) q) :
      cohomologyRightDerivedAddEquiv A q (cohomologyDirectImageEdge f A q x) =
        p (cohomologyRightDerivedAddEquiv ((directImage f).obj A) q x) := by
    rw [cohomologyDirectImageEdge_apply, cohomologyRightDerivedAddEquiv_naturality]
    dsimp only [Functor.comp_obj]
    rw [cohomologyRightDerivedAddEquiv_pullback]
    rfl
  intro x y hxy
  apply (cohomologyRightDerivedAddEquiv ((directImage f).obj A) q).injective
  apply hpinj
  rw [← he x, ← he y, hxy]

/-- Degree one needs no positive higher-image vanishing hypotheses. -/
theorem cohomologyDirectImageEdge_one_injective (f : Y ⟶ X)
    (A : AbelianSheaf.{u, u + 1} Y) :
    Function.Injective (cohomologyDirectImageEdge f A 1) :=
  cohomologyDirectImageEdge_injective f A 1 (by omega) (by intro a ha h; omega)

end AlgebraicGeometry.Scheme.EtaleCohomology
