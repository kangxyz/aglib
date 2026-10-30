/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.CompactSupport.OpenLocalization
public import Aglib.AlgebraicGeometry.EtaleCohomology.CompactSupport.CurveRoots
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.RootsComposition
public import Aglib.CategoryTheory.Adjunction.LowerShriekUnderlying

/-!
# Roots extension under composition of open immersions

The original lower-shriek composition comparison and counits, together with the intrinsic
roots inverse-image equation, give the whole coefficient extension square. All-degree original
cohomology compatibility follows by applying `Sheaf.H`; no finite-complement or curve premise
is needed for the square itself.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open GroupCohomology.Kummer.Coefficients GroupCohomology.Kummer.CoefficientBaseChange

universe u w

namespace AlgebraicGeometry.Scheme.EtaleCohomology

variable {V U X : Scheme.{u}} (j : U ⟶ X) (i : V ⟶ U)
  [IsOpenImmersion j] [IsOpenImmersion i]

/-- The whole original lower-shriek counit equation before coefficient evaluation. -/
theorem etaleLowerShriekCompIso_counit :
    Functor.whiskerLeft (inverseImage j ⋙ inverseImage i) (etaleLowerShriekCompIso j i).hom ≫
        ((etaleLowerShriekAdjunction i).comp (etaleLowerShriekAdjunction j)).counit =
      ((etaleLowerShriekAdjunction (i ≫ j)).ofNatIsoRight (inverseImageComp j i)).counit :=
  Adjunction.comparison_counit (etaleLowerShriekAdjunction (i ≫ j))
    (etaleLowerShriekAdjunction i) (etaleLowerShriekAdjunction j) (inverseImageComp j i)

/-- Evaluating the whole counit equation retains both original counits. -/
theorem etaleLowerShriekCompIso_counit_app (F : AbelianSheaf.{u, u + 1} X) :
    (etaleLowerShriekCompIso j i).hom.app ((inverseImage i).obj ((inverseImage j).obj F)) ≫
      (etaleLowerShriek j).map
        ((etaleLowerShriekAdjunction i).counit.app ((inverseImage j).obj F)) ≫
      (etaleLowerShriekAdjunction j).counit.app F =
    (etaleLowerShriek (i ≫ j)).map ((inverseImageComp j i).inv.app F) ≫
      (etaleLowerShriekAdjunction (i ≫ j)).counit.app F :=
  Adjunction.comparison_counit_app (etaleLowerShriekAdjunction (i ≫ j))
    (etaleLowerShriekAdjunction i) (etaleLowerShriekAdjunction j) (inverseImageComp j i) F

namespace CompactSupport

variable (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤)))

/-- The original roots extension map composes through the original lower-shriek comparison. -/
theorem rootsExtensionMap_comp :
    (etaleLowerShriekCompIso j i).hom.app (mu V n) ≫
      (etaleLowerShriek j).map (rootsExtensionMap i n hn (levelInvertible j n hinv)) ≫
      rootsExtensionMap j n hn hinv = rootsExtensionMap (i ≫ j) n hn hinv :=
  Adjunction.coefficient_counit_comp (etaleLowerShriekAdjunction (i ≫ j))
    (etaleLowerShriekAdjunction i) (etaleLowerShriekAdjunction j) (inverseImageComp j i)
    (rootsPullbackIso j n hn hinv) (rootsPullbackIso i n hn (levelInvertible j n hinv))
    (rootsPullbackIso (i ≫ j) n hn hinv)
    (GroupCohomology.Kummer.CoefficientBaseChange.rootsPullbackIso_comp j i n hn hinv)

/-- The original point-removal extension and roots coefficient comparison commute as sheaf maps. -/
theorem rootsExtensionMap_extension :
    (etaleLowerShriek (i ≫ j)).map
        (rootsPullbackIso i n hn (levelInvertible j n hinv)).hom ≫
      rootsExtensionMap (i ≫ j) n hn hinv =
        extensionMap i j (mu U n) ≫ rootsExtensionMap j n hn hinv := by
  rw [extensionMap_eq_compIso_counit, Category.assoc]
  exact Adjunction.coefficient_counit_extension (etaleLowerShriekAdjunction (i ≫ j))
    (etaleLowerShriekAdjunction i) (etaleLowerShriekAdjunction j) (inverseImageComp j i)
    (rootsPullbackIso j n hn hinv) (rootsPullbackIso i n hn (levelInvertible j n hinv))
    (rootsPullbackIso (i ≫ j) n hn hinv)
    (GroupCohomology.Kummer.CoefficientBaseChange.rootsPullbackIso_comp j i n hn hinv)

variable [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]

/-- Applying original cohomology to the coefficient square gives the whole roots extension map. -/
theorem rootsMap_extension (q : ℕ) :
    (rootsMap (i ≫ j) n hn hinv q).comp
        (H.map (i ≫ j) (rootsPullbackIso i n hn (levelInvertible j n hinv)).hom q) =
      (rootsMap j n hn hinv q).comp (extensionCohomologyMap i j (mu U n) q) := by
  apply AddMonoidHom.ext
  intro x
  change Sheaf.H.map (rootsExtensionMap (i ≫ j) n hn hinv) q
    (Sheaf.H.map ((etaleLowerShriek (i ≫ j)).map
      (rootsPullbackIso i n hn (levelInvertible j n hinv)).hom) q x) =
      Sheaf.H.map (rootsExtensionMap j n hn hinv) q
        (Sheaf.H.map (extensionMap i j (mu U n)) q x)
  rw [← Sheaf.H.map_comp_apply, ← Sheaf.H.map_comp_apply, rootsExtensionMap_extension]

end CompactSupport

end AlgebraicGeometry.Scheme.EtaleCohomology
