/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Ext.ShortExactComparison
public import Aglib.AlgebraicGeometry.EtaleCohomology.Pullback
public import Aglib.AlgebraicGeometry.EtaleCohomology.Torsion.Basic
public import Aglib.CategoryTheory.Sites.Torsion.Reduction

/-!
# Torsion reduction for the original cohomological pullback

The actual pullback map is stable under coefficient isomorphisms, zero
coefficients, and short exact extensions. If both actual cohomology functors
preserve countable filtered colimits, prime module-coefficient comparisons
therefore suffice for every torsion sheaf. Colimit preservation and the
prime comparisons remain explicit hypotheses; neither is asserted here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u w w'

attribute [local instance] hasSheafifyLarge

/-- The actual original cohomology functor in the coefficient variable. -/
def cohomologyFunctor (X : Scheme.{u})
    [HasExt.{w} (AbelianSheaf.{u, u + 1} X)] (n : ℕ) :
    AbelianSheaf.{u, u + 1} X ⥤ AddCommGrpCat.{w} :=
  extFunctorObj
    ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))) n

variable {X S : Scheme.{u}}
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{w'} (AbelianSheaf.{u, u + 1} S)]

/-- Original pullback, explicitly lifted to the common value universe of its two Ext models. -/
def cohomologyPullbackNatTrans (f : S ⟶ X) (n : ℕ) :
    cohomologyFunctor.{u, w} X n ⋙ AddCommGrpCat.uliftFunctor.{w', w} ⟶
      (inverseImage f ⋙ cohomologyFunctor.{u, w'} S n) ⋙
        AddCommGrpCat.uliftFunctor.{w, w'} :=
  (inverseImage f).extPrecompNatTrans
    (((inverseImageConstantIso f).app (AddCommGrpCat.of (ULift.{u + 1} ℤ))).inv) n

/-- The lifted component retains the original pullback and its two independent Ext universes. -/
theorem cohomologyPullbackNatTrans_app_apply (f : S ⟶ X)
    (F : AbelianSheaf.{u, u + 1} X) (n : ℕ) (x : Sheaf.H.{w} F n) :
    (cohomologyPullbackNatTrans.{u, w, w'} f n).app F (ULift.up x) =
      ULift.up (cohomologyPullback.{u, w, w'} f F n x) := rfl

/-- A zero coefficient has bijective original pullback in every degree. -/
theorem cohomologyPullback_bijective_of_isZero (f : S ⟶ X)
    (F : AbelianSheaf.{u, u + 1} X) (hF : IsZero F) (n : ℕ) :
    Function.Bijective (cohomologyPullback.{u, w, w'} f F n) :=
  (inverseImage f).extPrecompMap_bijective_of_isZero _ F hF n

/-- Actual coefficient isomorphisms preserve bijectivity of the original pullback. -/
theorem cohomologyPullback_bijective_of_iso (f : S ⟶ X)
    {F G : AbelianSheaf.{u, u + 1} X} (e : F ≅ G) (n : ℕ)
    (hF : Function.Bijective (cohomologyPullback.{u, w, w'} f F n)) :
    Function.Bijective (cohomologyPullback.{u, w, w'} f G n) :=
  (inverseImage f).extPrecompMap_bijective_of_iso _ e n hF

/-- The original pullback comparison is closed under short exact coefficient extensions. -/
theorem cohomologyPullback_bijective_of_shortExact (f : S ⟶ X)
    (T : ShortComplex (AbelianSheaf.{u, u + 1} X)) (hT : T.ShortExact)
    (h₁ : ∀ n, Function.Bijective (cohomologyPullback.{u, w, w'} f T.X₁ n))
    (h₃ : ∀ n, Function.Bijective (cohomologyPullback.{u, w, w'} f T.X₃ n)) (n : ℕ) :
    Function.Bijective (cohomologyPullback.{u, w, w'} f T.X₂ n) :=
  (inverseImage f).extPrecompMap_bijective_of_shortExact _ T hT h₁ h₃ n

/-- Countable cohomological continuity reduces torsion pullback to prime module coefficients. -/
theorem cohomologyPullback_bijective_of_prime_modules (f : S ⟶ X)
    [∀ n, PreservesColimitsOfShape ℕ (cohomologyFunctor.{u, w} X n)]
    [∀ n, PreservesColimitsOfShape ℕ (cohomologyFunctor.{u, w'} S n)]
    (hprime : ∀ (p : ℕ), p.Prime →
      ∀ M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ZMod p)),
      ∀ n, Function.Bijective (cohomologyPullback.{u, w, w'} f
        ((sheafCompose X.smallEtaleTopology
          (forget₂ (ModuleCat.{u + 1} (ZMod p)) AddCommGrpCat.{u + 1})).obj M) n))
    (F : AbelianSheaf.{u, u + 1} X) (hF : IsTorsion X F) :
    ∀ n, Function.Bijective (cohomologyPullback.{u, w, w'} f F n) := by
  apply Sheaf.property_of_prime_module_coefficients
    (fun G => ∀ n, Function.Bijective (cohomologyPullback.{u, w, w'} f G n))
    (fun e h n => cohomologyPullback_bijective_of_iso f e n (h n))
    (fun G hG n => cohomologyPullback_bijective_of_isZero f G hG n)
    hprime
    (fun T hT h₁ h₃ n => cohomologyPullback_bijective_of_shortExact f T hT h₁ h₃ n)
    ?_ F hF
  intro K hK n
  let : PreservesColimit K
      (extFunctorObj
        ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of (ULift.{u + 1} ℤ))) n) :=
    inferInstanceAs (PreservesColimit K (cohomologyFunctor.{u, w} X n))
  let : PreservesColimit K
      (inverseImage f ⋙ extFunctorObj
        ((constantSheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of (ULift.{u + 1} ℤ))) n) :=
    inferInstanceAs
      (PreservesColimit K (inverseImage f ⋙ cohomologyFunctor.{u, w'} S n))
  exact (inverseImage f).extPrecompMap_bijective_of_isColimit _ K (colimit.cocone K)
    (colimit.isColimit K) n (fun i => hK i n)

end AlgebraicGeometry.Scheme.EtaleCohomology
