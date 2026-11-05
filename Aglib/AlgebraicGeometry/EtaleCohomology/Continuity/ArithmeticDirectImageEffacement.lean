/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.SupportInduction.ArithmeticCurvePointedPositive
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.Exactness

/-! # Arithmetic curve effacement for actual direct-image coefficients

The original ringed module is pushed forward along the given coefficient map.
Exact module inverse image proves genuine injectivity of that direct image.
Its native underlying comparison transports the original class to the
arithmetic producer and back. No abelian-sheaf injectivity is asserted.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
open Coefficients
universe u
attribute [local instance] hasSheafifyLarge hasSheafifyModules HasExt.standard

/-- The actual abelian direct image of a genuine injective module supplies
pointed positive-degree effacement on an arithmetic curve, with the original class retained. -/
theorem exists_arithmetic_directImage_pointed_positive_refinement
    (q : ℕ) (hq : 0 < q)
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType ℤ R] [Algebra.FiniteType ℤ S]
    {X Y T : Scheme.{u}} (p : X ⟶ Spec (.of R)) [SmoothOfRelativeDimension 1 p]
    (a : Y ⟶ X) (b : Y ⟶ Spec (.of S))
    (H : IsPullback a b p (Spec.algebraMap R S))
    (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : R))
    (t : T ⟶ Spec (.of S))
    (I : ModuleSheaf T (ULift.{u + 1} (ZMod n))) [Injective I]
    (c : Sheaf.H.{u + 2} ((inverseImage b).obj ((directImage t).obj
      ((SheafOfModules.toSheaf (constantRing T (ULift.{u + 1} (ZMod n)))).obj I))) q)
    (Ω : Type u) [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ X) :
    ∃ (U : X.Etale) (xU : Spec (.of Ω) ⟶ U.left), xU ≫ U.hom = x ∧
      cohomologyPullback.{u, u + 2, u + 2} (pullback.snd U.hom a) _ q c = 0 := by
  let Λ := ULift.{u + 1} (ZMod n)
  let J := (moduleDirectImage t Λ).obj I
  let : Injective J := (moduleDirectImage t Λ).injective_obj I
  let E := (inverseImage b).mapIso ((moduleDirectImageUnderlyingIso t Λ).app I)
  let cJ := Sheaf.H.map E.inv q c
  obtain ⟨U, xU, hx, hc⟩ := exists_arithmetic_curve_pointed_positive_refinement
    q hq R S p a b H n hn hunit J cJ Ω x
  refine ⟨U, xU, hx, ?_⟩
  apply Sheaf.H.map_injective_of_isIso ((inverseImage (pullback.snd U.hom a)).map E.inv) q
  exact (cohomologyPullback_coefficientMap (pullback.snd U.hom a) E.inv q c).symm.trans
    (hc.trans (map_zero _).symm)


/-- The actual abelian direct image of a genuine injective module supplies
pointed H1 effacement on an arithmetic curve, with the original class retained. -/
theorem exists_arithmetic_directImage_pointed_H1_refinement
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType ℤ R] [Algebra.FiniteType ℤ S]
    {X Y T : Scheme.{u}} (p : X ⟶ Spec (.of R)) [SmoothOfRelativeDimension 1 p]
    (a : Y ⟶ X) (b : Y ⟶ Spec (.of S))
    (H : IsPullback a b p (Spec.algebraMap R S))
    (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : R))
    (t : T ⟶ Spec (.of S))
    (I : ModuleSheaf T (ULift.{u + 1} (ZMod n))) [Injective I]
    (c : Sheaf.H.{u + 2} ((inverseImage b).obj ((directImage t).obj
      ((SheafOfModules.toSheaf (constantRing T (ULift.{u + 1} (ZMod n)))).obj I))) 1)
    (Ω : Type u) [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ X) :
    ∃ (U : X.Etale) (xU : Spec (.of Ω) ⟶ U.left), xU ≫ U.hom = x ∧
      cohomologyPullback.{u, u + 2, u + 2} (pullback.snd U.hom a) _ 1 c = 0 := by
  exact exists_arithmetic_directImage_pointed_positive_refinement
    1 (by omega) R S p a b H n hn hunit t I c Ω x

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
