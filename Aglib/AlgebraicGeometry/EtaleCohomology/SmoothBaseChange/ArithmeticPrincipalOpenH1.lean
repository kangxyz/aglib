/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.AffineCoefficientTransport
public import Aglib.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.ArithmeticCurveH1
public import Aglib.AlgebraicGeometry.Spec.PrincipalClosedComplement

/-! # Arithmetic curve H1 vanishing for the original principal open

The genuine injective stays on the actual principal-open scheme in the
conclusion. Affine transport discharges the spectral coefficient restriction
of the arithmetic curve theorem without introducing a new vanishing premise.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u

attribute [local instance] hasSheafifyLarge hasSheafifyModules

/-- Uniform fixed-degree vanishing for the original arithmetic curve and
original genuine injective coefficient on its spectral base. -/
def ArithmeticCurveModuleInjectiveVanishing (q : ℕ) : Prop :=
  ∀ (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType ℤ R] [Algebra.FiniteType ℤ S]
    {X Y : Scheme.{u}} (p : X ⟶ Spec (.of R)) [SmoothOfRelativeDimension 1 p]
    (a : Y ⟶ X) (b : Y ⟶ Spec (.of S))
    (_H : IsPullback a b p (Spec.algebraMap R S))
    (n : ℕ) (_hn : 0 < n) (_hunit : IsUnit (n : R))
    (I : ModuleSheaf (Spec (.of S)) (ULift.{u + 1} (ZMod n))) [Injective I],
    IsZero ((higherDirectImage a q).obj ((inverseImage b).obj
      ((SheafOfModules.toSheaf (constantRing (Spec (.of S))
        (ULift.{u + 1} (ZMod n)))).obj I)))

/-- The actual arithmetic H1 producer supplies the first fixed-degree property. -/
theorem arithmeticCurveModuleInjectiveVanishing_one :
    ArithmeticCurveModuleInjectiveVanishing.{u} 1 := by
  intro R S hR hS hRS hfinR hfinS X Y p hp a b H n hn hunit I hI
  exact higherDirectImage_arithmetic_curve_injective_one_isZero
    R S p a b H n hn hunit I

/-- A fixed-degree arithmetic vanishing supplier extends to the original
arbitrary affine finite-type coefficient scheme. -/
theorem higherDirectImage_arithmetic_curve_affine_injective_isZero
    (q : ℕ) (hvan : ArithmeticCurveModuleInjectiveVanishing.{u} q)
    (R : Type u) [CommRing R] [Algebra.FiniteType ℤ R]
    {X Y U : Scheme.{u}} [IsAffine U]
    (p : X ⟶ Spec (.of R)) [SmoothOfRelativeDimension 1 p]
    (a : Y ⟶ X) (b : Y ⟶ U) (j : U ⟶ Spec (.of R)) [LocallyOfFiniteType j]
    (H : IsPullback a b p j) (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : R))
    (I : ModuleSheaf U (ULift.{u + 1} (ZMod n))) [Injective I] :
    IsZero ((higherDirectImage a q).obj ((inverseImage b).obj
      ((SheafOfModules.toSheaf (constantRing U (ULift.{u + 1} (ZMod n)))).obj I))) := by
  apply higherDirectImage_injective_isZero_of_affine_coefficient
    R p a b j H (ULift.{u + 1} (ZMod n)) q ?_ I
  intro S hS hRS hfin b' H' J hJ
  exact hvan R S p a b' H' n hn hunit J

/-- Fixed-degree vanishing on the actual principal-open higher-image summand.
This is the lower-degree supplier for outer cohomological induction. -/
theorem higherDirectImage_arithmetic_principalOpen_injective_isZero
    (q : ℕ) (hvan : ArithmeticCurveModuleInjectiveVanishing.{u} q)
    (S : Type u) [CommRing S] [Algebra.FiniteType ℤ S] (s : S)
    {T V : Scheme.{u}} (b : T ⟶ Spec (.of S)) [SmoothOfRelativeDimension 1 b]
    (j' : V ⟶ T) (bU : V ⟶ (principalSupportOpen S s).toScheme)
    (H : IsPullback bU j' (principalSupportOpen S s).ι b)
    (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : S))
    (J : ModuleSheaf (principalSupportOpen S s).toScheme (ULift.{u + 1} (ZMod n)))
    [Injective J] :
    IsZero ((higherDirectImage j' q).obj ((inverseImage bU).obj
      ((SheafOfModules.toSheaf (constantRing (principalSupportOpen S s).toScheme
        (ULift.{u + 1} (ZMod n)))).obj J))) := by
  let : IsAffine (principalSupportOpen S s).toScheme := by
    exact IsAffineOpen.Spec_basicOpen (R := CommRingCat.of S) s
  exact higherDirectImage_arithmetic_curve_affine_injective_isZero q hvan
    S b j' bU (principalSupportOpen S s).ι H.flip n hn hunit J

/-- Arithmetic curve degree-one vanishing for any actual affine coefficient
scheme locally of finite type over the original arithmetic base. -/
theorem higherDirectImage_arithmetic_curve_affine_injective_one_isZero
    (R : Type u) [CommRing R] [Algebra.FiniteType ℤ R]
    {X Y U : Scheme.{u}} [IsAffine U]
    (p : X ⟶ Spec (.of R)) [SmoothOfRelativeDimension 1 p]
    (a : Y ⟶ X) (b : Y ⟶ U) (j : U ⟶ Spec (.of R)) [LocallyOfFiniteType j]
    (H : IsPullback a b p j) (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : R))
    (I : ModuleSheaf U (ULift.{u + 1} (ZMod n))) [Injective I] :
    IsZero ((higherDirectImage a 1).obj ((inverseImage b).obj
      ((SheafOfModules.toSheaf (constantRing U (ULift.{u + 1} (ZMod n)))).obj I))) :=
  higherDirectImage_arithmetic_curve_affine_injective_isZero 1
    arithmeticCurveModuleInjectiveVanishing_one R p a b j H n hn hunit I

/-- The original principal-open higher-image summand vanishes in degree one
for every genuine injective on that same open scheme. -/
theorem higherDirectImage_arithmetic_principalOpen_injective_one_isZero
    (S : Type u) [CommRing S] [Algebra.FiniteType ℤ S] (s : S)
    {T V : Scheme.{u}} (b : T ⟶ Spec (.of S)) [SmoothOfRelativeDimension 1 b]
    (j' : V ⟶ T) (bU : V ⟶ (principalSupportOpen S s).toScheme)
    (H : IsPullback bU j' (principalSupportOpen S s).ι b)
    (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : S))
    (J : ModuleSheaf (principalSupportOpen S s).toScheme (ULift.{u + 1} (ZMod n)))
    [Injective J] :
    IsZero ((higherDirectImage j' 1).obj ((inverseImage bU).obj
      ((SheafOfModules.toSheaf (constantRing (principalSupportOpen S s).toScheme
        (ULift.{u + 1} (ZMod n)))).obj J))) :=
  higherDirectImage_arithmetic_principalOpen_injective_isZero 1
    arithmeticCurveModuleInjectiveVanishing_one S s b j' bU H n hn hunit J

end AlgebraicGeometry.Scheme.EtaleCohomology
