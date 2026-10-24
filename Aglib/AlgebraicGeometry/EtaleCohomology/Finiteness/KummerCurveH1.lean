/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finiteness.KummerCurveTorsion
public import Aglib.AlgebraicGeometry.Picard.KummerH1
public import Aglib.AlgebraicGeometry.Curves.SmoothGeometry
public import Aglib.AlgebraicGeometry.Curves.PointDivisor.PoleFunctions

/-! # Original Kummer H1 finiteness on smooth proper curves

The ordinary Picard torsion finiteness theorem is transported by the native
actual Kummer classification. Proper geometrically integral constants supply
surjectivity of the nth-power map on global units. The original Ext universe
is arbitrary; the finite-image construction uses its native standard model
only to prove finiteness of the universe-independent Picard torsion group.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.OverField.Curve
open GroupCohomology.Kummer.Coefficients

universe u w
namespace AlgebraicGeometry.Scheme.EtaleCohomology.KummerFamilyValues

attribute [local instance] hasSheafifyLarge

/-- Original H1 of positive invertible roots of unity is finite on a smooth
proper geometrically connected curve over an algebraically closed field,
with its specified rational point. No PBC or Picard-representability premise. -/
theorem finite_roots_h1_of_curve {k : Type u} [Field k] [IsAlgClosed k]
    (X : FScheme k) (o : Spec (.of k) ⟶ X.left) (ho : o ≫ X.hom = 𝟙 _)
    (hX : Properties X) (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k))
    [HasExt.{w} (AbelianSheaf.{u, u + 1} X.left)] :
    Finite (H1Etale.{u, u + 1, w} X.left (mu X.left n)) := by
  let := hX.proper
  let := hX.smooth
  let := hX.isIntegral
  let := hX.isGeometricallyIntegral
  let := curveProperties_isNoetherian hX
  let (x : Scheme.ClosedPoint X.left) := PointDivisor.isDiscreteValuationRing_stalk X hX x
  have hfinite := finite_picard_torsion X o ho hX n hn hunit
  let : Finite (Torsion.picardTorsion X.left n) := hfinite
  have hroot := TrivializedPower.globalUnits_pow_surjective X.left X.hom
    (Scheme.constants_bijective_of_proper_geometricallyIntegral X).2 n hn
  have hinv : IsUnit (n : Γ(X.left, ⊤)) := by
    simpa only [map_natCast] using
      hunit.map (((Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop).hom)
  exact Finite.of_injective
    (KummerH1.h1PicardTorsionEquiv X.left EtaleDescent.etaleLineBundleDescent
      (stacks03AJ X.left) n hn hinv hroot)
    (KummerH1.h1PicardTorsionEquiv X.left EtaleDescent.etaleLineBundleDescent
      (stacks03AJ X.left) n hn hinv hroot).injective

end AlgebraicGeometry.Scheme.EtaleCohomology.KummerFamilyValues
