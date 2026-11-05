/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Spec.PrincipalClosedComplement
public import Aglib.AlgebraicGeometry.EtaleCohomology.Localization.SmoothModuleInjectiveClassDetection
public import Aglib.RingTheory.KrullDimension.FiniteClosedSupport

/-! # The actual smaller principal closed branch of injective H1 effacement

The original quotient Spec(L/(s)), its complement D(s), a genuine closed
injective and the original coefficient monomorphism are constructed together.
The same quotient has the smaller dimension bound after an actual finite
coefficient transformation and localization. Original smooth H1 classes are
detected by the two branches, with no lower-degree exchange hypothesis.

This produces the closed branch and its actual class detector. It does not
assert that the transformed closed class vanishes, and does not turn an
arbitrary source refinement into a refinement on the original target axis.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u eY eV eW dY dV dA

attribute [local instance] hasSheafifyLarge hasSheafifyModules

variable (L : Type u) [CommRing L] (s : L)

local notation "j" => Scheme.Opens.ι (principalSupportOpen L s)
local notation "i" => principalSupportClosedMap L s

/-- Produce the actual genuine closed injective on the literal quotient, then
consume original open-zero and transformed closed-zero on any smooth Cartesian
family. The degree-one lower-vanishing interval is proved empty internally. -/
theorem exists_principalClosed_H1_detector
    {Y V W : Scheme.{u}}
    [HasExt.{eY} (AbelianSheaf.{u, u + 1} Y)]
    [HasExt.{eV} (AbelianSheaf.{u, u + 1} V)]
    [HasExt.{eW} (AbelianSheaf.{u, u + 1} W)]
    [HasDerivedCategory.{dY} (AbelianSheaf.{u, u + 1} Y)]
    [HasDerivedCategory.{dV} (AbelianSheaf.{u, u + 1} V)]
    [HasDerivedCategory.{dA} AddCommGrpCat.{u + 1}]
    (n : ℕ) (hn : 0 < n)
    (I : ModuleSheaf (Spec (.of L)) (ULift.{u + 1} (ZMod n))) [Injective I] :
    ∃ J : ModuleSheaf (Spec (CommRingCat.of (L ⧸ Ideal.span {s})))
        (ULift.{u + 1} (ZMod n)), Injective J ∧
      ∃ a : (moduleInverseImage i (ULift.{u + 1} (ZMod n))).obj I ⟶ J, Mono a ∧
        ∀ (b : Y ⟶ Spec (.of L)) (j' : V ⟶ Y)
          (bU : V ⟶ (principalSupportOpen L s).toScheme)
          (_hj : IsPullback bU j' j b) (_hb : Smooth b)
          (i' : W ⟶ Y) (bZ : W ⟶ Spec (CommRingCat.of (L ⧸ Ideal.span {s})))
          (hi : IsPullback bZ i' i b),
          ∀ c : Sheaf.H.{eY} ((inverseImage b).obj
            ((SheafOfModules.toSheaf (constantRing (Spec (.of L))
              (ULift.{u + 1} (ZMod n)))).obj I)) 1,
            cohomologyPullback j' _ 1 c = 0 →
            Sheaf.H.map
              (moduleClosedPullbackCoefficientMap i i' b bZ hi.w.symm
                (ULift.{u + 1} (ZMod n)) I J a) 1
              (cohomologyPullback i' _ 1 c) = 0 → c = 0 := by
  let : IsClosedImmersion (principalSupportClosedMap L s) :=
    IsClosedImmersion.spec_of_surjective
      (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {s})))
      Ideal.Quotient.mk_surjective
  obtain ⟨J, hJ, a, ha, hdetect⟩ :=
    exists_smooth_moduleInjective_class_detection
      (T := Y) (V := V) (W := W) j i (principalSupport_complement L s) n hn I
  refine ⟨J, hJ, a, ha, ?_⟩
  intro b j' bU hj hb i' bZ hi c hopen hclosed
  exact hdetect b j' bU hj hb i' bZ hi 1 (by omega)
    (by intro r hr hr1; omega) c hopen hclosed

/-- The original principal closed branch after finite transformation and
localization has a strictly smaller induction bound. No replacement quotient
or separate dimension certificate for the transformed ring is used. -/
theorem principalClosed_rank_after_finite_localization
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    (M : Submonoid S) [Algebra S L] [IsLocalization M L] [IsDomain L]
    (hs : s ≠ 0) (d : ℕ) (hd : ringKrullDim R ≤ (d + 1 : ℕ)) :
    ringKrullDim (L ⧸ Ideal.span {s}) ≤ (d : ℕ) :=
  Algebra.finite_localized_principalComplement_le_predecessor R S M L s hs d hd

end AlgebraicGeometry.Scheme.EtaleCohomology
