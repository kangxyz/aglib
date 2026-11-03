/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Localization.ModuleInjectiveClassDetection
public import Aglib.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.OrdinaryCartesian
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.ZMod
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.Exactness

/-! # Smooth two-branch detection with genuine bounded module coefficients

Ordinary smooth exchange supplies the formerly conditional degree-zero input
for the original Cartesian open square. The coefficient is the original module
sheaf over the constant lifted ZMod ring. Lower-degree vanishing, open
restriction zero and closed transformed-class zero are still required.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

/-- An additive functor preserves the original scalar annihilator equation. -/
private theorem nsmul_id_eq_zero_map
    {C D : Type*} [Category C] [Preadditive C] [Category D] [Preadditive D]
    (F : C ⥤ D) [F.Additive] (A : C) (n : ℕ) (h : n • 𝟙 A = 0) :
    n • 𝟙 (F.obj A) = 0 := by
  have hF := congrArg F.map h
  rw [F.map_nsmul, F.map_id, F.map_zero] at hF
  exact hF

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u eT eV eW dT dV dA

attribute [local instance] hasSheafifyLarge hasSheafifyModules


variable {X U Z T V W : Scheme.{u}}
  [HasExt.{eT} (AbelianSheaf.{u, u + 1} T)]
  [HasExt.{eV} (AbelianSheaf.{u, u + 1} V)]
  [HasExt.{eW} (AbelianSheaf.{u, u + 1} W)]
  [HasDerivedCategory.{dT} (AbelianSheaf.{u, u + 1} T)]
  [HasDerivedCategory.{dV} (AbelianSheaf.{u, u + 1} V)]
  [HasDerivedCategory.{dA} AddCommGrpCat.{u + 1}]

/-- Actual bounded module coefficients supply the canonical ordinary exchange;
the remaining two-branch class-detection inputs are unchanged. -/
theorem exists_smooth_moduleInjective_class_detection_of_killed
    (j : U ⟶ X) [IsOpenImmersion j] (i : Z ⟶ X) [IsClosedImmersion i]
    (hcomp : Set.range j = (Set.range i)ᶜ)
    (Λ : Type (u + 1)) [Ring Λ] (n : ℕ) (hn : 0 < n)
    (I : ModuleSheaf X Λ) [Injective I] (hI : n • 𝟙 I = 0) :
    ∃ J : ModuleSheaf Z Λ, Injective J ∧
      ∃ a : (moduleInverseImage i Λ).obj I ⟶ J, Mono a ∧
        ∀ (b : T ⟶ X) (j' : V ⟶ T) (bU : V ⟶ U)
          (_hj : IsPullback bU j' j b) (_hb : Smooth b) (i' : W ⟶ T) (bZ : W ⟶ Z)
          (hi : IsPullback bZ i' i b),
          ∀ (q : ℕ), 0 < q →
            (∀ r : ℕ, 1 ≤ r → r < q →
              IsZero ((higherDirectImage j' r).obj ((inverseImage bU).obj
                ((SheafOfModules.toSheaf (constantRing U Λ)).obj
                  ((moduleInverseImage j Λ).obj I))))) →
            ∀ x : Sheaf.H.{eT} ((inverseImage b).obj
              ((SheafOfModules.toSheaf (constantRing X Λ)).obj I)) q,
              cohomologyPullback j' _ q x = 0 →
              Sheaf.H.map
                (moduleClosedPullbackCoefficientMap i i' b bZ hi.w.symm
                  Λ I J a) q
                (cohomologyPullback i' _ q x) = 0 →
              x = 0 := by
  have hIj := nsmul_id_eq_zero_map (moduleInverseImage j Λ) I n hI
  have hF := nsmul_id_eq_zero_map (SheafOfModules.toSheaf (constantRing U Λ))
    ((moduleInverseImage j Λ).obj I) n hIj
  obtain ⟨J, hJ, a, ha, hdetect⟩ :=
    exists_moduleInjective_open_closed_cohomology_detection j i hcomp Λ I
  refine ⟨J, hJ, a, ha, ?_⟩
  intro b j' bU hj hb i' bZ hi q hq hvan x hopen hclosed
  let : Smooth b := hb
  let := baseChangeMap_smooth_bounded_isIso_of_isPullback j j' b bU hj
    ((SheafOfModules.toSheaf (constantRing U Λ)).obj
      ((moduleInverseImage j Λ).obj I)) n hn hF
  have ho := moduleOpenSummand_eq_zero_of_restriction
    j j' b bU hj.w.symm Λ I q hq hvan x hopen
  have hc := moduleClosedSummand_eq_zero i i' b bZ hi Λ I J a q x hclosed
  exact hdetect b q x ho hc

/-- Actual bounded module coefficients supply the canonical ordinary exchange;
the remaining two-branch class-detection inputs are unchanged. -/
theorem exists_smooth_moduleInjective_class_detection
    (j : U ⟶ X) [IsOpenImmersion j] (i : Z ⟶ X) [IsClosedImmersion i]
    (hcomp : Set.range j = (Set.range i)ᶜ)
    (n : ℕ) (hn : 0 < n)
    (I : ModuleSheaf X (ULift.{u + 1} (ZMod n))) [Injective I] :
    ∃ J : ModuleSheaf Z (ULift.{u + 1} (ZMod n)), Injective J ∧
      ∃ a : (moduleInverseImage i (ULift.{u + 1} (ZMod n))).obj I ⟶ J, Mono a ∧
        ∀ (b : T ⟶ X) (j' : V ⟶ T) (bU : V ⟶ U)
          (_hj : IsPullback bU j' j b) (_hb : Smooth b) (i' : W ⟶ T) (bZ : W ⟶ Z)
          (hi : IsPullback bZ i' i b),
          ∀ (q : ℕ), 0 < q →
            (∀ r : ℕ, 1 ≤ r → r < q →
              IsZero ((higherDirectImage j' r).obj ((inverseImage bU).obj
                ((SheafOfModules.toSheaf (constantRing U (ULift.{u + 1} (ZMod n)))).obj
                  ((moduleInverseImage j (ULift.{u + 1} (ZMod n))).obj I))))) →
            ∀ x : Sheaf.H.{eT} ((inverseImage b).obj
              ((SheafOfModules.toSheaf (constantRing X (ULift.{u + 1} (ZMod n)))).obj I)) q,
              cohomologyPullback j' _ q x = 0 →
              Sheaf.H.map
                (moduleClosedPullbackCoefficientMap i i' b bZ hi.w.symm
                  (ULift.{u + 1} (ZMod n)) I J a) q
                (cohomologyPullback i' _ q x) = 0 →
              x = 0 :=
  exists_smooth_moduleInjective_class_detection_of_killed
    (T := T) (V := V) (W := W) j i hcomp (ULift.{u + 1} (ZMod n)) n hn I
    (ModuleCat.Sheaf.ConstantRing.uLiftZMod_nsmul_id_eq_zero
      (Scheme.smallEtaleTopology X) n I)

end AlgebraicGeometry.Scheme.EtaleCohomology
