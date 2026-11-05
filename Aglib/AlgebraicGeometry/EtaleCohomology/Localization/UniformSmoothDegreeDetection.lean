/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Localization.SmoothModuleInjectiveClassDetection
public import Aglib.CategoryTheory.Preadditive.Annihilator

/-! # One genuine closed coefficient for all smooth target refinements

The closed injective and monomorphism are chosen before any target scheme,
cartesian square, or class. The same original lower-rank coefficient can
therefore be used for induction and for every subsequent pointed refinement.
Only lower positive degrees r < q are required; degree q vanishing is not
an input. A new existential choice of closed injective at the refined stage would not
identify the residual class already annihilated by induction.
-/

@[expose] public noncomputable section
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u eT eV eW dT dV dA
attribute [local instance] hasSheafifyLarge hasSheafifyModules

/-- Construct one genuine closed coefficient and its original monomorphism,
with fixed-degree detection uniform over all later smooth cartesian target families. -/
theorem exists_uniform_smooth_moduleInjective_degree_detector
    {X U Z : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (i : Z ⟶ X) [IsClosedImmersion i]
    (hcomp : Set.range j = (Set.range i)ᶜ)
    (n : ℕ) (hn : 0 < n)
    (I : ModuleSheaf X (ULift.{u + 1} (ZMod n))) [Injective I] :
    ∃ J : ModuleSheaf Z (ULift.{u + 1} (ZMod n)), Injective J ∧
      ∃ a : (moduleInverseImage i (ULift.{u + 1} (ZMod n))).obj I ⟶ J, Mono a ∧
        ∀ {T V W : Scheme.{u}}
          [HasExt.{eT} (AbelianSheaf.{u, u + 1} T)]
          [HasExt.{eV} (AbelianSheaf.{u, u + 1} V)]
          [HasExt.{eW} (AbelianSheaf.{u, u + 1} W)]
          [HasDerivedCategory.{dT} (AbelianSheaf.{u, u + 1} T)]
          [HasDerivedCategory.{dV} (AbelianSheaf.{u, u + 1} V)]
          [HasDerivedCategory.{dA} AddCommGrpCat.{u + 1}]
          (b : T ⟶ X) (j' : V ⟶ T) (bU : V ⟶ U)
          (_hj : IsPullback bU j' j b) (_ : Smooth b)
          (i' : W ⟶ T) (bZ : W ⟶ Z) (hi : IsPullback bZ i' i b)
          (q : ℕ) (_hq : 0 < q)
          (_hvan : ∀ r : ℕ, 1 ≤ r → r < q →
            IsZero ((higherDirectImage j' r).obj ((inverseImage bU).obj
              ((SheafOfModules.toSheaf (constantRing U
                (ULift.{u + 1} (ZMod n)))).obj
                ((moduleInverseImage j (ULift.{u + 1} (ZMod n))).obj I)))))
          (c : Sheaf.H.{eT} ((inverseImage b).obj
            ((SheafOfModules.toSheaf (constantRing X
              (ULift.{u + 1} (ZMod n)))).obj I)) q),
          cohomologyPullback j' _ q c = 0 →
          Sheaf.H.map
            (moduleClosedPullbackCoefficientMap i i' b bZ hi.w.symm
              (ULift.{u + 1} (ZMod n)) I J a) q
            (cohomologyPullback i' _ q c) = 0 → c = 0 := by
  obtain ⟨J, hJ, a, ha, hdetect⟩ :=
    exists_moduleInjective_open_closed_cohomology_detection.{u, eT}
      j i hcomp (ULift.{u + 1} (ZMod n)) I
  refine ⟨J, hJ, a, ha, ?_⟩
  intro T V W hT hV hW hDT hDV hDA b j' bU hj hb i' bZ hi q hq hvan c hopen hclosed
  let : Smooth b := hb
  have hkill := Functor.map_nsmul_id_eq_zero
    (SheafOfModules.toSheaf (constantRing U (ULift.{u + 1} (ZMod n))))
    ((moduleInverseImage j (ULift.{u + 1} (ZMod n))).obj I) n
    (ModuleCat.Sheaf.ConstantRing.uLiftZMod_nsmul_id_eq_zero
      (Scheme.smallEtaleTopology U) n
      ((moduleInverseImage j (ULift.{u + 1} (ZMod n))).obj I))
  let := baseChangeMap_smooth_bounded_isIso_of_isPullback j j' b bU hj
    ((SheafOfModules.toSheaf (constantRing U (ULift.{u + 1} (ZMod n)))).obj
      ((moduleInverseImage j (ULift.{u + 1} (ZMod n))).obj I)) n hn hkill
  have ho := moduleOpenSummand_eq_zero_of_restriction j j' b bU hj.w.symm
    (ULift.{u + 1} (ZMod n)) I q hq hvan c hopen
  have hc := moduleClosedSummand_eq_zero i i' b bZ hi
    (ULift.{u + 1} (ZMod n)) I J a q c hclosed
  exact hdetect b q c ho hc

end AlgebraicGeometry.Scheme.EtaleCohomology
