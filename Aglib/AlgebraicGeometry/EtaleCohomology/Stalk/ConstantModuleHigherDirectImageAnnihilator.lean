/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.ConstantModuleHigherDirectImageConstructible
public import Aglib.Algebra.Category.ModuleCat.AnnihilatorProperty
public import Aglib.CategoryTheory.Abelian.ObjectProperty.ExactInverseImage
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.ClosureConstructible
public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRing.Additive
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.Module.NatInt

/-! # Constructible native higher images of bounded-torsion constant modules

The original prime-killed producer and exact original constant functor feed
the general positive-annihilator producer. Every coefficient map and native
higher direct image is retained. Finite generation is over the original
Noetherian ring, without any finite underlying-group assumption.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u w s e wMX wMS wAX wAS

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify
  CategoryTheory.TorsionZMod.Ringed.hasSheafifyRingStandard
  CategoryTheory.TorsionZMod.Ringed.hasSheafifyAbStandard
  CategoryTheory.TorsionZMod.Ringed.ringWEqualsLocallyBijectiveStandard
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

open Coefficients

variable {X S : Scheme.{u}} [IsNoetherian S] (f : X ⟶ S) [IsProper f]
  (Λ : Type (u + 1)) [Ring Λ] [IsNoetherianRing Λ]
  [HasDerivedCategory.{wMX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wMS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wAX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{wAS} (AbelianSheaf.{u, u + 1} S)]
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [∀ U : S.Etale, HasExt.{s} (Sheaf ((Scheme.smallEtaleTopology X).over
    ((siteBaseChange f).obj U)) AddCommGrpCat.{u + 1})]
  [∀ U : S.Etale, HasExt.{max (u + 1) e}
    (AbelianSheaf.{u, u + 1} (pullback U.hom f))]

/-- Positive bounded torsion over a Noetherian coefficient ring suffices for
constructibility of every original native higher direct image of a finite-type
constant module. -/
theorem constantTorsionModuleNativeHigherDirectImage_isConstructible
    (n : ℕ) (hn : 0 < n) (M : ModuleCat.{u + 1} Λ) [Module.Finite Λ M]
    (hM : ∀ x : M, n • x = 0) (q : ℕ) :
    Constructible.Modules.IsConstructible
      ((moduleSheafEquivalence S Λ).inverse.obj
        (((moduleDirectImage f Λ).rightDerived q).obj
          ((moduleSheafEquivalence X Λ).functor.obj
            ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)))) := by
  let : (moduleSheafEquivalence X Λ).functor.Additive :=
    ModuleCat.Sheaf.ConstantRing.moduleSheafEquivalence_functor_additive.{u + 1, u, u + 1, u + 1}
      X.smallEtaleTopology Λ
  let : (moduleSheafEquivalence S Λ).inverse.Additive :=
    ModuleCat.Sheaf.ConstantRing.moduleSheafEquivalence_inverse_additive.{u + 1, u, u + 1, u + 1}
      S.smallEtaleTopology Λ
  let K := constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⋙
    (moduleSheafEquivalence X Λ).functor
  let P : ObjectProperty (ModuleSheaf S Λ) :=
    ObjectProperty.inverseImage
      (Constructible.Modules.IsConstructible (R := Λ) (X := S) :
        ObjectProperty (ModuleValuedSheaf S Λ))
      (moduleSheafEquivalence S Λ).inverse
  let : K.Additive := by dsimp only [K]; infer_instance
  let : PreservesFiniteLimits K := by dsimp [K, constantSheaf]; infer_instance
  let : PreservesFiniteColimits K := by dsimp [K, constantSheaf]; infer_instance
  exact ModuleCat.rightDerived_property_of_positive_annihilator Λ K
    (moduleDirectImage f Λ) P n hn
    (fun p hp _ N _ hN j => by
      let : Fact p.Prime := ⟨hp⟩
      exact constantPrimeKilledModuleNativeHigherDirectImage_isConstructible
        f Λ p N hN j) M hM q

/-- In particular every positive prime power is an admissible annihilator. -/
theorem constantPrimePowerKilledModuleNativeHigherDirectImage_isConstructible
    (p : ℕ) [Fact p.Prime] (r : ℕ) (M : ModuleCat.{u + 1} Λ) [Module.Finite Λ M]
    (hM : ∀ x : M, p ^ r • x = 0) (q : ℕ) :
    Constructible.Modules.IsConstructible
      ((moduleSheafEquivalence S Λ).inverse.obj
        (((moduleDirectImage f Λ).rightDerived q).obj
          ((moduleSheafEquivalence X Λ).functor.obj
            ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)))) :=
  constantTorsionModuleNativeHigherDirectImage_isConstructible f Λ (p ^ r)
    (pow_pos (Nat.Prime.pos (Fact.out)) r) M hM q

/-- The original valued higher image is constructible by the same original
native-to-valued comparison, not by installing a new scalar action. -/
theorem constantTorsionModuleValuedHigherDirectImage_isConstructible
    (n : ℕ) (hn : 0 < n) (M : ModuleCat.{u + 1} Λ) [Module.Finite Λ M]
    (hM : ∀ x : M, n • x = 0) (q : ℕ) :
    Constructible.Modules.IsConstructible
      ((constantModuleValuedHigherDirectImage f Λ q).obj M) :=
  (Constructible.Modules.isConstructible_iff_of_iso
    ((moduleHigherDirectImageValuedComparison f Λ q).app
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M))).mp
    (constantTorsionModuleNativeHigherDirectImage_isConstructible f Λ n hn M hM q)

omit [IsNoetherianRing Λ] in
/-- A finite coefficient ring supplies its positive characteristic internally.
The input remains a finite-type module over that ring. -/
theorem constantFiniteRingModuleNativeHigherDirectImage_isConstructible [Finite Λ]
    (M : ModuleCat.{u + 1} Λ) [Module.Finite Λ M] (q : ℕ) :
    Constructible.Modules.IsConstructible
      ((moduleSheafEquivalence S Λ).inverse.obj
        (((moduleDirectImage f Λ).rightDerived q).obj
          ((moduleSheafEquivalence X Λ).functor.obj
            ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)))) := by
  let : IsNoetherianRing Λ := inferInstance
  apply constantTorsionModuleNativeHigherDirectImage_isConstructible f Λ (ringChar Λ)
    (Nat.pos_of_ne_zero (CharP.ringChar_ne_zero_of_finite Λ)) M ?_ q
  intro x
  rw [← Nat.cast_smul_eq_nsmul Λ, CharP.cast_eq_zero Λ (ringChar Λ), zero_smul]

end AlgebraicGeometry.Scheme.EtaleCohomology
