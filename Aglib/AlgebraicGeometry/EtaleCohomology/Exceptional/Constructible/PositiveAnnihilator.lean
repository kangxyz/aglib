/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.CategoryTheory.Abelian.ObjectProperty.AnnihilatorRightDerived
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Constructible.CompactificationHigherImage
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.ClosureConstructible
public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRing.Additive
public import Aglib.CategoryTheory.Abelian.ObjectProperty.ExactInverseImage

/-! # Original constructible coefficients with a positive annihilator

For a fixed actual raw compactification, prime-killed constructible inputs
suffice for all positively annihilated constructible inputs. The theorem
keeps this prime case explicit: it does not assert that a characteristic-p
ring theorem already supplies arbitrary prime-killed modules over Λ.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients

universe u wM wS
attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify
  CategoryTheory.TorsionZMod.Ringed.hasSheafifyRingStandard
  CategoryTheory.TorsionZMod.Ringed.hasSheafifyAbStandard
  CategoryTheory.TorsionZMod.Ringed.ringWEqualsLocallyBijectiveStandard
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

/-- Prime tests for the original constructible coefficients imply all original
compactified higher-image tests for a specified positive annihilator. -/
theorem moduleCompactificationHigherImage_isConstructible_of_prime_tests
    {X S : Scheme.{u}} {f : X ⟶ S} (C : Hom.Compactification f)
    (Λ : Type (u + 1)) [Ring Λ] [IsNoetherianRing Λ]
    [HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]
    [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
    (n : ℕ) (hn : 0 < n)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ n →
      ∀ E : ModuleValuedSheaf X Λ, Constructible.Modules.IsConstructible E →
        p • 𝟙 E = 0 → ∀ q : ℕ,
        Constructible.Modules.IsConstructible
          ((moduleSheafEquivalence S Λ).inverse.obj
            ((moduleCompactificationHigherDirectImage C Λ q).obj
              ((moduleSheafEquivalence X Λ).functor.obj E))))
    (E : ModuleValuedSheaf X Λ) (hE : Constructible.Modules.IsConstructible E)
    (hkill : n • 𝟙 E = 0) (q : ℕ) :
    Constructible.Modules.IsConstructible
      ((moduleSheafEquivalence S Λ).inverse.obj
        ((moduleCompactificationHigherDirectImage C Λ q).obj
          ((moduleSheafEquivalence X Λ).functor.obj E))) := by
  let : (moduleSheafEquivalence X Λ).functor.Additive :=
    ModuleCat.Sheaf.ConstantRing.moduleSheafEquivalence_functor_additive.{u + 1, u, u + 1, u + 1}
      X.smallEtaleTopology Λ
  let : (moduleSheafEquivalence S Λ).inverse.Additive :=
    ModuleCat.Sheaf.ConstantRing.moduleSheafEquivalence_inverse_additive.{u + 1, u, u + 1, u + 1}
      S.smallEtaleTopology Λ
  let K := (moduleSheafEquivalence X Λ).functor ⋙ moduleLowerShriek C.j Λ
  let P : ObjectProperty (ModuleSheaf S Λ) := ObjectProperty.inverseImage
    (Constructible.Modules.IsConstructible : ObjectProperty (ModuleValuedSheaf S Λ))
    (moduleSheafEquivalence S Λ).inverse
  exact ObjectProperty.rightDerived_property_of_positive_annihilator
    (Constructible.Modules.IsConstructible : ObjectProperty (ModuleValuedSheaf X Λ))
    (fun {_ _} a hA hB => Constructible.Modules.isConstructible_kernel a hA hB)
    (fun {_ _} a hA hB => Constructible.Modules.isConstructible_cokernel a hA hB)
    K (moduleDirectImage C.p Λ) P n hn hprime E hE hkill q

end AlgebraicGeometry.Scheme.EtaleCohomology
