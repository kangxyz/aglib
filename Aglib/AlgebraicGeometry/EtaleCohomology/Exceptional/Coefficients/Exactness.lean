/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.Underlying
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-!
# Exact native constant-ring inverse image

Finite limits are detected by the original additive sheaf functor. The
proved underlying comparison transfers the original étale inverse image's
left exactness to the native ringed pullback. Injective preservation then
follows from the actual ringed adjunction, not from coefficient forgetting.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

universe u

attribute [local instance] hasSheafifyLarge
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

variable {X S : Scheme.{u}} (f : S ⟶ X) (Λ : Type (u + 1)) [Ring Λ]

instance moduleInverseImage_isLeftAdjoint : (moduleInverseImage f Λ).IsLeftAdjoint :=
  (moduleInverseImageAdjunction f Λ).isLeftAdjoint

instance moduleInverseImage_preservesFiniteLimits :
    PreservesFiniteLimits (moduleInverseImage f Λ) := by
  let : PreservesFiniteLimits
      (moduleInverseImage f Λ ⋙ SheafOfModules.toSheaf (constantRing S Λ)) :=
    preservesFiniteLimits_of_natIso (moduleInverseImageUnderlyingIso Λ f).symm
  exact preservesFiniteLimits_of_reflects_of_preserves
    (moduleInverseImage f Λ) (SheafOfModules.toSheaf (constantRing S Λ))

instance moduleInverseImage_preservesColimits :
    PreservesColimits (moduleInverseImage f Λ) := by infer_instance

instance moduleInverseImage_additive : (moduleInverseImage f Λ).Additive :=
  Functor.additive_of_preserves_binary_products _

instance moduleDirectImage_additive : (moduleDirectImage f Λ).Additive :=
  (moduleInverseImageAdjunction f Λ).right_adjoint_additive

instance moduleInverseImage_preservesHomology :
    (moduleInverseImage f Λ).PreservesHomology := by infer_instance

/-- The actual ringed inverse image preserves short exact sequences. -/
theorem shortExact_moduleInverseImage {T : ShortComplex (ModuleSheaf X Λ)}
    (hT : T.ShortExact) : (T.map (moduleInverseImage f Λ)).ShortExact :=
  hT.map_of_exact (moduleInverseImage f Λ)

/-- The original ringed direct image preserves injective objects. -/
instance moduleDirectImage_preservesInjectiveObjects :
    (moduleDirectImage f Λ).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (moduleInverseImageAdjunction f Λ)

end AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
