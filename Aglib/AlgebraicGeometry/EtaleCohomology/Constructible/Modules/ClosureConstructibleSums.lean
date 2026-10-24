/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.ClosurePartitions
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.ClosureSums

/-! # Finite sums of genuinely constructible module coefficients

The proof uses the original affine opens, native common finite partitions,
and exact original module inverse images. No Noetherian hypothesis is needed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

universe u r

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify
attribute [local instance] Abelian.hasFiniteBiproducts

variable {R : Type r} [CommRing R]

local instance closureConstructibleSumsHasModuleLimits :
    HasLimitsOfSize.{u + 1, u + 1} (ModuleCat.{u + 1} R) :=
  ModuleCat.hasLimitsOfSize.{u + 1, u + 1, u + 1, r}

/-- Binary products are constructible on the native common affine-local strata. -/
theorem isConstructible_prod {X : Scheme.{u}} {F G : ModuleSheaf R X}
    (hF : IsConstructible F) (hG : IsConstructible G) : IsConstructible (F ⨯ G) := by
  intro U
  obtain ⟨p, hpF, hpG⟩ := exists_common_partition_pair (hF U) (hG U)
  refine ⟨{ toFiniteLocallyClosedPartition := p, locally_constant := ?_ }⟩
  intro i
  let P := moduleInverseImage R U.1.ι ⋙ moduleInverseImage R (p.inclusion i)
  exact (isFiniteTypeLocallyConstant_iff_of_iso (PreservesLimitPair.iso P F G)).mpr
    (isFiniteTypeLocallyConstant_prod (hpF i) (hpG i))

/-- The original binary biproduct of constructible module coefficients is constructible. -/
theorem isConstructible_biprod {X : Scheme.{u}} {F G : ModuleSheaf R X}
    (hF : IsConstructible F) (hG : IsConstructible G) : IsConstructible (F ⊞ G) :=
  (isConstructible_iff_of_iso (biprod.isoProd F G)).mpr (isConstructible_prod hF hG)

/-- The original zero module coefficient is constructible. -/
theorem isConstructible_zero (X : Scheme.{u}) : IsConstructible (0 : ModuleSheaf R X) :=
  isConstructible_of_isFiniteTypeLocallyConstant (isFiniteTypeLocallyConstant_zero X)

/-- Constructibility as a native object property respects coefficient isomorphisms. -/
instance isConstructible_isoClosed (X : Scheme.{u}) :
    ObjectProperty.IsClosedUnderIsomorphisms (IsConstructible (R := R) (X := X)) where
  of_iso e h := (isConstructible_iff_of_iso e).mp h

/-- The constructible property contains the actual zero object. -/
instance isConstructible_containsZero (X : Scheme.{u}) :
    ObjectProperty.ContainsZero (IsConstructible (R := R) (X := X)) where
  exists_zero := ⟨0, isZero_zero _, isConstructible_zero X⟩

/-- Native binary-product closure uses actual common geometric partitions. -/
instance isConstructible_closedUnderBinaryProducts (X : Scheme.{u}) :
    ObjectProperty.IsClosedUnderBinaryProducts (IsConstructible (R := R) (X := X)) :=
  ObjectProperty.IsClosedUnderLimitsOfShape.mk' (by
    rintro _ ⟨F, hF⟩
    exact (isConstructible_iff_of_iso
      (HasLimit.isoOfNatIso (diagramIsoPair F))).mpr
      (isConstructible_prod (hF _) (hF _)))

/-- All finite products preserve module constructibility. -/
instance isConstructible_closedUnderFiniteProducts (X : Scheme.{u}) :
    ObjectProperty.IsClosedUnderFiniteProducts (IsConstructible (R := R) (X := X)) :=
  ObjectProperty.IsClosedUnderFiniteProducts.mk'

/-- Finite products of constructible modules in every available index universe. -/
theorem isConstructible_product {X : Scheme.{u}} {ι : Type*} [Finite ι]
    (F : ι → ModuleSheaf R X) (hF : ∀ i, IsConstructible (F i)) [HasProduct F] :
    IsConstructible (∏ᶜ F) := ObjectProperty.prop_product _ hF

/-- Finite sums use the original categorical module-sheaf biproduct. -/
theorem isConstructible_biproduct {X : Scheme.{u}} {ι : Type*} [Finite ι]
    (F : ι → ModuleSheaf R X) (hF : ∀ i, IsConstructible (F i)) [HasBiproduct F] :
    IsConstructible (⨁ F) := ObjectProperty.prop_of_isLimit_fan _ (biproduct.isLimit F) hF

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules
