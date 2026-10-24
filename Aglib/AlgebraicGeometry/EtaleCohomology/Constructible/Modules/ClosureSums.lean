/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.LocallyConstant
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import Mathlib.RingTheory.Finiteness.Prod

/-! # Finite sums of finite-type locally constant module coefficients

Two original local trivializations admit a jointly surjective common refinement
by the actual fibre products of their etale charts. The values are finite
products of finite modules, without any finite-cardinality assumption on the
ring. Native product comparisons then give closure under all finite products
and biproducts. No Noetherian hypothesis is needed for these statements.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

universe u r

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify
attribute [local instance] Abelian.hasFiniteBiproducts

variable {R : Type r} [CommRing R]

local instance closureSumsHasModuleLimits : HasLimitsOfSize.{u + 1, u + 1} (ModuleCat.{u + 1} R) :=
  ModuleCat.hasLimitsOfSize.{u + 1, u + 1, u + 1, r}

/-- The actual fibre products of two trivializing covers trivialize their
binary product, with the product module as constant value. -/
def FiniteTypeLocalTrivialization.prod {X : Scheme.{u}} {F G : ModuleSheaf R X}
    (t : FiniteTypeLocalTrivialization F) (s : FiniteTypeLocalTrivialization G) :
    FiniteTypeLocalTrivialization (F ⨯ G) where
  index := t.index × s.index
  chart i := Scheme.Etale.mk
    (pullback.fst (t.chart i.1).hom (s.chart i.2).hom ≫ (t.chart i.1).hom)
  covers x := by
    obtain ⟨i, y, hy⟩ := t.covers x
    obtain ⟨j, z, hz⟩ := s.covers x
    obtain ⟨w, hw, _⟩ := Scheme.Pullback.exists_preimage_pullback y z (hy.trans hz.symm)
    refine ⟨(i, j), w, ?_⟩
    change (t.chart i).hom ((pullback.fst (t.chart i).hom (s.chart j).hom) w) = x
    rw [hw, hy]
  value i := ModuleCat.of R (t.value i.1 × s.value i.2)
  finite_value i := by
    let := t.finite_value i.1
    let := s.finite_value i.2
    exact Module.Finite.prod
  trivialization i := by
    let a := (t.chart i.1).hom
    let b := (s.chart i.2).hom
    let p := pullback.fst a b
    let q := pullback.snd a b
    let C : ModuleCat.{u + 1} R ⥤ ModuleSheaf R (Limits.pullback a b) :=
      constantSheaf (Limits.pullback a b).smallEtaleTopology (ModuleCat.{u + 1} R)
    let : PreservesFiniteLimits C :=
      Limits.comp_preservesFiniteLimits (Functor.const (Limits.pullback a b).Etaleᵒᵖ)
        (presheafToSheaf (Limits.pullback a b).smallEtaleTopology (ModuleCat.{u + 1} R))
    let eF : (moduleInverseImage R (p ≫ a)).obj F ≅ C.obj (t.value i.1) :=
      (moduleInverseImageComp R a p).app F ≪≫
        (moduleInverseImage R p).mapIso (t.trivialization i.1) ≪≫
        (moduleInverseImageConstantIso R p).app (t.value i.1)
    let eG : (moduleInverseImage R (p ≫ a)).obj G ≅ C.obj (s.value i.2) :=
      eqToIso (congrArg (fun f => (moduleInverseImage R f).obj G) pullback.condition) ≪≫
        (moduleInverseImageComp R b q).app G ≪≫
        (moduleInverseImage R q).mapIso (s.trivialization i.2) ≪≫
        (moduleInverseImageConstantIso R q).app (s.value i.2)
    exact PreservesLimitPair.iso (moduleInverseImage R (p ≫ a)) F G ≪≫
      Limits.prod.mapIso eF eG ≪≫
      (PreservesLimitPair.iso C (t.value i.1) (s.value i.2)).symm ≪≫
      C.mapIso (limit.isoLimitCone
        (ModuleCat.binaryProductLimitCone.{u + 1, r} (t.value i.1) (s.value i.2)))

/-- Binary products of finite-type locally constant coefficients remain so. -/
theorem isFiniteTypeLocallyConstant_prod {X : Scheme.{u}} {F G : ModuleSheaf R X}
    (hF : IsFiniteTypeLocallyConstant F) (hG : IsFiniteTypeLocallyConstant G) :
    IsFiniteTypeLocallyConstant (F ⨯ G) := by
  obtain ⟨t⟩ := hF
  obtain ⟨s⟩ := hG
  exact ⟨t.prod s⟩

/-- Binary sums are the original categorical biproduct, not a replacement
coefficient object. -/
theorem isFiniteTypeLocallyConstant_biprod {X : Scheme.{u}} {F G : ModuleSheaf R X}
    (hF : IsFiniteTypeLocallyConstant F) (hG : IsFiniteTypeLocallyConstant G) :
    IsFiniteTypeLocallyConstant (F ⊞ G) :=
  (isFiniteTypeLocallyConstant_iff_of_iso (biprod.isoProd F G)).mpr
    (isFiniteTypeLocallyConstant_prod hF hG)

/-- The original zero module sheaf has a finite-type constant trivialization. -/
theorem isFiniteTypeLocallyConstant_zero (X : Scheme.{u}) :
    IsFiniteTypeLocallyConstant (0 : ModuleSheaf R X) := by
  let C := constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)
  let M : ModuleCat.{u + 1} R := ModuleCat.of R (ULift.{u + 1} PUnit.{1})
  have hM : IsZero M := ModuleCat.isZero_of_subsingleton _
  have hC : IsZero (C.obj M) := C.map_isZero hM
  exact (isFiniteTypeLocallyConstant_iff_of_iso (hC.isoZero)).mp
    (isFiniteTypeLocallyConstant_constant X M)

/-- Finite-type local constancy, as an object property, respects isomorphisms. -/
instance isFiniteTypeLocallyConstant_isoClosed (X : Scheme.{u}) :
    ObjectProperty.IsClosedUnderIsomorphisms
      (IsFiniteTypeLocallyConstant (R := R) (X := X)) where
  of_iso e h := (isFiniteTypeLocallyConstant_iff_of_iso e).mp h

/-- The property contains the actual zero coefficient. -/
instance isFiniteTypeLocallyConstant_containsZero (X : Scheme.{u}) :
    ObjectProperty.ContainsZero
      (IsFiniteTypeLocallyConstant (R := R) (X := X)) where
  exists_zero := ⟨0, isZero_zero _, isFiniteTypeLocallyConstant_zero X⟩

/-- Binary-product closure is proved by the actual common chart refinement. -/
instance isFiniteTypeLocallyConstant_closedUnderBinaryProducts (X : Scheme.{u}) :
    ObjectProperty.IsClosedUnderBinaryProducts
      (IsFiniteTypeLocallyConstant (R := R) (X := X)) :=
  ObjectProperty.IsClosedUnderLimitsOfShape.mk' (by
    rintro _ ⟨F, hF⟩
    exact (isFiniteTypeLocallyConstant_iff_of_iso
      (HasLimit.isoOfNatIso (diagramIsoPair F))).mpr
      (isFiniteTypeLocallyConstant_prod (hF _) (hF _)))

/-- All finite products preserve finite-type local constancy. -/
instance isFiniteTypeLocallyConstant_closedUnderFiniteProducts (X : Scheme.{u}) :
    ObjectProperty.IsClosedUnderFiniteProducts
      (IsFiniteTypeLocallyConstant (R := R) (X := X)) :=
  ObjectProperty.IsClosedUnderFiniteProducts.mk'

/-- A finite family of finite-type local systems has finite-type locally
constant categorical product, in every index universe. -/
theorem isFiniteTypeLocallyConstant_product {X : Scheme.{u}} {ι : Type*} [Finite ι]
    (F : ι → ModuleSheaf R X) (hF : ∀ i, IsFiniteTypeLocallyConstant (F i))
    [HasProduct F] : IsFiniteTypeLocallyConstant (∏ᶜ F) :=
  ObjectProperty.prop_product _ hF

/-- Finite sums of finite-type local systems are finite-type locally constant. -/
theorem isFiniteTypeLocallyConstant_biproduct {X : Scheme.{u}} {ι : Type*} [Finite ι]
    (F : ι → ModuleSheaf R X) (hF : ∀ i, IsFiniteTypeLocallyConstant (F i))
    [HasBiproduct F] : IsFiniteTypeLocallyConstant (⨁ F) :=
  ObjectProperty.prop_of_isLimit_fan _ (biproduct.isLimit F) hF

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules
