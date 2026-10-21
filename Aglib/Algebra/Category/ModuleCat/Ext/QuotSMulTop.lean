/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Ext.Cokernel
public import Aglib.RingTheory.QuotSMulTop.Hom
public import Mathlib.Algebra.Category.ModuleCat.Ext.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.RingTheory.Regular.Free
public import Mathlib.RingTheory.Regular.IsSMulRegular

/-!
# Degree-one Ext after quotienting by a module-regular scalar

An actual short exact presentation with free middle remains short exact modulo
a scalar regular on its last object. The quotient Hom universal property
identifies its restriction cokernel, giving the degree-one change-of-rings
comparison. No bound on the projective dimension of the last object is assumed.
-/

@[expose] public section

noncomputable section

universe u w

open CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra

namespace ModuleCat

variable {R : Type u} [CommRing R] (a : R)

/-- The actual quotient of a linear map, over the quotient ring. -/
def quotSMulTopMap {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    ModuleCat.of (R ⧸ Ideal.span {a}) (QuotSMulTop a M) ⟶
      ModuleCat.of (R ⧸ Ideal.span {a}) (QuotSMulTop a N) :=
  ModuleCat.ofHom ((QuotSMulTop.map a f.hom).extendScalarsOfSurjective
    (S := R ⧸ Ideal.span {a}) Ideal.Quotient.mk_surjective)

/-- The actual scalar-quotient short complex. -/
def quotSMulTopShortComplex (S : ShortComplex (ModuleCat.{u} R)) :
    ShortComplex (ModuleCat.{u} (R ⧸ Ideal.span {a})) :=
  ShortComplex.mk (quotSMulTopMap a S.f) (quotSMulTopMap a S.g) (by
    apply ModuleCat.hom_ext
    apply LinearMap.restrictScalars_injective R
    change (QuotSMulTop.map a S.g.hom).comp (QuotSMulTop.map a S.f.hom) = 0
    rw [← QuotSMulTop.map_comp]
    have hz : S.g.hom.comp S.f.hom = 0 := congrArg ModuleCat.Hom.hom S.zero
    rw [hz, map_zero])

/-- Regularity on the last object preserves left exactness of the quotient. -/
theorem quotSMulTopShortComplex_shortExact {S : ShortComplex (ModuleCat.{u} R)}
    (hS : S.ShortExact) (ha : IsSMulRegular S.X₃ a) :
    (quotSMulTopShortComplex a S).ShortExact := by
  have hex : Function.Exact S.f.hom S.g.hom := by
    rw [LinearMap.exact_iff]
    exact hS.exact.moduleCat_range_eq_ker.symm
  have hz : Function.Exact (0 : S.X₁ →ₗ[R] S.X₁) S.f.hom :=
    (LinearMap.exact_zero_iff_injective S.X₁ S.f.hom).mpr hS.moduleCat_injective_f
  have hq := QuotSMulTop.map_first_exact_on_four_term_exact_of_isSMulRegular_last hz hex ha
  have hi : Function.Injective (QuotSMulTop.map a S.f.hom) := by
    rw [map_zero, LinearMap.exact_zero_iff_injective] at hq
    exact hq
  exact ModuleCat.shortComplex_shortExact _
    (QuotSMulTop.map_exact a hex hS.moduleCat_surjective_g) hi
    (QuotSMulTop.map_surjective a hS.moduleCat_surjective_g)

/-- Hom over the quotient ring, expressed using the original coefficient maps. -/
def homQuotSMulTopLinearEquiv (M : ModuleCat.{u} R) :
    (ModuleCat.of (R ⧸ Ideal.span {a}) (QuotSMulTop a M) ⟶
      ModuleCat.of (R ⧸ Ideal.span {a}) (R ⧸ Ideal.span {a})) ≃ₗ[R]
      (M ⟶ ModuleCat.of R (R ⧸ Ideal.span {a})) :=
  (ModuleCat.homLinearEquiv (S := R)
    (M := ModuleCat.of (R ⧸ Ideal.span {a}) (QuotSMulTop a M))
    (N := ModuleCat.of (R ⧸ Ideal.span {a}) (R ⧸ Ideal.span {a}))).trans
    ((QuotSMulTop.homLinearEquiv a M (R ⧸ Ideal.span {a})).trans
      (ModuleCat.homLinearEquiv (S := R) (M := M)
        (N := ModuleCat.of R (R ⧸ Ideal.span {a}))).symm)

/-- The original restriction map commutes with quotient Hom factorization. -/
theorem homQuotSMulTopLinearEquiv_comp {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    (homQuotSMulTopLinearEquiv a M).toLinearMap.comp
        (Linear.leftComp R (ModuleCat.of (R ⧸ Ideal.span {a})
          (R ⧸ Ideal.span {a})) (quotSMulTopMap a f)) =
      (Linear.leftComp R (ModuleCat.of R (R ⧸ Ideal.span {a})) f).comp
        (homQuotSMulTopLinearEquiv a N).toLinearMap := by
  apply DFunLike.ext
  intro φ
  apply ModuleCat.hom_ext
  apply DFunLike.ext
  intro m
  rfl

/-- The quotient and original Hom restriction cokernels agree linearly. -/
def homCokernelQuotSMulTopLinearEquiv (S : ShortComplex (ModuleCat.{u} R)) :
    (((quotSMulTopShortComplex a S).X₁ ⟶ ModuleCat.of (R ⧸ Ideal.span {a})
        (R ⧸ Ideal.span {a})) ⧸ LinearMap.range (Linear.leftComp R
        (ModuleCat.of (R ⧸ Ideal.span {a}) (R ⧸ Ideal.span {a}))
        (quotSMulTopShortComplex a S).f)) ≃ₗ[R]
      ((S.X₁ ⟶ ModuleCat.of R (R ⧸ Ideal.span {a})) ⧸
        LinearMap.range (Linear.leftComp R (ModuleCat.of R (R ⧸ Ideal.span {a})) S.f)) :=
  Submodule.Quotient.equiv _ _ (homQuotSMulTopLinearEquiv a S.X₁) (by
    rw [← LinearMap.range_comp]
    exact (congrArg LinearMap.range (homQuotSMulTopLinearEquiv_comp a S.f)).trans
      (LinearMap.range_comp_of_range_eq_top _ (homQuotSMulTopLinearEquiv a S.X₂).range))

variable [HasExt.{w} (ModuleCat.{u} R)]
    [HasExt.{w} (ModuleCat.{u} (R ⧸ Ideal.span {a}))]

/-- Degree-one change of rings along an actual free-middle presentation.
The original last object need not have projective dimension at most one. -/
def extOneQuotSMulTopLinearEquiv {S : ShortComplex (ModuleCat.{u} R)}
    (hS : S.ShortExact) [Module.Free R S.X₂] (ha : IsSMulRegular S.X₃ a) :
    Ext.{w} S.X₃ (ModuleCat.of R (R ⧸ Ideal.span {a})) 1 ≃ₗ[R]
      Ext.{w} (ModuleCat.of (R ⧸ Ideal.span {a}) (QuotSMulTop a S.X₃))
        (ModuleCat.of (R ⧸ Ideal.span {a}) (R ⧸ Ideal.span {a})) 1 := by
  have : Module.Free (R ⧸ Ideal.span {a}) (quotSMulTopShortComplex a S).X₂ :=
    inferInstanceAs (Module.Free (R ⧸ Ideal.span {a}) (QuotSMulTop a S.X₂))
  have : Projective (quotSMulTopShortComplex a S).X₂ :=
    ModuleCat.projective_of_categoryTheory_projective (quotSMulTopShortComplex a S).X₂
  exact (hS.homCokernelExtOneLinearEquiv (R := R)
    (ModuleCat.of R (R ⧸ Ideal.span {a}))).symm.trans
    ((homCokernelQuotSMulTopLinearEquiv a S).symm.trans
      ((quotSMulTopShortComplex_shortExact a hS ha).homCokernelExtOneLinearEquiv
        (R := R) (ModuleCat.of (R ⧸ Ideal.span {a}) (R ⧸ Ideal.span {a}))))

end ModuleCat
