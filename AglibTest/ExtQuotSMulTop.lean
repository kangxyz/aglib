module

import Aglib.Algebra.Category.ModuleCat.Ext.QuotSMulTop

noncomputable section

universe u w

open CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra

example {R : Type u} [CommRing R] (a : R)
    [HasExt.{w} (ModuleCat.{u} R)]
    [HasExt.{w} (ModuleCat.{u} (R ⧸ Ideal.span {a}))]
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    [Module.Free R S.X₂] (ha : IsSMulRegular S.X₃ a) :
    Ext.{w} S.X₃ (ModuleCat.of R (R ⧸ Ideal.span {a})) 1 ≃ₗ[R]
      Ext.{w} (ModuleCat.of (R ⧸ Ideal.span {a}) (QuotSMulTop a S.X₃))
        (ModuleCat.of (R ⧸ Ideal.span {a}) (R ⧸ Ideal.span {a})) 1 :=
  ModuleCat.extOneQuotSMulTopLinearEquiv a hS ha

example {R : Type u} [CommRing R] (a : R)
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    (ha : IsSMulRegular S.X₃ a) :
    (ModuleCat.quotSMulTopShortComplex a S).ShortExact :=
  ModuleCat.quotSMulTopShortComplex_shortExact a hS ha
