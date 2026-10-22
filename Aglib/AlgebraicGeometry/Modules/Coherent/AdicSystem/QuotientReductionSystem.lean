/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Coherent.AdicSystem.QuotientSystem
public import Aglib.AlgebraicGeometry.Modules.Coherent.AdicSystem.QuotientFactorization

/-! # Original nested quotient reductions as maps of formal systems -/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules.Coherent

universe u

variable (X : Scheme.{u}) (K : X.IdealSheafData)

/-- Inclusions of ideal sheaves give the original natural quotient map. -/
def idealSheafQuotientMapNatTrans {J : X.IdealSheafData} (h : K ≤ J) :
    idealSheafQuotientFunctor X K ⟶ idealSheafQuotientFunctor X J where
  app F := idealSheafQuotientMap X K h F
  naturality _ _ f := idealSheafQuotientMap_naturality X K h f

/-- The original nested reduction isomorphism is natural in coefficients. -/
def idealSheafQuotientReductionNatIso {J : X.IdealSheafData} (h : K ≤ J) :
    idealSheafQuotientFunctor X K ⋙ idealSheafQuotientFunctor X J ≅
      idealSheafQuotientFunctor X J :=
  NatIso.ofComponents (idealSheafQuotientReductionIso X K h)
    (fun f => (diagramQuotientDesc X J (idealSheafQuotientMapNatTrans X K h)
      (fun F => (idealSheafQuotientReductionIso X K h F).hom)
      (idealSheafQuotientUnit_reductionIso_hom X K h)).naturality f)

namespace AdicSystem

variable (I : X.IdealSheafData) [IsLocallyNoetherian X]

/-- Nested quotients retain their original comparison in the formal category. -/
def quotientReductionIso {J : X.IdealSheafData} (h : K ≤ J) (F : AdicSystem X I) :
    quotient X I J (quotient X I K F) ≅ quotient X I J F :=
  ObjectProperty.isoMk _ (Functor.isoWhiskerLeft F.obj
    (idealSheafQuotientReductionNatIso X K h))

@[reassoc (attr := simp)]
theorem quotientUnit_reductionIso_hom {J : X.IdealSheafData} (h : K ≤ J)
    (F : AdicSystem X I) :
    quotientUnit X I J (quotient X I K F) ≫ (quotientReductionIso X K I h F).hom =
      quotientMap X I K h F := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext n
  exact idealSheafQuotientUnit_reductionIso_hom X K h (F.obj.obj n)

/-- The original independent-power quotient maps form one coherent diagram
of formal systems, rather than unrelated choices of objects. -/
def quotientTower (F : AdicSystem X I) : ℕᵒᵖ ⥤ AdicSystem X I where
  obj n := quotient X I (K ^ n.unop) F
  map g := quotientMap X I (K ^ _) (idealSheaf_pow_le X K (leOfHom g.unop)) F
  map_id n := by
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext m
    exact idealSheafQuotientMap_refl X (K ^ n.unop) (F.obj.obj m)
  map_comp g h := by
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext m
    exact (idealSheafQuotientMap_comp X _
      (idealSheaf_pow_le X K (leOfHom g.unop))
      (idealSheaf_pow_le X K (leOfHom h.unop)) (F.obj.obj m)).symm

end AdicSystem

end AlgebraicGeometry.Scheme.Modules.Coherent
