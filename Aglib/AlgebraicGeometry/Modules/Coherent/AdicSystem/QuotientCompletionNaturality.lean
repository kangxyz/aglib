/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Coherent.AdicSystem.QuotientCompletionUnit
public import Aglib.AlgebraicGeometry.Modules.Coherent.AdicSystem.QuotientInterchangeNaturality
public import Aglib.AlgebraicGeometry.Modules.Coherent.AdicSystem.QuotientReductionSystem

/-! # Whole-tower naturality of independent quotients and original completion -/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules.Coherent

universe u

variable (X : Scheme.{u}) (I K : X.IdealSheafData) [IsLocallyNoetherian X]

/-- Original independent quotient maps as coherent coefficient morphisms. -/
def idealSheafCoherentQuotientMap {L : X.IdealSheafData} (h : K ≤ L)
    (F : X.CoherentSheaf) :
    idealSheafCoherentQuotient X K F ⟶ idealSheafCoherentQuotient X L F :=
  ObjectProperty.homMk (idealSheafQuotientMap X K h F.obj)

/-- Completion interchange retains the original ideal-inclusion maps. -/
@[reassoc]
theorem idealSheafQuotientCompletionIso_ideal_naturality
    {L : X.IdealSheafData} (h : K ≤ L) (F : X.CoherentSheaf) :
    (completionFunctor X I).map (idealSheafCoherentQuotientMap X K h F) ≫
        (idealSheafQuotientCompletionIso X I L F).hom =
      (idealSheafQuotientCompletionIso X I K F).hom ≫
        AdicSystem.quotientMap X I K h ((completionFunctor X I).obj F) := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext n
  exact idealSheafQuotientInterchangeIso_ideal_naturality X K (I ^ n.unop) h F.obj

/-- The original independent-power quotient tower, retaining its coherent objects. -/
def idealSheafCoherentQuotientTower (F : X.CoherentSheaf) : ℕᵒᵖ ⥤ X.CoherentSheaf where
  obj n := idealSheafCoherentQuotient X (K ^ n.unop) F
  map g := idealSheafCoherentQuotientMap X (K ^ _)
    (idealSheaf_pow_le X K (leOfHom g.unop)) F
  map_id n := by
    apply ObjectProperty.hom_ext
    exact idealSheafQuotientMap_refl X (K ^ n.unop) F.obj
  map_comp g h := by
    apply ObjectProperty.hom_ext
    exact (idealSheafQuotientMap_comp X _
      (idealSheaf_pow_le X K (leOfHom g.unop))
      (idealSheaf_pow_le X K (leOfHom h.unop)) F.obj).symm

/-- The original coherent K-quotient tower completes to the original tower
of independent formal quotients, with every transition retained. -/
def idealSheafCoherentQuotientTowerCompletionIso (F : X.CoherentSheaf) :
    idealSheafCoherentQuotientTower X K F ⋙ completionFunctor X I ≅
      AdicSystem.quotientTower X K I ((completionFunctor X I).obj F) :=
  NatIso.ofComponents (fun n => idealSheafQuotientCompletionIso X I (K ^ n.unop) F)
    (fun {m _n} g => idealSheafQuotientCompletionIso_ideal_naturality X I (K ^ m.unop)
      (idealSheaf_pow_le X K (leOfHom g.unop)) F)

namespace AdicSystem

/-- A formal coefficient map acts on the entire original independent quotient
tower, naturally in its power index. -/
def quotientTowerHom {F G : AdicSystem X I} (φ : F ⟶ G) :
    quotientTower X K I F ⟶ quotientTower X K I G where
  app n := (quotientFunctor X I (K ^ n.unop)).map φ
  naturality {m n} g := by
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext k
    exact (idealSheafQuotientMap_naturality X (K ^ m.unop)
      (idealSheaf_pow_le X K (leOfHom g.unop)) (φ.hom.app k)).symm

end AdicSystem

end AlgebraicGeometry.Scheme.Modules.Coherent
