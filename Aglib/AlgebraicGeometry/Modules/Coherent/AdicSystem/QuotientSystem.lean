/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Coherent.AdicSystem.QuotientInterchange
public import Aglib.AlgebraicGeometry.Modules.Coherent.AdicSystem.Completion

/-! # Termwise independent quotients of the original coherent adic systems -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules.Coherent

universe u

variable (X : Scheme.{u}) (I K : X.IdealSheafData) [IsLocallyNoetherian X]

namespace AdicSystem

/-- Termwise quotient by any independent ideal remains an adic system for
the original ideal, with the original mapped transitions, including index zero. -/
theorem quotient_isAdicSystem (F : AdicSystem X I) :
    IsAdicSystem X I (F.obj ⋙ idealSheafQuotientFunctor X K) where
  coherent n := idealSheafQuotient_coherent X K (F.property.coherent n)
  annihilated n := idealSheafQuotient_killed_of_killed X (I ^ n) K
    (F.property.annihilated n)
  reduction n := by
    refine ⟨idealSheafQuotientInterchangeIso X K (I ^ n) (F.obj.obj (op (n + 1))) ≪≫
      (idealSheafQuotientFunctor X K).mapIso (F.reductionIso n), ?_⟩
    apply (cancel_epi ((idealSheafQuotientUnit X K).app
      (F.obj.obj (op (n + 1))))).mp
    dsimp only [Iso.trans_hom, Functor.mapIso_hom, Functor.comp_map,
      Functor.comp_obj, Functor.id_obj]
    erw [idealSheafQuotientUnit_interchangeIso_hom_assoc]
    erw [← (idealSheafQuotientUnit X K).naturality (F.reductionIso n).hom]
    simp only [Functor.id_map, unit_reductionIso_hom_assoc]
    exact (idealSheafQuotientUnit X K).naturality (F.transition n)

/-- The actual termwise quotient, not a replacement formal-system model. -/
def quotient (F : AdicSystem X I) : AdicSystem X I :=
  ⟨F.obj ⋙ idealSheafQuotientFunctor X K, quotient_isAdicSystem X I K F⟩

@[simp]
theorem quotient_obj (F : AdicSystem X I) (n : ℕ) :
    (quotient X I K F).obj.obj (op n) =
      (idealSheafQuotientFunctor X K).obj (F.obj.obj (op n)) := rfl

@[simp]
theorem quotient_transition (F : AdicSystem X I) (n : ℕ) :
    (quotient X I K F).transition n =
      (idealSheafQuotientFunctor X K).map (F.transition n) := rfl

/-- Each quotient stage retains annihilation by the independent ideal. -/
theorem quotient_killed (F : AdicSystem X I) (n : ℕ) :
    killedByIdealSheaf K ((quotient X I K F).obj.obj (op n)) :=
  idealSheafQuotient_killed X K _

/-- The quotient's zero stage is zero by the original adic condition. -/
theorem quotient_zero_isZero (F : AdicSystem X I) :
    IsZero ((quotient X I K F).obj.obj (op 0)) :=
  (quotient X I K F).zero_isZero

/-- Original coefficient natural transformations induce actual quotient maps. -/
def quotientFunctor : AdicSystem X I ⥤ AdicSystem X I where
  obj := quotient X I K
  map f := ObjectProperty.homMk (Functor.whiskerRight f.hom (idealSheafQuotientFunctor X K))
  map_id F := by
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext n
    exact (idealSheafQuotientFunctor X K).map_id _
  map_comp f g := by
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext n
    exact (idealSheafQuotientFunctor X K).map_comp _ _

/-- The original stage quotient units form a map of original formal systems. -/
def quotientUnit (F : AdicSystem X I) : F ⟶ quotient X I K F :=
  ObjectProperty.homMk (Functor.whiskerLeft F.obj (idealSheafQuotientUnit X K))

/-- Inclusions of independent ideals give the original stage reduction maps. -/
def quotientMap {L : X.IdealSheafData} (h : K ≤ L) (F : AdicSystem X I) :
    quotient X I K F ⟶ quotient X I L F :=
  ObjectProperty.homMk {
    app n := idealSheafQuotientMap X K h (F.obj.obj n)
    naturality _ _ f := idealSheafQuotientMap_naturality X K h (F.obj.map f) }

@[reassoc (attr := simp)]
theorem quotientUnit_map {L : X.IdealSheafData} (h : K ≤ L) (F : AdicSystem X I) :
    quotientUnit X I K F ≫ quotientMap X I K h F = quotientUnit X I L F := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext n
  exact idealSheafQuotientUnit_map X K h (F.obj.obj n)

end AdicSystem

end AlgebraicGeometry.Scheme.Modules.Coherent
