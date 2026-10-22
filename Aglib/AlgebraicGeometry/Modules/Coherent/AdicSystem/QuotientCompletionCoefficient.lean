/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Coherent.AdicSystem.QuotientCompletionNaturality

/-! # Original coefficient maps in independent quotient completion -/

@[expose] public noncomputable section
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme.Modules.Coherent
universe u
variable (X : Scheme.{u}) (I K : X.IdealSheafData) [IsLocallyNoetherian X]

/-- Quotient of the original coherent coefficient morphism. -/
def idealSheafCoherentQuotientHom {G H : X.CoherentSheaf} (a : G ⟶ H) :
    idealSheafCoherentQuotient X K G ⟶ idealSheafCoherentQuotient X K H :=
  ObjectProperty.homMk ((idealSheafQuotientFunctor X K).map a.hom)

/-- Original completion interchange retains original coherent coefficient maps. -/
@[reassoc]
theorem idealSheafQuotientCompletionIso_coefficient_naturality
    {G H : X.CoherentSheaf} (a : G ⟶ H) :
    (completionFunctor X I).map (idealSheafCoherentQuotientHom X K a) ≫
        (idealSheafQuotientCompletionIso X I K H).hom =
      (idealSheafQuotientCompletionIso X I K G).hom ≫
        (AdicSystem.quotientFunctor X I K).map ((completionFunctor X I).map a) := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext n
  exact idealSheafQuotientInterchangeIso_naturality X K (I ^ n.unop) a.hom

namespace AdicSystem

/-- The original independent ideal-inclusion maps are natural in formal coefficients. -/
@[reassoc]
theorem quotientMap_naturality {L : X.IdealSheafData} (h : K ≤ L)
    {F G : AdicSystem X I} (φ : F ⟶ G) :
    (quotientFunctor X I K).map φ ≫ quotientMap X I K h G =
      quotientMap X I K h F ≫ (quotientFunctor X I L).map φ := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext n
  exact idealSheafQuotientMap_naturality X K h (φ.hom.app n)

end AdicSystem
end AlgebraicGeometry.Scheme.Modules.Coherent
