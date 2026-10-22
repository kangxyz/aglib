/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.TwoIdeal.ReconstructionStages

/-! # Whole original coefficient diagrams in two-ideal recovery -/

@[expose] public noncomputable section
open CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Coherent
namespace AlgebraicGeometry.Scheme.Cohomology
universe u
variable {A : Type u} [CommRing A] [IsNoetherianRing A]
  (I : Ideal A) [IsAdicComplete I A] {X : Scheme.{u}} [IsLocallyNoetherian X]
  (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f] (K : X.IdealSheafData)
  (h : ClosedThickeningCompletionEssSurj f I K)
  (F : AdicSystem X (idealThickeningIdealSheaf f I))
local notation "J" => idealThickeningIdealSheaf f I
local notation "C" => completionFunctor X K

/-- Original coherent formal coefficients with all original transitions. -/
def originalStageCoherentDiagram : ℕᵒᵖ ⥤ X.CoherentSheaf where
  obj n := originalStageCoherent I f F n.unop
  map g := ObjectProperty.homMk (F.obj.map g)
  map_id n := by apply ObjectProperty.hom_ext; exact F.obj.map_id n
  map_comp g k := by apply ObjectProperty.hom_ext; exact F.obj.map_comp g k

/-- The original stage maps into the actual algebraic quotient tower. -/
def originalStageCoherentDiagramMap {H : X.CoherentSheaf}
    (φ : F ⟶ (completionFunctor X J).obj H) :
    originalStageCoherentDiagram I f F ⟶ idealSheafCoherentQuotientTower X J H where
  app n := originalStageCoherentMap I f F φ n.unop
  naturality {_m _n} g := by apply ObjectProperty.hom_ext; exact φ.hom.naturality g

/-- Original algebraic quotient maps form a whole compatible target map. -/
def coherentQuotientTowerHom (L : X.IdealSheafData) {G H : X.CoherentSheaf} (a : G ⟶ H) :
    idealSheafCoherentQuotientTower X L G ⟶ idealSheafCoherentQuotientTower X L H where
  app n := idealSheafCoherentQuotientHom X (L ^ n.unop) a
  naturality {m _n} g := by
    apply ObjectProperty.hom_ext
    exact (idealSheafQuotientMap_naturality X (L ^ m.unop)
      (idealSheaf_pow_le X L (leOfHom g.unop)) a.hom).symm

/-- The original stage comparison is natural for every I-index arrow. -/
theorem twoIdealOriginalStageIso_naturality {m n : ℕᵒᵖ} (g : m ⟶ n) :
    AdicSystem.quotientMap X K (J ^ m.unop)
        (idealSheaf_pow_le X J (leOfHom g.unop)) (twoIdealCoefficientSystem I f K h F) ≫
      (twoIdealOriginalStageIso I f K h F n.unop).hom =
    (twoIdealOriginalStageIso I f K h F m.unop).hom ≫
      (C).map ((originalStageCoherentDiagram I f F).map g) := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext e
  exact ((twoIdealCoefficientCompletionIso I f K h F).app e).hom.hom.naturality g

/-- All specified reconstructed-stage comparisons retain all original index arrows. -/
theorem twoIdealReconstructionStageIso_naturality {G : X.CoherentSheaf}
    (β : (C).obj G ≅ twoIdealCoefficientSystem I f K h F) {m n : ℕᵒᵖ} (g : m ⟶ n) :
    (C).map ((idealSheafCoherentQuotientTower X J G).map g) ≫
      (twoIdealReconstructionStageIso I f K h F β n.unop).hom =
    (twoIdealReconstructionStageIso I f K h F β m.unop).hom ≫
      (C).map ((originalStageCoherentDiagram I f F).map g) := by
  let q := idealSheaf_pow_le X J (leOfHom g.unop)
  have h₁ : CommSq
      ((C).map ((idealSheafCoherentQuotientTower X J G).map g))
      (idealSheafQuotientCompletionIso X K (J ^ m.unop) G).hom
      (idealSheafQuotientCompletionIso X K (J ^ n.unop) G).hom
      (AdicSystem.quotientMap X K (J ^ m.unop) q ((C).obj G)) :=
    ⟨idealSheafQuotientCompletionIso_ideal_naturality X K (J ^ m.unop) q G⟩
  have h₂ : CommSq
      (AdicSystem.quotientMap X K (J ^ m.unop) q ((C).obj G))
      ((AdicSystem.quotientFunctor X K (J ^ m.unop)).map β.hom)
      ((AdicSystem.quotientFunctor X K (J ^ n.unop)).map β.hom)
      (AdicSystem.quotientMap X K (J ^ m.unop) q (twoIdealCoefficientSystem I f K h F)) :=
    ⟨(AdicSystem.quotientMap_naturality X K (J ^ m.unop) q β.hom).symm⟩
  have h₃ : CommSq
      (AdicSystem.quotientMap X K (J ^ m.unop) q (twoIdealCoefficientSystem I f K h F))
      (twoIdealOriginalStageIso I f K h F m.unop).hom
      (twoIdealOriginalStageIso I f K h F n.unop).hom
      ((C).map ((originalStageCoherentDiagram I f F).map g)) :=
    ⟨twoIdealOriginalStageIso_naturality I f K h F g⟩
  exact (h₁.vert_comp (h₂.vert_comp h₃)).w

end AlgebraicGeometry.Scheme.Cohomology
