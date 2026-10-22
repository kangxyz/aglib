/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.TwoIdeal.QuotientEffectivity
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.ClosedImmersionReduction.Annihilation
public import Aglib.AlgebraicGeometry.Modules.Coherent.AdicSystem.QuotientReductionSystem

/-! # Coherent algebraizations of independent quotients as one original diagram

Only one coefficient is selected at each order. All transition maps are lifted
from the original formal quotient tower by proper completion full faithfulness,
so identities, compositions and the completion comparison remain coherent.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Coherent

namespace AlgebraicGeometry.Scheme.Cohomology

universe u

/-- Lift a diagram through a fully faithful functor using actual essential-image witnesses. -/
def liftEssImageDiagram {C D J : Type*} [Category C] [Category D] [Category J]
    (T : C ⥤ D) (ff : T.FullyFaithful) (P : J ⥤ D)
    (h : ∀ j, T.essImage (P.obj j)) : J ⥤ C where
  obj j := (h j).witness
  map {j k} f := ff.preimage ((h j).getIso.hom ≫ P.map f ≫ (h k).getIso.inv)
  map_id j := by
    apply ff.map_injective
    rw [ff.map_preimage, P.map_id, T.map_id]
    simp only [Category.id_comp, Iso.hom_inv_id]
  map_comp f g := by
    apply ff.map_injective
    rw [T.map_comp, ff.map_preimage, ff.map_preimage, ff.map_preimage, P.map_comp]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- The lifted diagram retains its specified whole-diagram comparison. -/
def liftEssImageDiagramIso {C D J : Type*} [Category C] [Category D] [Category J]
    (T : C ⥤ D) (ff : T.FullyFaithful) (P : J ⥤ D)
    (h : ∀ j, T.essImage (P.obj j)) : liftEssImageDiagram T ff P h ⋙ T ≅ P :=
  NatIso.ofComponents (fun j => (h j).getIso) (by
    intro j k f
    change T.map (ff.preimage ((h j).getIso.hom ≫ P.map f ≫ (h k).getIso.inv)) ≫
      (h k).getIso.hom = (h j).getIso.hom ≫ P.map f
    rw [ff.map_preimage]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
  (I : Ideal A) [IsAdicComplete I A] {X : Scheme.{u}} [IsLocallyNoetherian X]
  (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f] (K : X.IdealSheafData)
  (h : ClosedThickeningCompletionEssSurj f I K)
  (F : AdicSystem X (idealThickeningIdealSheaf f I))

/-- The algebraic coefficient diagram lifted from the canonical formal
K-power quotient tower, under actual thickening effectivity. -/
def twoIdealCoefficientDiagram : ℕᵒᵖ ⥤ X.CoherentSheaf :=
  liftEssImageDiagram (completionFunctor X (idealThickeningIdealSheaf f I))
    (completionFunctorFullyFaithful I f)
    (AdicSystem.quotientTower X K (idealThickeningIdealSheaf f I) F)
    (fun n => quotientPower_mem_essImage_of_thickening_effectivity f I K h F n.unop)

/-- Completing the entire algebraic coefficient diagram gives the original
formal quotient diagram, including all transitions and stage zero. -/
def twoIdealCoefficientCompletionIso :
    twoIdealCoefficientDiagram I f K h F ⋙
        completionFunctor X (idealThickeningIdealSheaf f I) ≅
      AdicSystem.quotientTower X K (idealThickeningIdealSheaf f I) F :=
  liftEssImageDiagramIso (completionFunctor X (idealThickeningIdealSheaf f I))
    (completionFunctorFullyFaithful I f)
    (AdicSystem.quotientTower X K (idealThickeningIdealSheaf f I) F)
    (fun n => quotientPower_mem_essImage_of_thickening_effectivity f I K h F n.unop)

/-- Each actual algebraic coefficient is killed by exactly its independent
ideal power, detected using proper completion rather than faithful flatness. -/
theorem twoIdealCoefficient_killed (n : ℕ) :
    killedByIdealSheaf (K ^ n) ((twoIdealCoefficientDiagram I f K h F).obj (op n)).obj := by
  let G := (twoIdealCoefficientDiagram I f K h F).obj (op n)
  let D := adicSystemToDiagram X (idealThickeningIdealSheaf f I)
  let e := (twoIdealCoefficientCompletionIso I f K h F).app (op n)
  have hk := killedByIdealSheaf_of_completion I (K ^ n).subschemeι f G (fun m => by
    rw [IdealSheafData.ker_subschemeι]
    exact killedByIdealSheaf_of_iso (K ^ n) ((D.mapIso e).app (op m)).symm
      (AdicSystem.quotient_killed X (idealThickeningIdealSheaf f I) (K ^ n) F m))
  simpa only [IdealSheafData.ker_subschemeι] using hk

end AlgebraicGeometry.Scheme.Cohomology
