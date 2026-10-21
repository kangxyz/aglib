/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.FullFaithful
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.RelationDiagram
public import Aglib.CategoryTheory.Abelian.PresentationEffectivity

/-!
# Algebraization from actual coefficient and relation presentations

Proper full faithfulness lifts the relation arrow between completed coherent
coefficients. Its algebraic cokernel completes to the given formal system,
by pointwise right exactness in the ambient inverse-diagram category. No
abelian structure or levelwise kernel is asserted for the category of
cartesian coherent adic systems.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Coherent

namespace AlgebraicGeometry.Scheme.Cohomology

universe u
variable {A : Type u} [CommRing A] [IsNoetherianRing A]
  (I : Ideal A) [IsAdicComplete I A] {X : Scheme.{u}} [IsLocallyNoetherian X]
  (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]

/-- Native completion into the ambient diagram category is fully faithful,
with the original coefficient morphisms as its maps. -/
def ambientCompletionFullyFaithful :
    (ambientCompletion X (idealThickeningIdealSheaf f I)).FullyFaithful :=
  (idealPowerCompletionToDiagramFullyFaithful I f).ofIso
    (idealPowerCompletionComparison I f)

/-- Two actual componentwise epimorphisms, onto the formal coefficient and
its ordinary relation diagram, algebraize the coefficient. The witness is
obtained by the algebraic cokernel of the lifted original relation arrow. -/
theorem completion_essImage_of_coefficient_and_relation_epi
    {P Q : X.CoherentSheaf}
    (F : AdicSystem X (idealThickeningIdealSheaf f I))
    (π : (completionFunctor X (idealThickeningIdealSheaf f I)).obj P ⟶ F)
    (hπ : ∀ n : ℕ, Epi (π.hom.app (op n)))
    (r : (ambientCompletion X (idealThickeningIdealSheaf f I)).obj Q ⟶
      AdicSystem.relationDiagram π)
    (hr : ∀ n : ℕ, Epi (r.app (op n))) :
    (completionFunctor X (idealThickeningIdealSheaf f I)).essImage F := by
  let C := ambientCompletion X (idealThickeningIdealSheaf f I)
  let : C.Full := (ambientCompletionFullyFaithful I f).full
  let : Epi π.hom := (NatTrans.epi_iff_epi_app π.hom).mpr (fun n => hπ n.unop)
  let : Epi r := (NatTrans.epi_iff_epi_app r).mpr (fun n => hr n.unop)
  have h : C.essImage F.obj := C.essImage_of_epi_of_kernel_epi π.hom r
  obtain ⟨M, ⟨e⟩⟩ := h
  exact ⟨M, ⟨ObjectProperty.isoMk (IsAdicSystem X (idealThickeningIdealSheaf f I)) e⟩⟩

end AlgebraicGeometry.Scheme.Cohomology
