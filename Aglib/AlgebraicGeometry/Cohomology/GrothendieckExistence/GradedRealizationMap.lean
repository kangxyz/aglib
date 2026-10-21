/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedLocalMap
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedFiniteCover
public import Aglib.AlgebraicGeometry.Modules.InternalHom.LocalEpiDescent

/-! # Actual morphisms between coherent graded quotient realizations

The ambient degree-zero map descends through the original quotient epimorphism.
The resulting map has exactly the original tensor-linear section maps on charts.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Coherent
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Cohomology

variable {A : Type u} [CommRing A] {X : Scheme.{u}} [IsLocallyNoetherian X]
  (f : X ⟶ Spec (CommRingCat.of A)) (I : Ideal A)
  {F G : AdicSystem X (idealThickeningIdealSheaf f I)} (φ : F ⟶ G)

/-- The actual local coefficient maps glue through the retained quotient
presentations; no independent map descent or overlap square is assumed. -/
theorem exists_formalGradedRealizationMap_on_cover
    {ι : Type u} (U : ι → X.affineOpens) (hU : ∀ x : X, ∃ i, x ∈ (U i).val)
    (P Q : (formalGradedSpace f I).Modules)
    (p : formalGradedAmbient f I F ⟶ P) (q : formalGradedAmbient f I G ⟶ Q) [Epi p]
    (eP : ∀ i, P.restrict (formalGradedChart f I (U i)) ≅
      tilde (formalGradedLocalModule f I F (U i)))
    (eQ : ∀ i, Q.restrict (formalGradedChart f I (U i)) ≅
      tilde (formalGradedLocalModule f I G (U i)))
    (hP : ∀ i, (Scheme.Modules.restrictFunctor (formalGradedChart f I (U i))).map p ≫
      (eP i).hom =
      formalGradedLocalQuotient f I F (U i))
    (hQ : ∀ i, (Scheme.Modules.restrictFunctor (formalGradedChart f I (U i))).map q ≫
      (eQ i).hom =
      formalGradedLocalQuotient f I G (U i)) :
    ∃ g : P ⟶ Q, p ≫ g = formalGradedAmbientMap f I φ ≫ q ∧
      ∀ i, (Scheme.Modules.restrictFunctor (formalGradedChart f I (U i))).map g ≫ (eQ i).hom =
        (eP i).hom ≫ formalGradedLocalMap f I φ (U i) := by
  let (V : X.Opens) : Algebra A Γ(X, V) := formalGradedSectionAlgebra f V
  let a (i : ι) := formalGradedChart f I (U i)
  let k (i : ι) := (eP i).hom ≫ formalGradedLocalMap f I φ (U i) ≫ (eQ i).inv
  have hk (i : ι) : (Scheme.Modules.restrictFunctor (a i)).map p ≫ k i =
      (Scheme.Modules.restrictFunctor (a i)).map (formalGradedAmbientMap f I φ ≫ q) := by
    apply (cancel_mono (eQ i).hom).mp
    dsimp only [k, a]
    simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
    rw [← Category.assoc, hP i, hQ i]
    exact (formalGradedLocalQuotient_naturality f I φ (U i)).symm
  have hc : ∀ y : formalGradedSpace f I, ∃ i, ∃ z, a i z = y := by
    intro y
    obtain ⟨i, z, hz⟩ := formalGradedCharts_cover f I U hU y
    exact ⟨i, z, hz⟩
  obtain ⟨g, hg, hgi⟩ := InternalHom.exists_factorization_of_local_epi
    (fun i => Spec (CommRingCat.of (Γ(X, U i) ⊗[A] I.associatedGraded)))
    a hc p (formalGradedAmbientMap f I φ ≫ q) k hk
  refine ⟨g, hg, fun i => ?_⟩
  rw [hgi]
  simp only [k, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end AlgebraicGeometry.Scheme.Cohomology
