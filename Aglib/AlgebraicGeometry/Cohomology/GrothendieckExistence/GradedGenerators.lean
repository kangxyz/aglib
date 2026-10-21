/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedGeneration

/-! # Generation of each original formal graded piece from the first level -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Coherent

namespace AlgebraicGeometry.Scheme.Cohomology

universe u
variable {A : Type u} [CommRing A] {X : Scheme.{u}} [IsLocallyNoetherian X]
  (f : X ⟶ Spec (CommRingCat.of A)) (I : Ideal A)
  (F : AdicSystem X (idealThickeningIdealSheaf f I))

/-- The degree-n piece is annihilated by the original base ideal. -/
theorem formalGradedPiece_scalar_eq_zero (n : ℕ) (b : I) :
    globalScalarEndomorphism X (F.gradedPiece n) (idealThickeningBaseScalar f b) = 0 := by
  let M := F.obj.obj (op (n + 1))
  let α := idealThickeningBaseScalar f
  have hE : globalScalarEndomorphism X (idealMultiple X α M (I ^ n)) (α b) = 0 := by
    apply (cancel_mono (idealMultipleι X α M (I ^ n))).mp
    rw [zero_comp, ← (globalScalarCenter X (α b)).naturality]
    apply (cancel_epi (factorThruImage (idealEvaluation X α M (I ^ n)))).mp
    rw [comp_zero, ← Category.assoc]
    change (factorThruImage (idealEvaluation X α M (I ^ n)) ≫
      image.ι (idealEvaluation X α M (I ^ n))) ≫ _ = 0
    rw [image.fac]
    apply Sigma.hom_ext
    intro a
    simp only [idealEvaluation, Sigma.ι_comp_desc_assoc, comp_zero]
    have hab : (b : A) * a ∈ I ^ (n + 1) := by
      rw [pow_succ']
      exact Ideal.mul_mem_mul b.property a.property
    have hmul : globalScalarEndomorphism X M (α a) ≫
        globalScalarEndomorphism X M (α b) =
        globalScalarEndomorphism X M (α ((b : A) * a)) := by
      simp only [globalScalarEndomorphism, map_mul, CatCenter.mul_app']
    rw [hmul]
    exact formalCoefficient_scalar_eq_zero f I F (n + 1) ⟨_, hab⟩
  let e := formalIdealMultipleGradedPieceIso f I F n
  apply (cancel_epi e.hom).mp
  rw [comp_zero, (globalScalarCenter X (α b)).naturality e.hom]
  change globalScalarEndomorphism X (idealMultiple X α M (I ^ n)) (α b) ≫ e.hom = 0
  rw [hE, zero_comp]

/-- The original scalar map into its original successive kernel. -/
def formalGradedPieceScalar (n : ℕ) (a : ↥(I ^ n)) :
    F.obj.obj (op (n + 1)) ⟶ F.gradedPiece n :=
  idealMultipleScalar X (idealThickeningBaseScalar f) (F.obj.obj (op (n + 1))) (I ^ n) a ≫
    (formalIdealMultipleGradedPieceIso f I F n).hom

/-- The first quotient of a common finite stage is the original first formal level. -/
def formalFirstQuotientIso (n : ℕ) :
    idealQuotient X (idealThickeningBaseScalar f) (F.obj.obj (op (n + 1))) I ≅
      F.obj.obj (op 1) := by
  let e : idealQuotient X (idealThickeningBaseScalar f) (F.obj.obj (op (n + 1))) I ≅
      idealQuotient X (idealThickeningBaseScalar f) (F.obj.obj (op (n + 1))) (I ^ 1) :=
    { hom := idealQuotientMap X (idealThickeningBaseScalar f) _ (by simp)
      inv := idealQuotientMap X (idealThickeningBaseScalar f) _ (by simp)
      hom_inv_id := by rw [idealQuotientMap_comp, idealQuotientMap_refl]
      inv_hom_id := by rw [idealQuotientMap_comp, idealQuotientMap_refl] }
  exact e ≪≫ baseIdealReductionIso f I F (Nat.succ_le_succ (Nat.zero_le n))

/-- Each degree-n scalar generator factors through the original first level. -/
def formalGradedPieceGenerator (n : ℕ) (a : ↥(I ^ n)) :
    F.obj.obj (op 1) ⟶ F.gradedPiece n :=
  (formalFirstQuotientIso f I F n).inv ≫
    idealQuotientDescOfAnnihilated X (idealThickeningBaseScalar f) I
      (formalGradedPieceScalar f I F n a) (formalGradedPiece_scalar_eq_zero f I F n)

@[reassoc (attr := simp)]
theorem formalGradedPiece_transition_generator (n : ℕ) (a : ↥(I ^ n)) :
    F.obj.map (homOfLE (Nat.succ_le_succ (Nat.zero_le n))).op ≫
      formalGradedPieceGenerator f I F n a = formalGradedPieceScalar f I F n a := by
  have he : idealQuotientπ X (idealThickeningBaseScalar f) (F.obj.obj (op (n + 1))) I ≫
      (formalFirstQuotientIso f I F n).hom =
      F.obj.map (homOfLE (Nat.succ_le_succ (Nat.zero_le n))).op := by
    simp only [formalFirstQuotientIso, Iso.trans_hom,
      idealQuotientπ_map_assoc, idealQuotientπ_baseIdealReductionIso_hom]
  rw [← he]
  simp [formalGradedPieceGenerator]

/-- The first formal coefficient generates every successive piece by its
original homogeneous scalar maps. This is a genuine epimorphism, not a
uniform-generation assumption. -/
instance formalGradedPieceGenerators_epi (n : ℕ) :
    Epi (Sigma.desc (formalGradedPieceGenerator f I F n)) := by
  let q : (∐ fun _ : ↥(I ^ n) => F.obj.obj (op (n + 1))) ⟶
      (∐ fun _ : ↥(I ^ n) => F.obj.obj (op 1)) :=
    Sigma.desc fun a => F.obj.map (homOfLE (Nat.succ_le_succ (Nat.zero_le n))).op ≫
      Sigma.ι (fun _ : ↥(I ^ n) => F.obj.obj (op 1)) a
  have hq : q ≫ Sigma.desc (formalGradedPieceGenerator f I F n) =
      factorThruImage (idealEvaluation X (idealThickeningBaseScalar f)
        (F.obj.obj (op (n + 1))) (I ^ n)) ≫
        (formalIdealMultipleGradedPieceIso f I F n).hom := by
    apply Sigma.hom_ext
    intro a
    simp [q, formalGradedPieceScalar, idealMultipleScalar, Category.assoc]
  have : Epi (q ≫ Sigma.desc (formalGradedPieceGenerator f I F n)) := by
    rw [hq]
    infer_instance
  exact epi_of_epi q _

end AlgebraicGeometry.Scheme.Cohomology
