/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.HilbertPolynomial.Basic
public import Aglib.AlgebraicGeometry.Cohomology.Projective.HilbertPolynomial.AffinePushforward
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Twisting.Picard
public import Aglib.AlgebraicGeometry.Modules.ProjectionFormula.FiniteLocallyFree
public import Aglib.AlgebraicGeometry.Modules.StructureSheaf.Pushforward
public import Aglib.AlgebraicGeometry.Modules.Coherent.Pushforward.ClosedImmersion.GeneralPushforward
public import Aglib.AlgebraicGeometry.Modules.Invertible.Bidual.Affine
public import Aglib.AlgebraicGeometry.Modules.Invertible.PullbackTensor.Local
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Pullback

/-!
# The native Hilbert polynomial under an original affine pullback scaling

For an actual closed embedding j and an affine endomorphism f over the
same field, a scaling law on the actual pulled O(1) class identifies the
Hilbert polynomial of j_* f_* O with the original polynomial of j_* O
composed with the corresponding integer dilation. The native integer
twist-class homomorphism supplies every integer twist, negative included.

The ordinary projection formula and the original affine cohomology
equivalence make the comparison. The statement concerns reparametrization
by pullback; no whole Euler-characteristic multiplication by rank is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.Modules.Invertible.PullbackTensor.Local
open scoped Polynomial

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable (k : Type u) [Field k] (ι : Type u) {X : Scheme.{u}}

private theorem pullbackClass_twist_of_scaling
    (j : X ⟶ ProjectiveSpace k ι) (f : X ⟶ X) (c : ℕ)
    (h : pullbackClass f (pullbackClass j (classOf _ (twistingLineBundle k ι 1))) =
      c • pullbackClass j (classOf _ (twistingLineBundle k ι 1))) (m : ℤ) :
    pullbackClass (f ≫ j) (classOf _ (twistingLineBundle k ι m)) =
      pullbackClass j (classOf _ (twistingLineBundle k ι ((c : ℤ) * m))) := by
  let A := classOf (ProjectiveSpace k ι) (twistingLineBundle k ι 1)
  have hm (a : ℤ) : classOf (ProjectiveSpace k ι) (twistingLineBundle k ι a) = a • A :=
    twistClassHom_eq_zsmul k ι a
  have hh : pullbackHom f (pullbackHom j A) = (c : ℤ) • pullbackHom j A := by
    simpa only [pullbackHom_apply, natCast_zsmul] using h
  rw [pullbackClass_comp f j]
  change pullbackHom f (pullbackHom j (classOf _ (twistingLineBundle k ι m))) =
    pullbackHom j (classOf _ (twistingLineBundle k ι ((c : ℤ) * m)))
  rw [hm m, hm ((c : ℤ) * m), map_zsmul, map_zsmul, map_zsmul, hh,
    ← mul_smul, mul_comm]

/-- The original Hilbert function of j_* f_* O is the dilation of the
original Hilbert function of j_* O when the actual pulled O(1) class scales.
The comparison holds at every integer, including negative twists. -/
theorem projectiveHilbertFunction_pushforwardStructure_comp_mul
    (j : X ⟶ ProjectiveSpace k ι) [IsClosedImmersion j]
    (f : X ⟶ X) [IsAffineHom f]
    (hbase : f ≫ (j ≫ toSpec k ι) = j ≫ toSpec k ι) (c : ℕ)
    (hscale : pullbackClass f (pullbackClass j (classOf _ (twistingLineBundle k ι 1))) =
      c • pullbackClass j (classOf _ (twistingLineBundle k ι 1))) (m : ℤ) :
    projectiveHilbertFunction k ι ((Scheme.Modules.pushforward j).obj
      (pushforwardStructureSheaf f)) m =
      projectiveHilbertFunction k ι ((Scheme.Modules.pushforward j).obj
        (SheafOfModules.unit X.ringCatSheaf)) ((c : ℤ) * m) := by
  let P := ProjectiveSpace k ι
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let b : X ⟶ P := f ≫ j
  let Tm := twistingSheaf k ι m
  let Tcm := twistingSheaf k ι ((c : ℤ) * m)
  let Lm : X.Modules := (Scheme.Modules.pullback b).obj Tm
  let Nm : X.Modules := (Scheme.Modules.pullback j).obj Tcm
  let : IsAffineHom b := inferInstance
  let : IsFiniteLocallyFree X Nm := inferInstance
  have hN := coherent_of_finiteLocallyFree Nm
  let : Nm.IsQuasicoherent := quasicoherent_of_affineCharts Nm (fun R a _ => (hN R a).1)
  have hclass : classOf X (pullbackLineBundle b (twistingLineBundle k ι m)) =
      classOf X (pullbackLineBundle j (twistingLineBundle k ι ((c : ℤ) * m))) :=
    pullbackClass_twist_of_scaling k ι j f c hscale m
  obtain ⟨e⟩ : Nonempty (Lm ≅ Nm) := (class_eq_iff X _ _).mp hclass
  let eA : (moduleTensorLeftFunctor P Tm).obj
      ((Scheme.Modules.pushforward j).obj (pushforwardStructureSheaf f)) ≅
      (Scheme.Modules.pushforward b).obj Lm :=
    (moduleTensorLeftFunctor P Tm).mapIso ((pushforwardComp f j).app O) ≪≫
      projectionFormulaIso b Tm O ≪≫
        (Scheme.Modules.pushforward b).mapIso ((SheafOfModulesOfCommRing.tensorRightUnitIso
          X.sheaf).app Lm)
  let eB : (moduleTensorLeftFunctor P Tcm).obj ((Scheme.Modules.pushforward j).obj O) ≅
      (Scheme.Modules.pushforward j).obj Nm :=
    projectionFormulaIso j Tcm O ≪≫
      (Scheme.Modules.pushforward j).mapIso
        ((SheafOfModulesOfCommRing.tensorRightUnitIso X.sheaf).app Nm)
  have hb : b ≫ toSpec k ι = j ≫ toSpec k ι := by
    simpa only [b, Category.assoc] using hbase
  change projectiveEulerChar k ι ((moduleTensorLeftFunctor P Tm).obj
    ((Scheme.Modules.pushforward j).obj (pushforwardStructureSheaf f))) =
      projectiveEulerChar k ι ((moduleTensorLeftFunctor P Tcm).obj
        ((Scheme.Modules.pushforward j).obj O))
  exact (projectiveEulerChar_congr k ι eA).trans
    ((projectiveEulerChar_congr k ι ((Scheme.Modules.pushforward b).mapIso e)).trans
      ((projectiveEulerChar_pushforward_eq_of_toSpec_eq k ι b j hb Nm).trans
        (projectiveEulerChar_congr k ι eB).symm))

/-- The native rational polynomial of j_* f_* O is the original native
polynomial of j_* O composed with the actual scalar dilation. No locally
free rank or polynomial-degree hypothesis is used. -/
theorem projectiveHilbertPolynomial_pushforwardStructure_eq_comp_mul
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (j : X ⟶ ProjectiveSpace k ι) [IsClosedImmersion j]
    (f : X ⟶ X) [IsAffineHom f]
    (hbase : f ≫ (j ≫ toSpec k ι) = j ≫ toSpec k ι) (c : ℕ)
    (hscale : pullbackClass f (pullbackClass j (classOf _ (twistingLineBundle k ι 1))) =
      c • pullbackClass j (classOf _ (twistingLineBundle k ι 1))) :
    projectiveHilbertPolynomial k ι ((Scheme.Modules.pushforward j).obj
      (pushforwardStructureSheaf f)) =
      (projectiveHilbertPolynomial k ι ((Scheme.Modules.pushforward j).obj
        (SheafOfModules.unit X.ringCatSheaf))).comp (Polynomial.C (c : ℚ) * Polynomial.X) := by
  have hO :=
    Scheme.Modules.Coherent.Pushforward.ClosedImmersion.affineLocallyFiniteType_pushforward j
      (affineLocallyFiniteType_structureModule X)
  apply projectiveHilbertPolynomial_eq_of_eval
  intro m
  rw [projectiveHilbertFunction_pushforwardStructure_comp_mul k ι j f hbase c hscale m]
  have h := projectiveHilbertFunction_eq_eval k ι n e _ hO ((c : ℤ) * m)
  simpa only [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Int.cast_mul, Int.cast_natCast] using h

end AlgebraicGeometry.Scheme.Cohomology
