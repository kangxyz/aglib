/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.ModuleCat.HomComplex.NormalCoefficient
public import Aglib.Algebra.Homology.ModuleCat.HomComplex.TwoLayer
public import Mathlib.CategoryTheory.Abelian.Injective.Extend

/-!
# Original scalar homothety for the coinduced regular coefficient

The original signed evaluation at the regular module in degree zero, followed
by precomposition with the inverse original evaluation-at-one comparison,
is the scalar homothety into the module-valued endomorphism complex.

For a finite algebra over a regular local ring of specified finite dimension,
the existing finite-restriction biduality theorem proves that this same map is
a quasi-isomorphism. That theorem constructs its finite-projective model
internally. No projectivity or flatness of the algebra, supplied model,
homothety isomorphism, or canonical trivialization is assumed.

This is homothety of the actual coinduced coefficient complex. Transport to
its concentrated canonical homology and local dualizing uniqueness remain
separate obligations.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive HomologicalComplex
open CategoryTheory.Abelian

universe u

namespace CochainComplex.HomComplex

section Scalar

variable {S : Type u} [CommRing S]

/-- Original evaluation at the regular single, with the inner Hom identified
by its existing evaluation-at-one comparison. -/
def homothety (J : CochainComplex (ModuleCat.{u} S) ℤ) :
    (singleFunctor (ModuleCat.{u} S) 0).obj (ModuleCat.of S S) ⟶
      moduleComplex S J J :=
  evaluation ((singleFunctor (ModuleCat.{u} S) 0).obj (ModuleCat.of S S)) J ≫
    precomp S (regularSingleComplexIso J).inv J

/-- The constructed map is multiplication by the original scalar in every
degree of the coefficient complex; the degree-zero evaluation sign is one. -/
theorem homothety_f_zero_v_apply (J : CochainComplex (ModuleCat.{u} S) ℤ)
    (s : S) (n : ℤ) (x : J.X n) :
    (((homothety J).f 0
      ((singleObjXSelf (.up ℤ) 0 (ModuleCat.of S S)).inv s)).v n n (add_zero n)) x =
      s • x := by
  let U : CochainComplex (ModuleCat.{u} S) ℤ :=
    (singleFunctor (ModuleCat.{u} S) 0).obj (ModuleCat.of S S)
  let e : moduleComplex S U J ≅ J := regularSingleComplexIso J
  let φ : Cochain U J n := e.inv.f n x
  let v : U.X 0 := (singleObjXSelf (.up ℤ) 0 (ModuleCat.of S S)).inv s
  let z : Cochain (moduleComplex S U J) J 0 := evaluationComponent U J 0 v
  have hφ : (Cochain.fromSingleEquiv (zero_add n) φ) (1 : S) = x := by
    change regularSingleCochainEquiv J n ((regularSingleCochainEquiv J n).symm x) = x
    exact (regularSingleCochainEquiv J n).apply_symm_apply x
  have hc := Cochain.zero_cochain_comp_v (Cochain.ofHom e.inv) z n n (add_zero n)
  have hcx := ConcreteCategory.congr_hom hc x
  change (((Cochain.ofHom e.inv).comp z (zero_add 0)).v n n (add_zero n)) x =
    (z.v n n (add_zero n)) φ at hcx
  change (((Cochain.ofHom e.inv).comp z (zero_add 0)).v n n (add_zero n)) x = s • x
  calc
    _ = (z.v n n (add_zero n)) φ := hcx
    _ = (φ.v 0 n (zero_add n)) v := by
      simpa only [zero_mul, Int.negOnePow_zero, one_smul] using
        evaluationComponent_apply U J 0 v n n (add_zero n) φ
    _ = (Cochain.fromSingleEquiv (zero_add n) φ) s := rfl
    (Cochain.fromSingleEquiv (zero_add n) φ) s =
        s • (Cochain.fromSingleEquiv (zero_add n) φ) (1 : S) := by
      simpa only [smul_eq_mul, mul_one] using
        (Cochain.fromSingleEquiv (zero_add n) φ).hom.map_smul s (1 : S)
    _ = s • x := congrArg (fun z => s • z) hφ

end Scalar

section FiniteRegularBase

variable {R S : Type u} [CommRing R] [CommRing S] [IsRegularLocalRing R]
  (q : R →+* S) [Module.Finite R ((ModuleCat.restrictScalars q).obj (ModuleCat.of S S))]
  (d : ℕ) (hd : ringKrullDim R = (d : ℕ))

include hd in
/-- The actual scalar homothety of a coinduced regular coefficient is a
quasi-isomorphism. The finite-projective restriction model is constructed by
the existing finite-restriction biduality theorem, not supplied as an input. -/
theorem homothety_coinduced_quasiIso_of_restrictFinite
    (I : CochainComplex (ModuleCat.{u} R) ℤ) [I.IsKInjective]
    [(coinducedCoefficientComplex q I).IsKInjective]
    (ι : (singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R) ⟶ I)
    [QuasiIso ι] :
    QuasiIso (homothety (coinducedCoefficientComplex q I)) := by
  let := HasDerivedCategory.standard (ModuleCat.{u} S)
  let J := coinducedCoefficientComplex q I
  let U := (singleFunctor (ModuleCat.{u} S) 0).obj (ModuleCat.of S S)
  let : CochainComplex.IsKInjective
      (((ModuleCat.coextendScalars q).mapHomologicalComplex (.up ℤ)).obj I) :=
    inferInstanceAs ((coinducedCoefficientComplex q I).IsKInjective)
  have hsingle : IsIso ((derivedEvaluation J).app
      ((DerivedCategory.singleFunctor (ModuleCat.{u} S) 0).obj (ModuleCat.of S S))) :=
    derivedEvaluation_single_isIso_of_restrictFinite q d hd (ModuleCat.of S S) 0
      (ModuleCat.of R R) (LinearEquiv.refl R R) I ι
  let eU : DerivedCategory.Q.obj U ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} S) 0).obj (ModuleCat.of S S) :=
    ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} S) 0).app
      (ModuleCat.of S S)).symm
  have hQ : IsIso ((derivedEvaluation J).app (DerivedCategory.Q.obj U)) :=
    (NatTrans.isIso_app_iff_of_iso (derivedEvaluation J) eU).mpr hsingle
  rw [derivedEvaluation_app_Q] at hQ
  have hEval : IsIso (DerivedCategory.Q.map (evaluation U J)) :=
    @IsIso.of_isIso_comp_right _ _ _ _ _ (DerivedCategory.Q.map (evaluation U J))
      ((derivedDoubleDualFactors J).inv.app U)
      (NatIso.inv_app_isIso (derivedDoubleDualFactors J) U) hQ
  let : QuasiIso (evaluation U J) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat.{u} S) (evaluation U J)).mp hEval
  let : IsIso (precomp S (regularSingleComplexIso J).inv J) := by
    change IsIso ((moduleComplexFunctor S J).map (regularSingleComplexIso J).inv.op)
    infer_instance
  change QuasiIso (evaluation U J ≫ precomp S (regularSingleComplexIso J).inv J)
  infer_instance

include hd in
/-- Every actual injective resolution of the regular base supplies the
K-injective coefficient and its original augmentation internally. -/
theorem homothety_coinduced_injectiveResolution_quasiIso
    (I : InjectiveResolution (ModuleCat.of R R)) :
    QuasiIso (homothety (coinducedCoefficientComplex q I.cochainComplex)) := by
  let : I.cochainComplex.IsKInjective := CochainComplex.isKInjective_of_injective _ 0
  exact homothety_coinduced_quasiIso_of_restrictFinite q d hd I.cochainComplex I.ι'

end FiniteRegularBase

end CochainComplex.HomComplex
