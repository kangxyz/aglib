/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.ModuleCat.HomComplex.Cohomology
public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Coinduction.Projective
public import Aglib.Algebra.Homology.DerivedCategory.KInjective.Adjunction.InjectiveComplex
public import Aglib.RingTheory.RegularLocalRing.FiniteNormalAlgebra
public import Mathlib.Algebra.Homology.SingleHomology

/-!
# The original coefficient over a finite normal surface algebra

For an actual finite injective local map from a regular local ring of
dimension two to a normal Noetherian local domain of dimension two, native
finite-normal freeness makes scalar coinduction exact. The original
coefficient augmentation therefore gives a quasi-isomorphism from
`Hom_R(A,R)[0]` to the actual coinduced coefficient complex.

Evaluation at one identifies the actual A-module Hom complex from `A[0]`
with that coefficient complex. This proves its concentration in degree zero
and identifies its original A-module homology with the native coinduced
module, with action `(a * phi)(b) = phi(b*a)`. The same maps identify the
genuine derived dual when the chosen coefficient is a bounded-below
complex of injectives.

This is local coefficient concentration. It does not identify the
closed-embedding right-adjoint object with a canonical sheaf or identify
a geometric trace.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive Opposite

universe u d

namespace CochainComplex.HomComplex

section RegularSource

variable {A : Type u} [CommRing A]

/-- Original cochains from the regular module in degree zero are evaluated at one. -/
def regularSingleCochainEquiv (J : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ) :
    Cochain ((singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)) J n ≃ₗ[A]
      J.X n :=
  ({ Cochain.fromSingleEquiv (X := ModuleCat.of A A) (K := J) (zero_add n) with
      map_smul' a φ := by
        change (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (ModuleCat.of A A)).inv ≫
            (a • φ).v 0 n (zero_add n) =
          a • ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 (ModuleCat.of A A)).inv ≫
            φ.v 0 n (zero_add n))
        rw [Cochain.smul_v, Linear.comp_smul] } :
      Cochain ((singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)) J n ≃ₗ[A]
        (ModuleCat.of A A ⟶ J.X n)).trans
    (ModuleCat.homLinearEquiv.trans (LinearMap.ringLmapEquivSelf A A (J.X n)))

/-- The original single-object comparison is included before evaluation at one. -/
theorem regularSingleCochainEquiv_apply (J : CochainComplex (ModuleCat.{u} A) ℤ)
    (n : ℤ)
    (φ : Cochain ((singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)) J n) :
    regularSingleCochainEquiv J n φ =
      (Cochain.fromSingleEquiv (zero_add n) φ) (1 : A) := rfl

/-- A cochain from the original single constructor is evaluated by its supplied map. -/
theorem regularSingleCochainEquiv_fromSingleMk
    (J : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ) (f : ModuleCat.of A A ⟶ J.X n) :
    regularSingleCochainEquiv J n (Cochain.fromSingleMk f (zero_add n)) = f (1 : A) := by
  rw [regularSingleCochainEquiv_apply, Cochain.fromSingleEquiv_fromSingleMk]

/-- Evaluation at one is an isomorphism of the actual A-module complexes. -/
def regularSingleComplexIso (J : CochainComplex (ModuleCat.{u} A) ℤ) :
    moduleComplex A ((singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)) J ≅ J :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (regularSingleCochainEquiv J n).toModuleIso) (by
      intro p q hpq
      apply ConcreteCategory.hom_ext
      intro φ
      obtain ⟨f, rfl⟩ := Cochain.fromSingleMk_surjective φ p (zero_add p)
      change J.d p q (regularSingleCochainEquiv J p
          (Cochain.fromSingleMk f (zero_add p))) =
        regularSingleCochainEquiv J q (δ p q (Cochain.fromSingleMk f (zero_add p)))
      rw [Cochain.δ_fromSingleMk f (zero_add p) q q (zero_add q),
        regularSingleCochainEquiv_fromSingleMk, regularSingleCochainEquiv_fromSingleMk]
      rfl)

/-- The complex isomorphism uses the original evaluation map in each degree. -/
theorem regularSingleComplexIso_hom_f_apply (J : CochainComplex (ModuleCat.{u} A) ℤ)
    (n : ℤ)
    (φ : Cochain ((singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)) J n) :
    (regularSingleComplexIso J).hom.f n φ =
      (Cochain.fromSingleEquiv (zero_add n) φ) (1 : A) := rfl

/-- Evaluation at one commutes with original coefficient postcomposition. -/
@[reassoc]
theorem regularSingleComplexIso_naturality
    {J L : CochainComplex (ModuleCat.{u} A) ℤ} (f : J ⟶ L) :
    postcomp A ((singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)) f ≫
        (regularSingleComplexIso L).hom =
      (regularSingleComplexIso J).hom ≫ f := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro φ
  obtain ⟨g, rfl⟩ := Cochain.fromSingleMk_surjective φ n (zero_add n)
  change regularSingleCochainEquiv L n
      ((Cochain.fromSingleMk g (zero_add n)).comp (Cochain.ofHom f) (add_zero n)) =
    f.f n (regularSingleCochainEquiv J n (Cochain.fromSingleMk g (zero_add n)))
  rw [← Cochain.fromSingleMk_postcomp, regularSingleCochainEquiv_fromSingleMk,
    regularSingleCochainEquiv_fromSingleMk]
  rfl

end RegularSource

section CoinducedCoefficient

variable {R A : Type u} [CommRing R] [CommRing A] (σ : R →+* A)

/-- The coefficient is the native coinduced A-module, with its original source action. -/
def coinducedCoefficient : ModuleCat.{u} A :=
  (ModuleCat.coextendScalars σ).obj (ModuleCat.of R R)

/-- Its underlying functionals are literally R-linear maps from the restricted algebra. -/
def coinducedCoefficientEquiv :
    coinducedCoefficient σ ≃ₗ[A]
      ((ModuleCat.restrictScalars σ).obj (ModuleCat.of A A) →ₗ[R] R) :=
  ModuleCat.CoextendScalars.equiv σ (ModuleCat.of R R)

/-- The intrinsic A-action is multiplication on the original argument of the functional. -/
theorem coinducedCoefficientEquiv_smul_apply (φ : coinducedCoefficient σ) (a b : A) :
    coinducedCoefficientEquiv σ (a • φ) b = coinducedCoefficientEquiv σ φ (b * a) := rfl

/-- The original coefficient complex is mapped termwise by native coinduction. -/
def coinducedCoefficientComplex (I : CochainComplex (ModuleCat.{u} R) ℤ) :
    CochainComplex (ModuleCat.{u} A) ℤ :=
  ((ModuleCat.coextendScalars σ).mapHomologicalComplex (.up ℤ)).obj I

/-- The actual augmentation is coinduced after the inverse native single comparison. -/
def coinducedCoefficientAugmentation (I : CochainComplex (ModuleCat.{u} R) ℤ)
    (u : ((singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)) ⟶ I) :
    ((singleFunctor (ModuleCat.{u} A) 0).obj (coinducedCoefficient σ)) ⟶
      coinducedCoefficientComplex σ I :=
  (HomologicalComplex.singleMapHomologicalComplex
      (ModuleCat.coextendScalars σ) (.up ℤ) 0).inv.app (ModuleCat.of R R) ≫
    ((ModuleCat.coextendScalars σ).mapHomologicalComplex (.up ℤ)).map u

/-- The same augmentation, expressed in the original Hom complex from the regular module. -/
def coinducedRegularHomAugmentation (I : CochainComplex (ModuleCat.{u} R) ℤ)
    (u : ((singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)) ⟶ I) :
    ((singleFunctor (ModuleCat.{u} A) 0).obj (coinducedCoefficient σ)) ⟶
      moduleComplex A ((singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A))
        (coinducedCoefficientComplex σ I) :=
  coinducedCoefficientAugmentation σ I u ≫
    (regularSingleComplexIso (coinducedCoefficientComplex σ I)).inv

/-- Evaluation of the Hom augmentation is exactly the original coinduced augmentation. -/
@[reassoc]
theorem coinducedRegularHomAugmentation_evaluation
    (I : CochainComplex (ModuleCat.{u} R) ℤ)
    (u : ((singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)) ⟶ I) :
    coinducedRegularHomAugmentation σ I u ≫
        (regularSingleComplexIso (coinducedCoefficientComplex σ I)).hom =
      coinducedCoefficientAugmentation σ I u := by
  simp only [coinducedRegularHomAugmentation, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

/-- A bounded-below injective coefficient gives an actual K-injective coinduced complex. -/
instance coinducedCoefficientComplex_isKInjective
    (I : CochainComplex (ModuleCat.{u} R) ℤ) [I.IsStrictlyGE 0]
    [∀ n : ℤ, Injective (I.X n)] : (coinducedCoefficientComplex σ I).IsKInjective :=
  (ModuleCat.restrictCoextendScalarsAdj σ).isKInjective_map_of_injectiveComplex I 0

end CoinducedCoefficient

section NormalSurfaceCoefficient

variable {R A : Type u} [CommRing R] [CommRing A] [IsRegularLocalRing R]
  [IsLocalRing A] [IsNoetherianRing A] [IsDomain A] [IsIntegrallyClosed A]
  (σ : R →+* A) [IsLocalHom σ] (hfin : σ.Finite) (hinj : Function.Injective σ)
  (hR : ringKrullDim R = 2) (hA : ringKrullDim A = 2)

include hfin hinj hR hA

/-- Native finite-normal freeness supplies projectivity for the actual restricted module. -/
theorem restrictedProjective_of_finite_normal_dimension_two :
    Module.Projective R ((ModuleCat.restrictScalars σ).obj (ModuleCat.of A A)) := by
  let : Algebra R A := σ.toAlgebra
  let : Module.Finite R A := hfin
  let : Module.Free R A :=
    IsRegularLocalRing.free_of_finite_normal_dimension_two hR hA hinj
  let e : A ≃ₗ[R] ((ModuleCat.restrictScalars σ).obj (ModuleCat.of A A)) :=
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact Module.Projective.of_equiv' e

/-- Exact coinduction sends the actual regular-base augmentation to a quasi-isomorphism. -/
theorem coinducedCoefficientAugmentation_quasiIso
    (I : CochainComplex (ModuleCat.{u} R) ℤ)
    (u : ((singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)) ⟶ I) [QuasiIso u] :
    QuasiIso (coinducedCoefficientAugmentation σ I u) := by
  let : Module.Projective R ((ModuleCat.restrictScalars σ).obj (ModuleCat.of A A)) :=
    restrictedProjective_of_finite_normal_dimension_two σ hfin hinj hR hA
  let : (ModuleCat.coextendScalars.{u, u, u} σ).PreservesHomology :=
    ModuleCat.coextendScalars_preservesHomology_of_projective.{u, u, u} σ
  let : QuasiIso
      (((ModuleCat.coextendScalars.{u, u, u} σ).mapHomologicalComplex (.up ℤ)).map u) :=
    HomologicalComplex.quasiIso_map_of_preservesHomology u
      (ModuleCat.coextendScalars.{u, u, u} σ)
  let e := (HomologicalComplex.singleMapHomologicalComplex
    (ModuleCat.coextendScalars.{u, u, u} σ) (.up ℤ) 0).app (ModuleCat.of R R)
  let a := e.inv
  let : IsIso a := e.symm.isIso_hom
  let : QuasiIso a := quasiIso_of_isIso a
  change QuasiIso (a ≫
    (((ModuleCat.coextendScalars.{u, u, u} σ).mapHomologicalComplex (.up ℤ)).map u))
  exact quasiIso_comp a
    (((ModuleCat.coextendScalars.{u, u, u} σ).mapHomologicalComplex (.up ℤ)).map u)

/-- The original Hom augmentation is a quasi-isomorphism, without a concentration premise. -/
theorem coinducedRegularHomAugmentation_quasiIso
    (I : CochainComplex (ModuleCat.{u} R) ℤ)
    (u : ((singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)) ⟶ I) [QuasiIso u] :
    QuasiIso (coinducedRegularHomAugmentation σ I u) := by
  let : QuasiIso (coinducedCoefficientAugmentation σ I u) :=
    coinducedCoefficientAugmentation_quasiIso σ hfin hinj hR hA I u
  unfold coinducedRegularHomAugmentation
  infer_instance

/-- All other cohomology groups of the actual A-valued coefficient Hom complex vanish. -/
theorem coinducedRegularHom_isZero_homology
    (I : CochainComplex (ModuleCat.{u} R) ℤ)
    (u : ((singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)) ⟶ I) [QuasiIso u]
    (n : ℤ) (hn : n ≠ 0) :
    IsZero ((moduleComplex A
      ((singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A))
      (coinducedCoefficientComplex σ I)).homology n) := by
  let : QuasiIso (coinducedRegularHomAugmentation σ I u) :=
    coinducedRegularHomAugmentation_quasiIso σ hfin hinj hR hA I u
  exact (HomologicalComplex.isZero_single_obj_homology (.up ℤ) 0
    (coinducedCoefficient σ) n hn).of_iso
      (isoOfQuasiIsoAt (coinducedRegularHomAugmentation σ I u) n).symm

/-- Degree-zero homology is the same intrinsic A-module of regular-base functionals. -/
def coinducedRegularHomologyZeroIso
    (I : CochainComplex (ModuleCat.{u} R) ℤ)
    (u : ((singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)) ⟶ I) [QuasiIso u] :
    (moduleComplex A ((singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A))
        (coinducedCoefficientComplex σ I)).homology 0 ≅ coinducedCoefficient σ := by
  let : QuasiIso (coinducedRegularHomAugmentation σ I u) :=
    coinducedRegularHomAugmentation_quasiIso σ hfin hinj hR hA I u
  exact (isoOfQuasiIsoAt
    (coinducedRegularHomAugmentation σ I u) 0).symm ≪≫
      HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 (coinducedCoefficient σ)

/-- The degree-zero identification is normalized by the original augmentation map. -/
@[reassoc]
theorem coinducedRegularHomologyZeroIso_augmentation
    (I : CochainComplex (ModuleCat.{u} R) ℤ)
    (u : ((singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)) ⟶ I) [QuasiIso u] :
    HomologicalComplex.homologyMap (coinducedRegularHomAugmentation σ I u) 0 ≫
        (coinducedRegularHomologyZeroIso σ hfin hinj hR hA I u).hom =
      (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0
        (coinducedCoefficient σ)).hom := by
  let : QuasiIso (coinducedRegularHomAugmentation σ I u) :=
    coinducedRegularHomAugmentation_quasiIso σ hfin hinj hR hA I u
  simp only [coinducedRegularHomologyZeroIso, Iso.trans_hom, Iso.symm_hom,
    isoOfQuasiIsoAt_hom_inv_id_assoc]

/-- The genuine derived dual of the original regular module is this same coefficient single. -/
def normalCoefficientDerivedIso [HasDerivedCategory.{d} (ModuleCat.{u} A)]
    (I : CochainComplex (ModuleCat.{u} R) ℤ) [I.IsStrictlyGE 0]
    [∀ n : ℤ, Injective (I.X n)]
    (u : ((singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)) ⟶ I) [QuasiIso u] :
    (derivedDual (coinducedCoefficientComplex σ I)).obj
        (op ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A))) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (coinducedCoefficient σ) := by
  let : QuasiIso (coinducedRegularHomAugmentation σ I u) :=
    coinducedRegularHomAugmentation_quasiIso σ hfin hinj hR hA I u
  exact (derivedDual (coinducedCoefficientComplex σ I)).mapIso
      (((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} A) 0).app
        (ModuleCat.of A A)).symm.op) ≪≫
    (derivedDualFactors (coinducedCoefficientComplex σ I)).app
      (op ((singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A))) ≪≫
    (asIso (DerivedCategory.Q.map (coinducedRegularHomAugmentation σ I u))).symm ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} A) 0).app
      (coinducedCoefficient σ)).symm

end NormalSurfaceCoefficient

end CochainComplex.HomComplex
