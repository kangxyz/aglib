/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.ModuleCat.HomComplex.Derived
public import Aglib.Algebra.Homology.ModuleCat.HomComplex.Coinduction
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Original signed evaluation on finite-projective restrictions

Native module reflexivity proves signed biduality for a bounded complex of
finite projective modules. Postcomposition with the actual coefficient
augmentation and the original evaluation square transfer this result to a
fixed K-injective coefficient. The original coinduction comparison then
reflects quasi-isomorphism of the genuine A-linear evaluation, whose image
is the already constructed derived evaluation.

The coefficient is an actual universe-sized module W with W ≃ₗ[R] R. The
finite-projective model, its term bounds and its original quasi-isomorphism
to scalar restriction are retained. No evaluation-isomorphism, duality-data,
A-perfectness or surface-model premise replaces any of these constructions.
-/

@[expose] public section
noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive Opposite

universe r u v w z

namespace CochainComplex.HomComplex

section Postcomposition

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- Original target postcomposition on the native additive Hom complex. -/
def additivePostcomp (K : CochainComplex C ℤ) {L J : CochainComplex C ℤ} (f : L ⟶ J) :
    HomComplex K L ⟶ HomComplex K J where
  f n := AddCommGrpCat.ofHom
    { toFun := fun x => x.comp (Cochain.ofHom f) (add_zero n)
      map_zero' := Cochain.zero_comp _ _
      map_add' := fun x y => Cochain.add_comp x y _ _ }
  comm' i j hij := by
    apply ConcreteCategory.hom_ext
    intro x
    exact δ_comp_ofHom x f j

/-- The actual target map induces the original cocycle postcomposition. -/
def cocyclePostcomp (K : CochainComplex C ℤ) {L J : CochainComplex C ℤ}
    (f : L ⟶ J) (n : ℤ) : Cocycle K L n →+ Cocycle K J n where
  toFun x := x.postcomp f
  map_zero' := by
    apply Subtype.ext
    change (0 : Cochain K L n).comp (Cochain.ofHom f) (add_zero n) = 0
    exact Cochain.zero_comp _ _
  map_add' x y := by
    apply Subtype.ext
    change (x.1 + y.1).comp (Cochain.ofHom f) (add_zero n) =
      x.1.comp (Cochain.ofHom f) (add_zero n) + y.1.comp (Cochain.ofHom f) (add_zero n)
    exact Cochain.add_comp x.1 y.1 _ _

/-- Postcomposition on native Hom cohomology, retaining the original shifted target map. -/
def cohomologyPostcomp (K : CochainComplex C ℤ) {L J : CochainComplex C ℤ}
    (f : L ⟶ J) (n : ℤ) : CohomologyClass K L n →+ CohomologyClass K J n where
  toFun x := (CohomologyClass.homAddEquiv (K := K) (L := J) (n := n)).symm
    (CohomologyClass.homAddEquiv (K := K) (L := L) (n := n) x ≫
      (HomotopyCategory.quotient C (.up ℤ)).map (f⟦n⟧'))
  map_zero' := by simp
  map_add' x y := by simp

/-- Postcomposition carries each original cocycle to its actual postcomposed class. -/
theorem cohomologyPostcomp_mk (K : CochainComplex C ℤ) {L J : CochainComplex C ℤ}
    (f : L ⟶ J) (n : ℤ) (x : Cocycle K L n) :
    cohomologyPostcomp K f n (CohomologyClass.mk x) = CohomologyClass.mk (x.postcomp f) := by
  apply (CohomologyClass.homAddEquiv (K := K) (L := J) (n := n)).injective
  change (CohomologyClass.homAddEquiv (K := K) (L := J) (n := n))
      ((CohomologyClass.homAddEquiv (K := K) (L := J) (n := n)).symm _) = _
  rw [AddEquiv.apply_symm_apply]
  change (HomotopyCategory.quotient C (.up ℤ)).map (Cocycle.equivHomShift.symm x) ≫
      (HomotopyCategory.quotient C (.up ℤ)).map (f⟦n⟧') =
    (HomotopyCategory.quotient C (.up ℤ)).map (Cocycle.equivHomShift.symm (x.postcomp f))
  rw [Cocycle.equivHomShift_symm_postcomp, Functor.map_comp]

/-- The original additive Hom map has the specified native cocycle and cohomology maps. -/
def additivePostcompHomologyMapData (K : CochainComplex C ℤ)
    {L J : CochainComplex C ℤ} (f : L ⟶ J) (n : ℤ) :
    ShortComplex.LeftHomologyMapData
      ((HomologicalComplex.shortComplexFunctor AddCommGrpCat (.up ℤ) n).map
        (additivePostcomp K f))
      (leftHomologyData K L n) (leftHomologyData K J n) where
  φK := AddCommGrpCat.ofHom (cocyclePostcomp K f n)
  φH := AddCommGrpCat.ofHom (cohomologyPostcomp K f n)
  commi := by ext x; rfl
  commf' := by
    apply (cancel_mono (leftHomologyData K J n).i).mp
    simp only [Category.assoc, ShortComplex.LeftHomologyData.f'_i]
    erw [show AddCommGrpCat.ofHom (cocyclePostcomp K f n) ≫
        (leftHomologyData K J n).i =
      (leftHomologyData K L n).i ≫ (additivePostcomp K f).f n by ext x; rfl]
    rw [← Category.assoc, ShortComplex.LeftHomologyData.f'_i]
    exact ((additivePostcomp K f).comm _ _).symm
  commπ := by
    ext x
    exact cohomologyPostcomp_mk K f n x

end Postcomposition

section KProjective

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

private def homotopyProjectiveDerivedEquiv (K L : CochainComplex C ℤ) [K.IsKProjective] :
    ((HomotopyCategory.quotient C (.up ℤ)).obj K ⟶
      (HomotopyCategory.quotient C (.up ℤ)).obj L) ≃+
    (DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj L) :=
  { Equiv.ofBijective (homotopyToDerivedHom K L)
      ((Iso.homCongr ((DerivedCategory.quotientCompQhIso C).app K)
        ((DerivedCategory.quotientCompQhIso C).app L)).bijective.comp
          (CochainComplex.IsKProjective.Qh_map_bijective K
            ((HomotopyCategory.quotient C (.up ℤ)).obj L))) with
    map_add' f g := by
      simp [homotopyToDerivedHom, Preadditive.comp_add, Preadditive.add_comp] }

private theorem homotopyProjectiveDerivedEquiv_map
    (K L : CochainComplex C ℤ) [K.IsKProjective] (f : K ⟶ L) :
    homotopyProjectiveDerivedEquiv K L ((HomotopyCategory.quotient C (.up ℤ)).map f) =
      DerivedCategory.Q.map f :=
  NatIso.naturality_1 (DerivedCategory.quotientCompQhIso C) f

private def cohomologyProjectiveDerivedEquiv (K L : CochainComplex C ℤ)
    [K.IsKProjective] (n : ℤ) :
    CohomologyClass K L n ≃+
      (DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj (L⟦n⟧)) :=
  (CohomologyClass.homAddEquiv (K := K) (L := L) (n := n)).trans
    (homotopyProjectiveDerivedEquiv K (L⟦n⟧))

private theorem cohomologyProjectiveDerivedEquiv_postcomp
    (K : CochainComplex C ℤ) [K.IsKProjective] {L J : CochainComplex C ℤ}
    (f : L ⟶ J) (n : ℤ) (x : CohomologyClass K L n) :
    cohomologyProjectiveDerivedEquiv K J n (cohomologyPostcomp K f n x) =
      cohomologyProjectiveDerivedEquiv K L n x ≫ DerivedCategory.Q.map (f⟦n⟧') := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  rw [cohomologyPostcomp_mk]
  change homotopyProjectiveDerivedEquiv K (J⟦n⟧)
      ((HomotopyCategory.quotient C (.up ℤ)).map
        (Cocycle.equivHomShift.symm (x.postcomp f))) =
    homotopyProjectiveDerivedEquiv K (L⟦n⟧)
      ((HomotopyCategory.quotient C (.up ℤ)).map (Cocycle.equivHomShift.symm x)) ≫
      DerivedCategory.Q.map (f⟦n⟧')
  rw [homotopyProjectiveDerivedEquiv_map, homotopyProjectiveDerivedEquiv_map,
    Cocycle.equivHomShift_symm_postcomp, Functor.map_comp]

private theorem cohomologyPostcomp_bijective (K : CochainComplex C ℤ) [K.IsKProjective]
    {L J : CochainComplex C ℤ} (f : L ⟶ J) [QuasiIso f] (n : ℤ) :
    Function.Bijective (cohomologyPostcomp K f n) := by
  constructor
  · intro x y h
    apply (cohomologyProjectiveDerivedEquiv K L n).injective
    apply (cancel_mono (DerivedCategory.Q.map (f⟦n⟧'))).mp
    rw [← cohomologyProjectiveDerivedEquiv_postcomp,
      ← cohomologyProjectiveDerivedEquiv_postcomp, h]
  · intro z
    obtain ⟨x, hx⟩ := (cohomologyProjectiveDerivedEquiv K L n).surjective
      (cohomologyProjectiveDerivedEquiv K J n z ≫ inv (DerivedCategory.Q.map (f⟦n⟧')))
    refine ⟨x, (cohomologyProjectiveDerivedEquiv K J n).injective ?_⟩
    rw [cohomologyProjectiveDerivedEquiv_postcomp, hx]
    simp

/-- An actual target quasi-isomorphism acts quasi-isomorphically on Hom
from a K-projective source. -/
theorem additivePostcomp_quasiIso (K : CochainComplex C ℤ) [K.IsKProjective]
    {L J : CochainComplex C ℤ} (f : L ⟶ J) [QuasiIso f] :
    QuasiIso (additivePostcomp K f) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  let h := additivePostcompHomologyMapData K f n
  let E := AddEquiv.ofBijective (cohomologyPostcomp K f n)
    (cohomologyPostcomp_bijective K f n)
  let e := AddEquiv.toAddCommGrpIso
    (X := AddCommGrpCat.of (CohomologyClass K L n))
    (Y := AddCommGrpCat.of (CohomologyClass K J n)) E
  have : IsIso h.φH := by
    change IsIso e.hom
    infer_instance
  change IsIso (ShortComplex.homologyMap _)
  rw [h.homologyMap_eq]
  infer_instance

end KProjective

section ModuleKProjective

variable (R : Type r) [Ring R] {C : Type u} [Category.{v} C] [Abelian C] [Linear R C]

/-- The original forgetful identity retains the actual target postcomposition map. -/
theorem moduleComplexForgetIso_postcomp (K : CochainComplex C ℤ)
    {L J : CochainComplex C ℤ} (f : L ⟶ J) :
    ((forget₂ (ModuleCat.{v} R) AddCommGrpCat).mapHomologicalComplex (.up ℤ)).map
        (postcomp R K f) ≫ (moduleComplexForgetIso R K J).hom =
      (moduleComplexForgetIso R K L).hom ≫ additivePostcomp K f := by
  ext n x
  rfl

/-- Target quasi-isomorphism invariance holds for the original module-valued Hom map. -/
theorem postcomp_quasiIso (K : CochainComplex C ℤ) [K.IsKProjective]
    {L J : CochainComplex C ℤ} (f : L ⟶ J) [QuasiIso f] :
    QuasiIso (postcomp R K f) := by
  let := HasDerivedCategory.standard C
  let U := forget₂ (ModuleCat.{v} R) AddCommGrpCat
  let : QuasiIso (additivePostcomp K f) := additivePostcomp_quasiIso K f
  have hcomp : QuasiIso
      ((U.mapHomologicalComplex (.up ℤ)).map (postcomp R K f) ≫
        (moduleComplexForgetIso R K J).hom) := by
    rw [moduleComplexForgetIso_postcomp]
    infer_instance
  let : QuasiIso ((U.mapHomologicalComplex (.up ℤ)).map (postcomp R K f)) :=
    (quasiIso_iff_comp_right _ _).mp hcomp
  exact (HomologicalComplex.quasiIso_map_iff_of_preservesHomology (postcomp R K f) U).mp
    inferInstance

end ModuleKProjective

section FiniteProjective

variable {R : Type u} [CommRing R]

private theorem moduleMap_units_smul {M N : ModuleCat.{max u v} R} (f : M ⟶ N)
    (s : ℤˣ) (x : M) : f (s • x) = s • f x := by
  change f.hom ((s : ℤ) • x) = (s : ℤ) • f.hom x
  exact map_zsmul f.hom (s : ℤ) x

/-- Coefficient change uses the very same signed evaluation on both sides. -/
theorem evaluation_coefficient_naturality (K : CochainComplex (ModuleCat.{max u v} R) ℤ)
    {L I : CochainComplex (ModuleCat.{max u v} R) ℤ} (f : L ⟶ I) :
    evaluation K I ≫ precomp R (postcomp R K f) I =
      evaluation K L ≫ postcomp R (moduleComplex R K L) f := by
  apply HomologicalComplex.hom_ext
  intro p
  apply ConcreteCategory.hom_ext
  intro x
  apply Cochain.ext
  intro q r hqr
  apply ConcreteCategory.hom_ext
  intro φ
  change (((Cochain.ofHom (postcomp R K f)).comp
      (evaluationComponent K I p x) (zero_add p)).v q r hqr) φ =
    (((evaluationComponent K L p x).comp (Cochain.ofHom f) (add_zero p)).v q r hqr) φ
  rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v,
    Cochain.comp_zero_cochain_v, Cochain.ofHom_v]
  change ((evaluationComponent K I p x).v q r hqr) ((postcomp R K f).f q φ) =
    f.f r (((evaluationComponent K L p x).v q r hqr) φ)
  rw [evaluationComponent_apply, evaluationComponent_apply, postcomp_f_apply,
    Cochain.comp_zero_cochain_v, Cochain.ofHom_v, moduleMap_units_smul]
  rfl

/-- Native toSingleEquiv, with its existing scalar multiplication retained. -/
def cochainToSingleLinearEquiv (K : CochainComplex (ModuleCat.{max u v} R) ℤ)
    (W : ModuleCat.{max u v} R) (p n : ℤ) (h : p + n = 0) :
    Cochain K ((singleFunctor (ModuleCat.{max u v} R) 0).obj W) n ≃ₗ[R] (K.X p ⟶ W) :=
  { Cochain.toSingleEquiv h with
    map_smul' a φ := by
      change (a • φ).v p 0 h ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 W).hom =
        a • (φ.v p 0 h ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 W).hom)
      rw [Cochain.smul_v, Linear.smul_comp] }

/-- W is an actual chosen universe-sized copy of R, not a duality datum. -/
def singleDualTermEquiv (K : CochainComplex (ModuleCat.{max u v} R) ℤ)
    (W : ModuleCat.{max u v} R) (e : W ≃ₗ[R] R) (p n : ℤ) (h : p + n = 0) :
    (moduleComplex R K ((singleFunctor (ModuleCat.{max u v} R) 0).obj W)).X n ≃ₗ[R]
      Module.Dual R (K.X p) :=
  (cochainToSingleLinearEquiv K W p n h).trans
    (ModuleCat.homLinearEquiv.trans (LinearEquiv.congrRight e))

/-- The term comparison uses the original cochain component and
native single-object isomorphism. -/
theorem singleDualTermEquiv_apply (K : CochainComplex (ModuleCat.{max u v} R) ℤ)
    (W : ModuleCat.{max u v} R) (e : W ≃ₗ[R] R) (p n : ℤ) (h : p + n = 0)
    (φ : Cochain K ((singleFunctor (ModuleCat.{max u v} R) 0).obj W) n) (x : K.X p) :
    singleDualTermEquiv K W e p n h φ x =
      e ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 W).hom (φ.v p 0 h x)) := rfl

/-- Double Hom is compared with the ordinary double dual using the inverse first comparison. -/
def singleDoubleDualTermEquiv (K : CochainComplex (ModuleCat.{max u v} R) ℤ)
    (W : ModuleCat.{max u v} R) (e : W ≃ₗ[R] R) (p : ℤ) :
    (moduleComplex R
        (moduleComplex R K ((singleFunctor (ModuleCat.{max u v} R) 0).obj W))
        ((singleFunctor (ModuleCat.{max u v} R) 0).obj W)).X p ≃ₗ[R]
      Module.Dual R (Module.Dual R (K.X p)) :=
  (singleDualTermEquiv
    (moduleComplex R K ((singleFunctor (ModuleCat.{max u v} R) 0).obj W))
    W e (-p) p (neg_add_cancel p)).trans
      (singleDualTermEquiv K W e p (-p) (add_neg_cancel p)).symm.dualMap

/-- The original evaluation component becomes signed ordinary evaluation,
with its native unit sign. -/
theorem singleDoubleDualTermEquiv_evaluation
    (K : CochainComplex (ModuleCat.{max u v} R) ℤ)
    (W : ModuleCat.{max u v} R) (e : W ≃ₗ[R] R) (p : ℤ) (x : K.X p) :
    singleDoubleDualTermEquiv K W e p
        (evaluationComponent K ((singleFunctor (ModuleCat.{max u v} R) 0).obj W) p x) =
      (p * (-p)).negOnePow • Module.Dual.eval R (K.X p) x := by
  apply LinearMap.ext
  intro φ
  let D := moduleComplex R K ((singleFunctor (ModuleCat.{max u v} R) 0).obj W)
  let t := singleDualTermEquiv K W e p (-p) (add_neg_cancel p)
  change singleDualTermEquiv D W e (-p) p (neg_add_cancel p)
      (evaluationComponent K ((singleFunctor (ModuleCat.{max u v} R) 0).obj W) p x)
      (t.symm φ) = (p * (-p)).negOnePow • φ x
  rw [singleDualTermEquiv_apply, evaluationComponent_apply, moduleMap_units_smul]
  change e ((p * (-p)).negOnePow •
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 W).hom
        ((t.symm φ).v p 0 (add_neg_cancel p) x)) = _
  change e (((p * (-p)).negOnePow : ℤ) •
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 W).hom
        ((t.symm φ).v p 0 (add_neg_cancel p) x)) =
    ((p * (-p)).negOnePow : ℤ) • φ x
  rw [map_zsmul]
  change (p * (-p)).negOnePow • (t (t.symm φ)) x = (p * (-p)).negOnePow • φ x
  rw [LinearEquiv.apply_symm_apply]

/-- Finite-projective module reflexivity makes the original
single-coefficient evaluation invertible. -/
theorem evaluation_single_isIso (K : CochainComplex (ModuleCat.{max u v} R) ℤ)
    (W : ModuleCat.{max u v} R) (e : W ≃ₗ[R] R)
    [∀ p, Module.Finite R (K.X p)] [∀ p, Module.Projective R (K.X p)] :
    IsIso (evaluation K ((singleFunctor (ModuleCat.{max u v} R) 0).obj W)) := by
  have (p : ℤ) : IsIso
      ((evaluation K ((singleFunctor (ModuleCat.{max u v} R) 0).obj W)).f p) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    let t := singleDoubleDualTermEquiv K W e p
    apply (Function.Bijective.of_comp_iff' t.bijective _).mp
    change Function.Bijective (fun x : K.X p => t
      (evaluationComponent K ((singleFunctor (ModuleCat.{max u v} R) 0).obj W) p x))
    have ht : (fun x : K.X p => t
        (evaluationComponent K ((singleFunctor (ModuleCat.{max u v} R) 0).obj W) p x)) =
        (fun y : Module.Dual R (Module.Dual R (K.X p)) => (p * (-p)).negOnePow • y) ∘
          Module.Dual.eval R (K.X p) := by
      funext x
      rw [Function.comp_apply]
      exact singleDoubleDualTermEquiv_evaluation K W e p x
    rw [ht]
    exact (MulAction.bijective ((p * (-p)).negOnePow)).comp
      (Module.bijective_dual_eval R (K.X p))
  exact HomologicalComplex.Hom.isIso_of_components _

/-- Each original single-dual term of a finite-projective complex is finite projective. -/
theorem singleDual_finite_projective (K : CochainComplex (ModuleCat.{max u v} R) ℤ)
    (W : ModuleCat.{max u v} R) (e : W ≃ₗ[R] R)
    [∀ p, Module.Finite R (K.X p)] [∀ p, Module.Projective R (K.X p)] (n : ℤ) :
    Module.Finite R ((moduleComplex R K ((singleFunctor (ModuleCat.{max u v} R) 0).obj W)).X n) ∧
      Module.Projective R
        ((moduleComplex R K ((singleFunctor (ModuleCat.{max u v} R) 0).obj W)).X n) := by
  let t := singleDualTermEquiv K W e (-n) n (neg_add_cancel n)
  exact ⟨Module.Finite.equiv t.symm, Module.Projective.of_equiv' t.symm⟩

/-- The lower term bound of the original complex is the upper bound of its single dual. -/
theorem singleDual_isStrictlyLE (K : CochainComplex (ModuleCat.{max u v} R) ℤ)
    (W : ModuleCat.{max u v} R) (e : W ≃ₗ[R] R) (a : ℤ) [K.IsStrictlyGE a] :
    (moduleComplex R K ((singleFunctor (ModuleCat.{max u v} R) 0).obj W)).IsStrictlyLE (-a) := by
  rw [isStrictlyLE_iff]
  intro n hn
  let : Subsingleton (K.X (-n)) :=
    ModuleCat.subsingleton_of_isZero (K.isZero_of_isStrictlyGE a (-n) (by omega))
  apply ModuleCat.isZero_iff_subsingleton.mpr
  exact ⟨fun x y => (singleDualTermEquiv K W e (-n) n (neg_add_cancel n)).injective
    (Subsingleton.elim _ _)⟩

/-- No evaluation-isomorphism premise: the original augmentation and finite projective
terms prove quasi-isomorphism of this very signed evaluation. -/
theorem evaluation_quasiIso_of_finite_projective
    (P : CochainComplex (ModuleCat.{max u v} R) ℤ)
    (W : ModuleCat.{max u v} R) (e : W ≃ₗ[R] R)
    (I : CochainComplex (ModuleCat.{max u v} R) ℤ) [I.IsKInjective]
    (u : ((singleFunctor (ModuleCat.{max u v} R) 0).obj W) ⟶ I) [QuasiIso u]
    (a b : ℤ) [P.IsStrictlyGE a] [P.IsStrictlyLE b]
    [∀ p, Module.Finite R (P.X p)] [∀ p, Module.Projective R (P.X p)] :
    QuasiIso (evaluation P I) := by
  let := HasDerivedCategory.standard (ModuleCat.{max u v} R)
  let S := (singleFunctor (ModuleCat.{max u v} R) 0).obj W
  let D := moduleComplex R P S
  let : P.IsKProjective := isKProjective_of_projective P b
  let (n : ℤ) : Module.Projective R (D.X n) := (singleDual_finite_projective P W e n).2
  let : D.IsStrictlyLE (-a) := singleDual_isStrictlyLE P W e a
  let : D.IsKProjective := isKProjective_of_projective D (-a)
  let f : D ⟶ moduleComplex R P I := postcomp R P u
  let : QuasiIso f := postcomp_quasiIso R P u
  let : QuasiIso (precomp R f I) := precomp_quasiIso R f I
  let : IsIso (evaluation P S) := evaluation_single_isIso P W e
  let : QuasiIso (postcomp R D u) := postcomp_quasiIso R D u
  have h : QuasiIso (evaluation P I ≫ precomp R f I) := by
    change QuasiIso (evaluation P I ≫ precomp R (postcomp R P u) I)
    rw [evaluation_coefficient_naturality]
    infer_instance
  exact (quasiIso_iff_comp_right _ _).mp h

/-- A displayed finite-projective model proves quasi-isomorphism of
the original evaluation on its target. -/
theorem evaluation_quasiIso_of_model
    (P L : CochainComplex (ModuleCat.{max u v} R) ℤ)
    (W : ModuleCat.{max u v} R) (e : W ≃ₗ[R] R)
    (I : CochainComplex (ModuleCat.{max u v} R) ℤ) [I.IsKInjective]
    (u : ((singleFunctor (ModuleCat.{max u v} R) 0).obj W) ⟶ I) [QuasiIso u]
    (a b : ℤ) [P.IsStrictlyGE a] [P.IsStrictlyLE b]
    [∀ p, Module.Finite R (P.X p)] [∀ p, Module.Projective R (P.X p)]
    (q : P ⟶ L) [QuasiIso q] : QuasiIso (evaluation L I) := by
  let := HasDerivedCategory.standard (ModuleCat.{max u v} R)
  let : QuasiIso (evaluation P I) := evaluation_quasiIso_of_finite_projective P W e I u a b
  let : QuasiIso (precomp R q I) := precomp_quasiIso R q I
  let : QuasiIso (precomp R (precomp R q I) I) := precomp_quasiIso R (precomp R q I) I
  have h : QuasiIso (q ≫ evaluation L I) := by
    rw [evaluation_naturality]
    infer_instance
  exact (quasiIso_iff_comp_left _ _).mp h

end FiniteProjective

section CoinducedEvaluation

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] (σ : R →+* A)

/-- Restriction is used only to reflect quasi-isomorphism of the original A-map. -/
theorem evaluation_coinduced_quasiIso_of_model
    (K : CochainComplex (ModuleCat.{max u v w} A) ℤ)
    (P : CochainComplex (ModuleCat.{max u v w} R) ℤ)
    (W : ModuleCat.{max u v w} R) (e : W ≃ₗ[R] R)
    (I : CochainComplex (ModuleCat.{max u v w} R) ℤ) [I.IsKInjective]
    (u : ((singleFunctor (ModuleCat.{max u v w} R) 0).obj W) ⟶ I) [QuasiIso u]
    (a b : ℤ) [P.IsStrictlyGE a] [P.IsStrictlyLE b]
    [∀ p, Module.Finite R (P.X p)] [∀ p, Module.Projective R (P.X p)]
    (q : P ⟶ ((ModuleCat.restrictScalars σ).mapHomologicalComplex (.up ℤ)).obj K)
    [QuasiIso q] :
    QuasiIso (evaluation K
      (((ModuleCat.coextendScalars σ).mapHomologicalComplex (.up ℤ)).obj I)) := by
  let F : ModuleCat.{max u v w} A ⥤ ModuleCat.{max u v w} R :=
    ModuleCat.restrictScalars σ
  let J : CochainComplex (ModuleCat.{max u v w} A) ℤ :=
    ((ModuleCat.coextendScalars σ).mapHomologicalComplex (.up ℤ)).obj I
  let L : CochainComplex (ModuleCat.{max u v w} R) ℤ :=
    (F.mapHomologicalComplex (.up ℤ)).obj K
  let : QuasiIso (evaluation L I) :=
    evaluation_quasiIso_of_model.{u, max v w} P L W e I u a b q
  have h : QuasiIso
      ((F.mapHomologicalComplex (.up ℤ)).map (evaluation K J) ≫
        (coinductionDoubleComplexIso.{u, v, max u w} σ K I).hom) := by
    rw [coinductionDoubleComplexIso_evaluation.{u, v, max u w}]
    infer_instance
  let : QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map (evaluation K J)) :=
    (quasiIso_iff_comp_right _ _).mp h
  exact (HomologicalComplex.quasiIso_map_iff_of_preservesHomology (evaluation K J) F).mp
    inferInstance

/-- The already constructed genuine A-derived evaluation is invertible on this
actual representative. The K-injective coinduced coefficient is supplied by the
chosen ordinary injective resolution, independently of perfectness. -/
theorem derivedEvaluation_app_Q_isIso_of_model
    [HasDerivedCategory.{z} (ModuleCat.{max u v w} A)]
    (K : CochainComplex (ModuleCat.{max u v w} A) ℤ)
    (P : CochainComplex (ModuleCat.{max u v w} R) ℤ)
    (W : ModuleCat.{max u v w} R) (e : W ≃ₗ[R] R)
    (I : CochainComplex (ModuleCat.{max u v w} R) ℤ) [I.IsKInjective]
    [CochainComplex.IsKInjective
      (show CochainComplex (ModuleCat.{max u v w} A) ℤ from
        ((ModuleCat.coextendScalars σ).mapHomologicalComplex (.up ℤ)).obj I)]
    (u : ((singleFunctor (ModuleCat.{max u v w} R) 0).obj W) ⟶ I) [QuasiIso u]
    (a b : ℤ) [P.IsStrictlyGE a] [P.IsStrictlyLE b]
    [∀ p, Module.Finite R (P.X p)] [∀ p, Module.Projective R (P.X p)]
    (q : P ⟶ ((ModuleCat.restrictScalars σ).mapHomologicalComplex (.up ℤ)).obj K)
    [QuasiIso q] :
    IsIso ((derivedEvaluation
      (((ModuleCat.coextendScalars σ).mapHomologicalComplex (.up ℤ)).obj I)).app
        (DerivedCategory.Q.obj K)) := by
  let J : CochainComplex (ModuleCat.{max u v w} A) ℤ :=
    ((ModuleCat.coextendScalars σ).mapHomologicalComplex (.up ℤ)).obj I
  let : QuasiIso (evaluation K J) :=
    evaluation_coinduced_quasiIso_of_model.{u, v, w} σ K P W e I u a b q
  rw [derivedEvaluation_app_Q]
  infer_instance

/-- Naturality transports invertibility to an actual derived object while
retaining the original component of derivedEvaluation at that object. -/
theorem derivedEvaluation_isIso_of_model
    [HasDerivedCategory.{z} (ModuleCat.{max u v w} A)]
    (K : CochainComplex (ModuleCat.{max u v w} A) ℤ)
    (P : CochainComplex (ModuleCat.{max u v w} R) ℤ)
    (W : ModuleCat.{max u v w} R) (e : W ≃ₗ[R] R)
    (I : CochainComplex (ModuleCat.{max u v w} R) ℤ) [I.IsKInjective]
    [CochainComplex.IsKInjective
      (show CochainComplex (ModuleCat.{max u v w} A) ℤ from
        ((ModuleCat.coextendScalars σ).mapHomologicalComplex (.up ℤ)).obj I)]
    (u : ((singleFunctor (ModuleCat.{max u v w} R) 0).obj W) ⟶ I) [QuasiIso u]
    (a b : ℤ) [P.IsStrictlyGE a] [P.IsStrictlyLE b]
    [∀ p, Module.Finite R (P.X p)] [∀ p, Module.Projective R (P.X p)]
    (q : P ⟶ ((ModuleCat.restrictScalars σ).mapHomologicalComplex (.up ℤ)).obj K)
    [QuasiIso q] (T : DerivedCategory (ModuleCat.{max u v w} A))
    (eK : DerivedCategory.Q.obj K ≅ T) :
    IsIso ((derivedEvaluation
      (((ModuleCat.coextendScalars σ).mapHomologicalComplex (.up ℤ)).obj I)).app T) := by
  let J : CochainComplex (ModuleCat.{max u v w} A) ℤ :=
    ((ModuleCat.coextendScalars σ).mapHomologicalComplex (.up ℤ)).obj I
  let D := (derivedDual J).rightOp ⋙ derivedDual J
  let : IsIso ((derivedEvaluation J).app (DerivedCategory.Q.obj K)) :=
    derivedEvaluation_app_Q_isIso_of_model.{u, v, w, z} σ K P W e I u a b q
  have he := (derivedEvaluation J).naturality eK.hom
  change eK.hom ≫ (derivedEvaluation J).app T =
    (derivedEvaluation J).app (DerivedCategory.Q.obj K) ≫ D.map eK.hom at he
  have : IsIso (eK.hom ≫ (derivedEvaluation J).app T) := by
    rw [he]
    infer_instance
  exact IsIso.of_isIso_comp_left eK.hom ((derivedEvaluation J).app T)

end CoinducedEvaluation

end CochainComplex.HomComplex
