/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.ModuleCat.HomComplex.Evaluation
public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Coinduction
public import Aglib.Algebra.Homology.HomologicalComplex.Adjunction

/-!
# Coinduction on the actual module-valued Hom complex

Each original cochain is adjointed by evaluation at one. Its inverse sends
h to the functional x ↦ (a ↦ h(a*x)). The isomorphism is over the original
source ring and retains target-ring multiplication through its original
action on the source complex. No projectivity or duality hypothesis is used.
-/

@[expose] public section
noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive

universe u v w

namespace CochainComplex.HomComplex

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] (σ : R →+* A)

/-- The actual coinduction Hom adjunction on every original homogeneous cochain,
linear for the original restricted R-action. -/
def coinductionCochainEquiv
    (K : CochainComplex (ModuleCat.{max v w} A) ℤ)
    (I : CochainComplex (ModuleCat.{max v w} R) ℤ) (n : ℤ) :
    (ModuleCat.restrictScalars σ).obj
        ((moduleComplex A K
          (((ModuleCat.coextendScalars σ).mapHomologicalComplex (.up ℤ)).obj I)).X n) ≃ₗ[R]
      Cochain (((ModuleCat.restrictScalars σ).mapHomologicalComplex (.up ℤ)).obj K) I n where
  toFun φ := Cochain.mk fun p q hpq =>
    ModuleCat.RestrictionCoextensionAdj.HomEquiv.toRestriction σ (φ.v p q hpq)
  invFun ψ := Cochain.mk fun p q hpq =>
    ModuleCat.RestrictionCoextensionAdj.HomEquiv.fromRestriction σ (ψ.v p q hpq)
  left_inv φ := by
    apply Cochain.ext
    intro p q hpq
    apply ConcreteCategory.hom_ext
    intro x
    apply (ModuleCat.CoextendScalars.equiv σ (I.X q)).injective
    apply LinearMap.ext
    intro a
    change ModuleCat.CoextendScalars.equiv σ (I.X q)
        ((φ.v p q hpq).hom ((show A from a) • x)) (1 : A) =
      ModuleCat.CoextendScalars.equiv σ (I.X q) ((φ.v p q hpq).hom x) a
    rw [(φ.v p q hpq).hom.map_smul]
    change ModuleCat.CoextendScalars.equiv σ (I.X q)
        ((φ.v p q hpq).hom x) ((1 : A) * (show A from a)) = _
    rw [one_mul]
  right_inv ψ := by
    apply Cochain.ext
    intro p q hpq
    apply ConcreteCategory.hom_ext
    intro x
    change (ψ.v p q hpq).hom ((1 : A) • (show K.X p from x)) = (ψ.v p q hpq).hom x
    rw [one_smul]
  map_add' φ ψ := by
    ext p q hpq x
    rfl
  map_smul' r φ := by
    ext p q hpq x
    change ModuleCat.CoextendScalars.equiv σ (I.X q) (σ r • ((φ.v p q hpq).hom x)) (1 : A) =
      r • ModuleCat.CoextendScalars.equiv σ (I.X q) ((φ.v p q hpq).hom x) (1 : A)
    change ModuleCat.CoextendScalars.equiv σ (I.X q) ((φ.v p q hpq).hom x) ((1 : A) * σ r) = _
    rw [one_mul]
    have h := (ModuleCat.CoextendScalars.equiv σ (I.X q)
      ((φ.v p q hpq).hom x)).map_smul r (1 : A)
    change ModuleCat.CoextendScalars.equiv σ (I.X q)
        ((φ.v p q hpq).hom x) (σ r * (1 : A)) =
      r • ModuleCat.CoextendScalars.equiv σ (I.X q)
        ((φ.v p q hpq).hom x) (1 : A) at h
    simpa only [mul_one] using h

/-- Every original homogeneous component is sent to evaluation at one. -/
theorem coinductionCochainEquiv_apply
    (K : CochainComplex (ModuleCat.{max v w} A) ℤ)
    (I : CochainComplex (ModuleCat.{max v w} R) ℤ) (n : ℤ)
    (φ : Cochain K (((ModuleCat.coextendScalars σ).mapHomologicalComplex (.up ℤ)).obj I) n)
    (p q : ℤ) (hpq : p + n = q) (x : K.X p) :
    ((coinductionCochainEquiv σ K I n φ).v p q hpq) x =
      ModuleCat.CoextendScalars.equiv σ (I.X q) (φ.v p q hpq x) (1 : A) := rfl

/-- The inverse acts on the original source by actual A-multiplication. -/
theorem coinductionCochainEquiv_symm_apply
    (K : CochainComplex (ModuleCat.{max v w} A) ℤ)
    (I : CochainComplex (ModuleCat.{max v w} R) ℤ) (n : ℤ)
    (ψ : Cochain (((ModuleCat.restrictScalars σ).mapHomologicalComplex (.up ℤ)).obj K) I n)
    (p q : ℤ) (hpq : p + n = q) (x : K.X p) (a : A) :
    ModuleCat.CoextendScalars.equiv σ (I.X q)
        (((coinductionCochainEquiv σ K I n).symm ψ).v p q hpq x) a =
      (ψ.v p q hpq) (a • x) := rfl

/-- Target-ring multiplication on the coinduced Hom complex is original
source multiplication after the R-linear cochain comparison. -/
theorem coinductionCochainEquiv_smul_apply
    (K : CochainComplex (ModuleCat.{max v w} A) ℤ)
    (I : CochainComplex (ModuleCat.{max v w} R) ℤ) (n : ℤ)
    (φ : Cochain K (((ModuleCat.coextendScalars σ).mapHomologicalComplex (.up ℤ)).obj I) n)
    (a : A) (p q : ℤ) (hpq : p + n = q) (x : K.X p) :
    ((coinductionCochainEquiv σ K I n (a • φ)).v p q hpq) x =
      ((coinductionCochainEquiv σ K I n φ).v p q hpq) (a • x) := by
  change ModuleCat.CoextendScalars.equiv σ (I.X q) (a • ((φ.v p q hpq).hom x)) (1 : A) =
    ModuleCat.CoextendScalars.equiv σ (I.X q) ((φ.v p q hpq).hom (a • x)) (1 : A)
  rw [(φ.v p q hpq).hom.map_smul]

/-- The component formula is original scalar restriction followed by the
original adjunction counit, expressed as an equality of native R-module maps. -/
theorem coinductionCochainEquiv_component
    (K : CochainComplex (ModuleCat.{max v w} A) ℤ)
    (I : CochainComplex (ModuleCat.{max v w} R) ℤ) (n : ℤ)
    (φ : Cochain K (((ModuleCat.coextendScalars σ).mapHomologicalComplex (.up ℤ)).obj I) n)
    (p q : ℤ) (hpq : p + n = q) :
    (coinductionCochainEquiv σ K I n φ).v p q hpq =
      (ModuleCat.restrictScalars σ).map (φ.v p q hpq) ≫
        (ModuleCat.restrictCoextendScalarsAdj.{w,u,v} σ).counit.app (I.X q) := by
  apply ConcreteCategory.hom_ext
  intro x
  rfl

/-- The actual mapped adjunction counit has the original R-module counit
as its degree-q component. -/
theorem coinductionAdjunction_counit_f
    (I : CochainComplex (ModuleCat.{max v w} R) ℤ) (q : ℤ) :
    (((ModuleCat.restrictCoextendScalarsAdj.{w,u,v} σ).mapHomologicalComplex
      (.up ℤ)).counit.app I).f q =
      (ModuleCat.restrictCoextendScalarsAdj.{w,u,v} σ).counit.app (I.X q) := by
  simp only [CategoryTheory.Adjunction.mapHomologicalComplex]

/-- The same original cochain map is restriction followed by the original
chain counit. This expression retains its actual cochain composition. -/
theorem coinductionCochainEquiv_eq_map_comp
    (K : CochainComplex (ModuleCat.{max v w} A) ℤ)
    (I : CochainComplex (ModuleCat.{max v w} R) ℤ) (n : ℤ)
    (φ : Cochain K (((ModuleCat.coextendScalars σ).mapHomologicalComplex (.up ℤ)).obj I) n) :
    coinductionCochainEquiv σ K I n φ =
      (φ.map (ModuleCat.restrictScalars σ)).comp
        (Cochain.ofHom
          (((ModuleCat.restrictCoextendScalarsAdj.{w,u,v} σ).mapHomologicalComplex
            (.up ℤ)).counit.app I)) (add_zero n) := by
  apply Cochain.ext
  intro p q hpq
  simpa only [Cochain.comp_zero_cochain_v, Cochain.ofHom_v, Cochain.map_v,
    coinductionAdjunction_counit_f] using
    coinductionCochainEquiv_component σ K I n φ p q hpq

/-- The original cochain adjunction commutes with the native Hom differential. -/
theorem coinductionCochainEquiv_delta
    (K : CochainComplex (ModuleCat.{max v w} A) ℤ)
    (I : CochainComplex (ModuleCat.{max v w} R) ℤ) (n m : ℤ)
    (φ : Cochain K (((ModuleCat.coextendScalars σ).mapHomologicalComplex (.up ℤ)).obj I) n) :
    coinductionCochainEquiv σ K I m (δ n m φ) =
      δ n m (coinductionCochainEquiv σ K I n φ) := by
  rw [coinductionCochainEquiv_eq_map_comp, coinductionCochainEquiv_eq_map_comp,
    δ_comp_ofHom, δ_map]

/-- The genuine A-valued Hom complex, restricted to R, is the original R-Hom
complex through the original evaluation-at-one chain isomorphism. -/
def coinductionComplexIso
    (K : CochainComplex (ModuleCat.{max v w} A) ℤ)
    (I : CochainComplex (ModuleCat.{max v w} R) ℤ) :
    ((ModuleCat.restrictScalars σ).mapHomologicalComplex (.up ℤ)).obj
        (moduleComplex A K
          (((ModuleCat.coextendScalars σ).mapHomologicalComplex (.up ℤ)).obj I)) ≅
      moduleComplex R
        (((ModuleCat.restrictScalars σ).mapHomologicalComplex (.up ℤ)).obj K) I :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (coinductionCochainEquiv σ K I n).toModuleIso) (by
      intro i j hij
      apply ConcreteCategory.hom_ext
      intro φ
      exact (coinductionCochainEquiv_delta σ K I i j φ).symm)

/-- Source naturality retains both original precomposition chain maps. -/
@[reassoc]
theorem coinductionComplexIso_naturality
    {K L : CochainComplex (ModuleCat.{max v w} A) ℤ} (f : K ⟶ L)
    (I : CochainComplex (ModuleCat.{max v w} R) ℤ) :
    ((ModuleCat.restrictScalars σ).mapHomologicalComplex (.up ℤ)).map
        (precomp A f (((ModuleCat.coextendScalars σ).mapHomologicalComplex (.up ℤ)).obj I)) ≫
      (coinductionComplexIso σ K I).hom =
    (coinductionComplexIso σ L I).hom ≫
      precomp R (((ModuleCat.restrictScalars σ).mapHomologicalComplex (.up ℤ)).map f) I := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro φ
  change coinductionCochainEquiv σ K I n ((Cochain.ofHom f).comp φ (zero_add n)) =
    (Cochain.ofHom (((ModuleCat.restrictScalars σ).mapHomologicalComplex (.up ℤ)).map f)).comp
      (coinductionCochainEquiv σ L I n φ) (zero_add n)
  rw [coinductionCochainEquiv_eq_map_comp, coinductionCochainEquiv_eq_map_comp,
    Cochain.map_comp, Cochain.map_ofHom, Cochain.comp_assoc_of_first_is_zero_cochain]

/-- The original coinduction comparison on double Hom, including the inverse
of the same first comparison in the contravariant source position. -/
def coinductionDoubleComplexIso
    (K : CochainComplex (ModuleCat.{max v w} A) ℤ)
    (I : CochainComplex (ModuleCat.{max v w} R) ℤ) :
    ((ModuleCat.restrictScalars σ).mapHomologicalComplex (.up ℤ)).obj
        (moduleComplex A
          (moduleComplex A K
            (((ModuleCat.coextendScalars σ).mapHomologicalComplex (.up ℤ)).obj I))
          (((ModuleCat.coextendScalars σ).mapHomologicalComplex (.up ℤ)).obj I)) ≅
      moduleComplex R
        (moduleComplex R
          (((ModuleCat.restrictScalars σ).mapHomologicalComplex (.up ℤ)).obj K) I) I :=
  coinductionComplexIso σ
      (moduleComplex A K (((ModuleCat.coextendScalars σ).mapHomologicalComplex (.up ℤ)).obj I)) I ≪≫
    (moduleComplexFunctor R I).mapIso (coinductionComplexIso σ K I).symm.op

private theorem coinduction_evaluate_one_units_smul
    (M : ModuleCat.{max v w} R) (s : ℤˣ) (z : (ModuleCat.coextendScalars σ).obj M) :
    ModuleCat.CoextendScalars.equiv σ M (s • z) (1 : A) =
      s • ModuleCat.CoextendScalars.equiv σ M z (1 : A) := by
  let e := (ModuleCat.restrictCoextendScalarsAdj.{w,u,v} σ).counit.app M
  change e.hom ((s : ℤ) • (show (ModuleCat.restrictScalars σ).obj
      ((ModuleCat.coextendScalars σ).obj M) from z)) = (s : ℤ) • e.hom z
  exact map_zsmul e.hom (s : ℤ) z

/-- The genuine A-linear signed evaluation becomes the original signed
R-evaluation under the actual coinduction comparison, with no change of source action. -/
theorem coinductionDoubleComplexIso_evaluation
    (K : CochainComplex (ModuleCat.{max v w} A) ℤ)
    (I : CochainComplex (ModuleCat.{max v w} R) ℤ) :
    ((ModuleCat.restrictScalars σ).mapHomologicalComplex (.up ℤ)).map
        (evaluation K (((ModuleCat.coextendScalars σ).mapHomologicalComplex (.up ℤ)).obj I)) ≫
      (coinductionDoubleComplexIso σ K I).hom =
    evaluation (((ModuleCat.restrictScalars σ).mapHomologicalComplex (.up ℤ)).obj K) I := by
  apply HomologicalComplex.hom_ext
  intro p
  apply ConcreteCategory.hom_ext
  intro x
  let J := ((ModuleCat.coextendScalars σ).mapHomologicalComplex (.up ℤ)).obj I
  change (Cochain.ofHom (coinductionComplexIso σ K I).inv).comp
      (coinductionCochainEquiv σ (moduleComplex A K J) I p
        (evaluationComponent K J p (show K.X p from x))) (zero_add p) =
    evaluationComponent
      (((ModuleCat.restrictScalars σ).mapHomologicalComplex (.up ℤ)).obj K) I p x
  apply Cochain.ext
  intro q r hqr
  apply ConcreteCategory.hom_ext
  intro φ
  rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v]
  change ((coinductionCochainEquiv σ (moduleComplex A K J) I p
      (evaluationComponent K J p (show K.X p from x))).v q r hqr)
      ((coinductionCochainEquiv σ K I q).symm φ) =
    ((evaluationComponent
      (((ModuleCat.restrictScalars σ).mapHomologicalComplex (.up ℤ)).obj K) I p x).v
      q r hqr) φ
  rw [coinductionCochainEquiv_apply, evaluationComponent_apply, evaluationComponent_apply,
    coinduction_evaluate_one_units_smul, coinductionCochainEquiv_symm_apply, one_smul]

end CochainComplex.HomComplex
