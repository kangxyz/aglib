/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.ModuleCat.HomComplex
public import Mathlib.Tactic.Ring

/-!
# Signed evaluation on the actual module-valued Hom complex

The evaluation is an original A-linear chain map before any scalar
restriction or localization. No projectivity, finiteness, K-injectivity or
evaluation-isomorphism premise is imposed on this construction.
-/

@[expose] public section
noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive Opposite

universe u v

namespace CochainComplex.HomComplex

variable {A : Type u} [CommRing A]

private theorem map_units_int_smul {M N : ModuleCat.{v} A} (f : M ⟶ N)
    (s : ℤˣ) (x : M) : f (s • x) = s • f x := by
  change f.hom ((s : ℤ) • x) = (s : ℤ) • f.hom x
  exact map_zsmul f.hom (s : ℤ) x

/-- Signed evaluation in degree p, using the original native Hom cochains. -/
def evaluationComponent (K J : CochainComplex (ModuleCat.{v} A) ℤ) (p : ℤ) :
    K.X p ⟶ (moduleComplex A (moduleComplex A K J) J).X p :=
  ModuleCat.ofHom
    { toFun := fun x => Cochain.mk fun q r hqr => ModuleCat.ofHom
        { toFun := fun φ => (p * q).negOnePow • (φ.v p r (by omega)) x
          map_add' := fun φ ψ => by
            change (p * q).negOnePow • ((φ.v p r (by omega)) x + (ψ.v p r (by omega)) x) = _
            exact smul_add _ _ _
          map_smul' := fun a φ => by
            change (p * q).negOnePow • (a • (φ.v p r (by omega)) x) =
              a • ((p * q).negOnePow • (φ.v p r (by omega)) x)
            exact smul_comm _ _ _ }
      map_add' := fun x y => by
        ext q r hqr φ
        change (p * q).negOnePow • (φ.v p r (by omega)) (x + y) = _
        rw [map_add, smul_add]
        rfl
      map_smul' := fun a x => by
        ext q r hqr φ
        change (p * q).negOnePow • (φ.v p r (by omega)) (a • x) = _
        rw [map_smul]
        exact smul_comm _ _ _ }

/-- The actual evaluation component includes the Koszul sign (-1)^(p*q). -/
@[simp]
theorem evaluationComponent_apply (K J : CochainComplex (ModuleCat.{v} A) ℤ)
    (p : ℤ) (x : K.X p) (q r : ℤ) (hqr : q + p = r) (φ : Cochain K J q) :
    ((evaluationComponent K J p x).v q r hqr) φ =
      (p * q).negOnePow • (φ.v p r (by omega)) x := rfl

private theorem evaluation_sign_identity {M : Type*} [AddCommGroup M]
    (p q : ℤ) (z y : M) :
    (p * q).negOnePow • z +
        (p + 1).negOnePow • ((p * (q + 1)).negOnePow •
          (z + (q + 1).negOnePow • y)) =
      ((p + 1) * q).negOnePow • y := by
  have hcancel : (p + 1).negOnePow * (p * (q + 1)).negOnePow =
      -(p * q).negOnePow := by
    rw [← Int.negOnePow_add, ← Int.negOnePow_succ]
    apply (Int.negOnePow_eq_iff _ _).mpr
    exact ⟨p, by ring⟩
  have hkeep : (p + 1).negOnePow * (p * (q + 1)).negOnePow *
        (q + 1).negOnePow = ((p + 1) * q).negOnePow := by
    rw [← Int.negOnePow_add, ← Int.negOnePow_add]
    apply (Int.negOnePow_eq_iff _ _).mpr
    exact ⟨p + 1, by ring⟩
  simp only [smul_add, smul_smul, ← mul_assoc]
  rw [hkeep, hcancel, Units.neg_smul]
  abel

/-- The sign in the evaluation is exactly the one making it commute with
the original Hom differential. -/
theorem evaluationComponent_delta (K J : CochainComplex (ModuleCat.{v} A) ℤ)
    (p : ℤ) (x : K.X p) :
    δ p (p + 1) (evaluationComponent K J p x) =
      evaluationComponent K J (p + 1) (K.d p (p + 1) x) := by
  ext q r hqr φ
  rw [δ_v p (p + 1) rfl _ q r hqr (p + q) (q + 1) (by omega) rfl]
  change J.d (p + q) r ((p * q).negOnePow • (φ.v p (p + q) rfl) x) +
      (p + 1).negOnePow • ((p * (q + 1)).negOnePow •
        ((δ q (q + 1) φ).v p r (by omega)) x) =
    ((p + 1) * q).negOnePow • (φ.v (p + 1) r (by omega)) (K.d p (p + 1) x)
  rw [map_units_int_smul]
  have hinner := congrArg (fun f : K.X p ⟶ J.X r => f x)
    (δ_v q (q + 1) rfl φ p r (by omega) (p + q) (p + 1) (by omega) rfl)
  change ((δ q (q + 1) φ).v p r (by omega)) x =
    J.d (p + q) r ((φ.v p (p + q) rfl) x) +
      (q + 1).negOnePow • (φ.v (p + 1) r (by omega)) (K.d p (p + 1) x) at hinner
  rw [hinner]
  exact evaluation_sign_identity p q _ _

/-- Genuine A-linear signed evaluation on an actual complex. -/
def evaluation (K J : CochainComplex (ModuleCat.{v} A) ℤ) :
    K ⟶ moduleComplex A (moduleComplex A K J) J where
  f p := evaluationComponent K J p
  comm' p p' hpp' := by
    have hp : p + 1 = p' := hpp'
    subst p'
    apply ConcreteCategory.hom_ext
    intro x
    exact evaluationComponent_delta K J p x

/-- Naturality holds for the original A-linear chain maps, before localization. -/
@[reassoc]
theorem evaluation_naturality {K L : CochainComplex (ModuleCat.{v} A) ℤ}
    (f : K ⟶ L) (J : CochainComplex (ModuleCat.{v} A) ℤ) :
    f ≫ evaluation L J =
      evaluation K J ≫ precomp A (precomp A f J) J := by
  apply HomologicalComplex.hom_ext
  intro p
  apply ConcreteCategory.hom_ext
  intro x
  apply Cochain.ext
  intro q r hqr
  apply ConcreteCategory.hom_ext
  intro φ
  change ((evaluationComponent L J p (f.f p x)).v q r hqr) φ =
    (((Cochain.ofHom (precomp A f J)).comp
      (evaluationComponent K J p x) (zero_add p)).v q r hqr) φ
  rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v]
  change ((evaluationComponent L J p (f.f p x)).v q r hqr) φ =
    ((evaluationComponent K J p x).v q r hqr) ((precomp A f J).f q φ)
  rw [evaluationComponent_apply, evaluationComponent_apply, precomp_f_apply,
    Cochain.zero_cochain_comp_v, Cochain.ofHom_v]
  rfl

/-- The genuine chain-level evaluation, with its actual double-Hom target functor. -/
def evaluationNatTrans (J : CochainComplex (ModuleCat.{v} A) ℤ) :
    𝟭 (CochainComplex (ModuleCat.{v} A) ℤ) ⟶
      (moduleComplexFunctor A J).rightOp ⋙ moduleComplexFunctor A J where
  app K := evaluation K J
  naturality {X Y} f := evaluation_naturality (K := X) (L := Y) f J

end CochainComplex.HomComplex
