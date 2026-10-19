/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Grassmannian.Quotient.BaseChange
public import Aglib.AlgebraicGeometry.Grassmannian.FunctorOfPoints

/-!
# Grassmannian points of locally free quotients

For an `R`-algebra `A`, every rank-`k` locally free quotient of `O^n` on `Spec A` is isomorphic to
`pointQuot A N` for exactly one point `N` of Mathlib's Grassmannian `G(k, A ⊗[R] R^n; A)`;
`affinePoint A` is the resulting bijection on isomorphism classes (`affinePoint_bijective`), and
it commutes with base change (`affinePoint_pullback`).

For a scheme `T` over `Spec R`, a class `q` of quotients on `T` gives the natural transformation
`toPointsNatTrans T q : algSpecPoints T ⟶ Module.Grassmannian.functor k`,
`(v : Spec A ⟶ T) ↦ affinePoint A (v^* q)`. These form the natural transformation
`toLocalFunctor R k n : quotFunctor R k n ⟶ Grassmannian.localFunctor R k n`.

All statements assume the named premise `Module.Grassmannian.BaseChangeMkQFormula`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite Limits TensorProduct

namespace AlgebraicGeometry.Grassmannian

open Scheme.Modules LocallyFreeQuotient

variable {R : CommRingCat.{u}} {k n : ℕ}

set_option hygiene false in
/-- Mathlib's Grassmannian functor `A ↦ G(k, A ⊗[R] (Fin n → R); A)` on `R`-algebras. -/
local notation "𝐆" => Module.Grassmannian.functor.{u, u, u} (R := R) (M := Fin n → R) k

/-- The Grassmannian point of a class of locally free quotients on `Spec A`. -/
def affinePoint (A : CommAlgCat.{u} R) :
    Quotient (LocallyFreeQuotient.setoid (Spec (CommRingCat.of A)) k n) →
      Module.Grassmannian A (A ⊗[R] (Fin n → R)) k :=
  Quotient.lift
    (fun P ↦ (exists_tildeQuot_equiv (A := CommRingCat.of A) (tensorBasis A) P).choose)
    (fun P P' h ↦ eq_of_tildeQuot_equiv (A := CommRingCat.of A) (tensorBasis A)
      (Setoid.trans
        (Setoid.symm (exists_tildeQuot_equiv (A := CommRingCat.of A) (tensorBasis A) P).choose_spec)
        (Setoid.trans h
          (exists_tildeQuot_equiv (A := CommRingCat.of A) (tensorBasis A) P').choose_spec)))

theorem equiv_pointQuot_affinePoint (A : CommAlgCat.{u} R)
    (P : LocallyFreeQuotient (Spec (CommRingCat.of A)) k n) :
    P ≈ pointQuot A (affinePoint A (Quotient.mk _ P)) :=
  (exists_tildeQuot_equiv (A := CommRingCat.of A) (tensorBasis A) P).choose_spec

theorem affinePoint_pointQuot (A : CommAlgCat.{u} R)
    (N : Module.Grassmannian A (A ⊗[R] (Fin n → R)) k) :
    affinePoint A (Quotient.mk _ (pointQuot A N)) = N :=
  eq_of_tildeQuot_equiv (A := CommRingCat.of A) (tensorBasis A)
    (Setoid.symm (equiv_pointQuot_affinePoint A _))

theorem affinePoint_mk_eq_iff (A : CommAlgCat.{u} R)
    (P P' : LocallyFreeQuotient (Spec (CommRingCat.of A)) k n) :
    affinePoint A (Quotient.mk _ P) = affinePoint A (Quotient.mk _ P') ↔ P ≈ P' := by
  refine ⟨fun h ↦ Setoid.trans (equiv_pointQuot_affinePoint A P) ?_, fun h ↦ ?_⟩
  · rw [h]
    exact Setoid.symm (equiv_pointQuot_affinePoint A P')
  · exact congrArg (affinePoint A) (Quotient.sound h)

/-- **Quotients on `Spec A` are Grassmannian points.** -/
theorem affinePoint_bijective (A : CommAlgCat.{u} R) :
    Function.Bijective (affinePoint (k := k) (n := n) A) := by
  refine ⟨fun x y h ↦ ?_, fun N ↦ ⟨_, affinePoint_pointQuot A N⟩⟩
  induction x using Quotient.inductionOn with | h P =>
  induction y using Quotient.inductionOn with | h P' =>
  exact Quotient.sound ((affinePoint_mk_eq_iff A P P').mp h)

variable [Module.Grassmannian.BaseChangeMkQFormula.{u, u, u} R (Fin n → R)]

/-- `affinePoint` commutes with base change. -/
theorem affinePoint_pullback {A B : CommAlgCat.{u} R} (f : A ⟶ B)
    (P : LocallyFreeQuotient (Spec (CommRingCat.of A)) k n) :
    affinePoint B (Quotient.mk _ (P.pullback (Spec.map (CommRingCat.ofHom (f.hom : A →+* B))))) =
      Module.Grassmannian.map f.hom (affinePoint A (Quotient.mk _ P)) := by
  obtain ⟨e⟩ := equiv_pointQuot_affinePoint A P
  rw [← affinePoint_pointQuot B (Module.Grassmannian.map f.hom (affinePoint A (Quotient.mk _ P)))]
  exact congrArg (affinePoint B) (Quotient.sound
    (Setoid.trans ⟨e.pullback _⟩ (pullback_pointQuot f _)))

/-- The Grassmannian points of a class of quotients on `T`,
`(v : Spec A ⟶ T) ↦ affinePoint A (v^* q)`, as a natural transformation from the functor of
points of `T` on `R`-algebras. -/
def toPointsNatTrans (T : Over (Spec R)) (q : (quotFunctor R k n).obj (op T)) :
    algSpecPoints T ⟶ 𝐆 where
  app A := TypeCat.ofHom fun v ↦ affinePoint A ((quotFunctor R k n).map v.op q)
  naturality A B f := by
    ext v
    change affinePoint B ((quotFunctor R k n).map ((algSpec R).map f.op ≫ v).op q) =
      Module.Grassmannian.map f.hom (affinePoint A ((quotFunctor R k n).map v.op q))
    rw [op_comp, CategoryTheory.Functor.map_comp_apply]
    generalize (quotFunctor R k n).map v.op q = x
    induction x using Quotient.inductionOn with | h P =>
    exact affinePoint_pullback f P

theorem toPointsNatTrans_app (T : Over (Spec R)) (q : (quotFunctor R k n).obj (op T))
    (A : CommAlgCat.{u} R) (v : (algSpec R).obj (op A) ⟶ T) :
    (toPointsNatTrans T q).app A v = affinePoint A ((quotFunctor R k n).map v.op q) := rfl

variable (R k n) in
/-- **Quotients give Grassmannian points**: the natural transformation
`Quot_k(O^n) ⟶ localFunctor R k n`, `q ↦ toPointsNatTrans T q`. -/
def toLocalFunctor : quotFunctor R k n ⟶ localFunctor R k n where
  app T := TypeCat.ofHom fun q ↦ toPointsNatTrans T.unop q
  naturality T T' t := by
    ext q
    refine NatTrans.ext (funext fun A ↦ ?_)
    ext v
    change affinePoint A ((quotFunctor R k n).map v.op ((quotFunctor R k n).map t q)) =
      affinePoint A ((quotFunctor R k n).map (v ≫ t.unop).op q)
    rw [op_comp, Quiver.Hom.op_unop, CategoryTheory.Functor.map_comp_apply]

theorem toLocalFunctor_app (T : (Over (Spec R))ᵒᵖ) (q : (quotFunctor R k n).obj T) :
    (toLocalFunctor R k n).app T q = toPointsNatTrans T.unop q := rfl

end AlgebraicGeometry.Grassmannian
