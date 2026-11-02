/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.Biproducts
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-! # Finite-product-stable properties of original finite abelian groups

The native finite cyclic decomposition and its actual projections bound every
factor by the given annihilator. Only finite underlying abelian groups occur.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped DirectSum

universe u

namespace AddCommGrpCat

section FiniteProducts

variable (P : ObjectProperty AddCommGrpCat.{u})
  [P.IsClosedUnderIsomorphisms] [P.IsClosedUnderFiniteProducts]

/-- A native finite cyclic decomposition transports a finite-product-stable
property back to the original group through the actual finite product. -/
theorem prop_of_zmod_directSum_equiv_of_finiteProducts {A : Type u} [AddCommGroup A]
    {ι : Type} [Finite ι] (m : ι → ℕ) (e : A ≃+ ⨁ i, ZMod (m i))
    (h : ∀ i, P (of (ULift.{u} (ZMod (m i))))) : P (of A) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let B : ι → AddCommGrpCat.{u} := fun i => of (ULift.{u} (ZMod (m i)))
  have hB : P (⨁ B) := P.prop_of_isLimit_fan (biproduct.isLimit B) h
  have hPi : P (of (∀ i, B i)) := P.prop_of_iso (biproductIsoPi B) hB
  let ePi : A ≃+ (∀ i, ULift.{u} (ZMod (m i))) :=
    e.trans ((DirectSum.addEquivProd (fun i => ZMod (m i))).trans
      (AddEquiv.piCongrRight fun _ => AddEquiv.ulift.symm))
  exact P.prop_of_iso ePi.toAddCommGrpIso.symm hPi

/-- Positive cyclic divisors of the original annihilator suffice for any
isomorphism- and finite-product-stable property of finite abelian groups. -/
theorem prop_of_finite_of_cyclic_divisors_of_finiteProducts (N : ℕ)
    (h : ∀ m : ℕ, 0 < m → m ∣ N → P (of (ULift.{u} (ZMod m))))
    (A : Type u) [AddCommGroup A] [Finite A] (hN : ∀ a : A, N • a = 0) :
    P (of A) := by
  classical
  obtain ⟨ι, hι, p, hp, r, ⟨e⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite A
  let := hι
  apply prop_of_zmod_directSum_equiv_of_finiteProducts P (fun i => p i ^ r i) e
  intro i
  have hs : Function.Surjective
      ((DFinsupp.evalAddMonoidHom i).comp e.toAddMonoidHom) := by
    intro a
    refine ⟨e.symm (DirectSum.of (fun j => ZMod (p j ^ r j)) i a), ?_⟩
    change (e (e.symm (DirectSum.of (fun j => ZMod (p j ^ r j)) i a))) i = a
    rw [e.apply_symm_apply]
    exact DirectSum.of_eq_same (β := fun j => ZMod (p j ^ r j)) i a
  have he : AddMonoid.exponent A ∣ N :=
    AddMonoid.exponent_dvd_iff_forall_nsmul_eq_zero.mpr hN
  have hd : p i ^ r i ∣ N := by
    rw [← ZMod.exponent (p i ^ r i)]
    exact (AddMonoidHom.exponent_dvd hs).trans he
  exact h (p i ^ r i) (pow_pos (hp i).pos _) hd


end FiniteProducts

variable (P : ObjectProperty AddCommGrpCat.{u})
  [P.ContainsZero] [P.IsClosedUnderIsomorphisms] [P.IsClosedUnderExtensions]

private theorem finiteProducts_of_extensions : P.IsClosedUnderFiniteProducts := by
  let : P.IsClosedUnderBinaryProducts :=
    ObjectProperty.IsClosedUnderLimitsOfShape.mk' (by
      rintro _ ⟨F, hF⟩
      exact P.prop_of_iso (HasLimit.isoOfNatIso (diagramIsoPair F)).symm
        (P.prop_of_iso (biprod.isoProd _ _) (P.prop_biprod (hF _) (hF _))))
  exact ObjectProperty.IsClosedUnderFiniteProducts.mk'

/-- Backwards-compatible extension-stable interface, using the same actual
finite cyclic decomposition and finite-product construction. -/
theorem prop_of_zmod_directSum_equiv
    {A : Type u} [AddCommGroup A] {ι : Type} [Finite ι]
    (m : ι → ℕ) (e : A ≃+ ⨁ i, ZMod (m i))
    (h : ∀ i, P (of (ULift.{u} (ZMod (m i))))) : P (of A) := by
  let : P.IsClosedUnderFiniteProducts := finiteProducts_of_extensions P
  exact prop_of_zmod_directSum_equiv_of_finiteProducts P m e h

/-- Backwards-compatible extension-stable annihilator interface. -/
theorem prop_of_finite_of_cyclic_divisors
    (N : ℕ) (h : ∀ m : ℕ, 0 < m → m ∣ N → P (of (ULift.{u} (ZMod m))))
    (A : Type u) [AddCommGroup A] [Finite A] (hN : ∀ a : A, N • a = 0) :
    P (of A) := by
  let : P.IsClosedUnderFiniteProducts := finiteProducts_of_extensions P
  exact prop_of_finite_of_cyclic_divisors_of_finiteProducts P N h A hN

end AddCommGrpCat
