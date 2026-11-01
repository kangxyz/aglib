/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.ModuleCat.Coproduct
public import Aglib.Algebra.DirectSumTransport

/-! # Complete coproduct-complex transport to original functor values

The native coproduct homology isomorphism, the supplied actual complex
isomorphism and original homology comparisons are assembled before any
geometric complex or coefficient functor is specialized.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex DirectSum

universe u v w a b z zV zW

namespace ModuleCat

variable {R : Type (max u v)} [Ring R] {δ : Type v} [DecidableEq δ]
  {κ : Type w} {c : ComplexShape κ} {C : Type a} [Category.{b} C]

/-- The complete native complex-coproduct computation on independently supplied original
carriers. No functor presentation of those carriers is needed. -/
def coproductEquivOfComplex
    (K : δ → HomologicalComplex (ModuleCat.{max u v} R) c)
    (L : HomologicalComplex (ModuleCat.{max u v} R) c)
    (iso : coproductComplex K ≅ L) (q : κ)
    {V : δ → Type zV} [∀ i, AddCommMonoid (V i)] [∀ i, Module R (V i)]
    {W : Type zW} [AddCommMonoid W] [Module R W]
    (eᵢ : ∀ i, (K i).homology q ≃ₗ[R] V i)
    (e : L.homology q ≃ₗ[R] W) : (⨁ i, V i) ≃ₗ[R] W :=
  DirectSum.transportEquiv eᵢ
    (coproductComplexHomologyLinearEquiv K q)
    (homologyMapIso iso q).toLinearEquiv e

/-- The full original complex-coproduct computation as a linear equivalence
on the actual values of a supplied functor, with independent value universe. -/
def functorCoproductEquivOfComplex
    (F : C ⥤ ModuleCat.{z} R) (M : δ → C) [HasCoproduct M]
    (K : δ → HomologicalComplex (ModuleCat.{max u v} R) c)
    (L : HomologicalComplex (ModuleCat.{max u v} R) c)
    (iso : coproductComplex K ≅ L) (q : κ)
    (eᵢ : ∀ i, (K i).homology q ≃ₗ[R] F.obj (M i))
    (e : L.homology q ≃ₗ[R] F.obj (∐ M)) :
    (⨁ i, F.obj (M i)) ≃ₗ[R] F.obj (∐ M) :=
  coproductEquivOfComplex.{u, v, w, z, z} K L iso q eᵢ e

end ModuleCat
