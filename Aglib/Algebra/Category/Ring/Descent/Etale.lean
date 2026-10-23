/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.Ring.Descent.FinitePresentation.Factorization
public import Mathlib.RingTheory.Smooth.NoetherianDescent
public import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Etale algebra objects at a filtered stage

Every etale algebra over an actual filtered colimit of commutative
rings is the scalar extension of an etale algebra at one stage. The
ring transition maps and colimit maps need not be injective or flat.
-/

@[expose] public noncomputable section

open CategoryTheory Limits
open scoped TensorProduct

universe u v

variable {I : Type u} [Category.{u} I] [IsFiltered I]
  (F : I ⥤ CommRingCat.{u}) (c : Cocone F) (hc : IsColimit c)

include hc

/-- An etale algebra over a filtered ring colimit has an actual
etale model at a stage above any prescribed index. -/
theorem Algebra.Etale.exists_model_of_isColimit_above
    (B : Type v) [CommRing B] [Algebra c.pt B]
    [Algebra.Etale c.pt B] (i₀ : I) :
    ∃ (i : I) (_ : i₀ ⟶ i) (Bᵢ : Type u) (_ : CommRing Bᵢ) (_ : Algebra (F.obj i) Bᵢ),
      Algebra.Etale (F.obj i) Bᵢ ∧
      letI : Algebra (F.obj i) c.pt := (c.ι.app i).hom.toAlgebra
      Nonempty (c.pt ⊗[F.obj i] Bᵢ ≃ₐ[c.pt] B) := by
  obtain ⟨A₀, B₀, _, _, hfg, het, ⟨e⟩⟩ :=
    Algebra.Etale.exists_subalgebra_fg ℤ c.pt B
  let : Algebra.Etale A₀ B₀ := het
  let : Algebra.FiniteType ℤ A₀ := ⟨A₀.fg_top.mpr hfg⟩
  let : Algebra.FinitePresentation ℤ A₀ :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  let φ : CommRingCat.of A₀ ⟶ c.pt := CommRingCat.ofHom A₀.val.toRingHom
  obtain ⟨i, hi, ψ, hψ⟩ :=
    CommRingCat.exists_factorization_of_finitePresentation_int_above F c hc
      (.of A₀) φ i₀
  let : Algebra A₀ (F.obj i) := ψ.hom.toAlgebra
  let : Algebra (F.obj i) c.pt := (c.ι.app i).hom.toAlgebra
  let : IsScalarTower A₀ (F.obj i) c.pt := IsScalarTower.of_algebraMap_eq fun x ↦ by
    exact congr($(hψ).hom x).symm
  refine ⟨i, hi, F.obj i ⊗[A₀] B₀, inferInstance, inferInstance,
    inferInstance, ?_⟩
  exact ⟨(Algebra.TensorProduct.cancelBaseChange A₀ (F.obj i) c.pt c.pt B₀).trans e.symm⟩

/-- Every etale algebra over a filtered ring colimit is the scalar
extension of an etale algebra at some stage. -/
theorem Algebra.Etale.exists_model_of_isColimit
    (B : Type v) [CommRing B] [Algebra c.pt B]
    [Algebra.Etale c.pt B] :
    ∃ (i : I) (Bᵢ : Type u) (_ : CommRing Bᵢ) (_ : Algebra (F.obj i) Bᵢ),
      Algebra.Etale (F.obj i) Bᵢ ∧
      letI : Algebra (F.obj i) c.pt := (c.ι.app i).hom.toAlgebra
      Nonempty (c.pt ⊗[F.obj i] Bᵢ ≃ₐ[c.pt] B) := by
  obtain ⟨i₀⟩ := IsFiltered.nonempty (C := I)
  obtain ⟨i, _, Bᵢ, hBᵢ, hABᵢ, het, he⟩ :=
    Algebra.Etale.exists_model_of_isColimit_above F c hc B i₀
  exact ⟨i, Bᵢ, hBᵢ, hABᵢ, het, he⟩
