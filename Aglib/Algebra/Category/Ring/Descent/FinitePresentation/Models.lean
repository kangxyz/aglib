/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.RingTheory.Extension.Presentation.Core

/-!
# Finitely presented algebra models at a filtered stage

A finite set in an actual filtered colimit of commutative rings comes from
one stage. Applying this to the coefficients of a finite presentation gives
a finitely presented algebra at that stage, with an algebra isomorphism from
its actual scalar extension to the original algebra. The stage maps need
not be injective.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits TensorProduct

universe u v

variable {I : Type u} [Category.{u} I] [IsFiltered I]
  (F : I ⥤ CommRingCat.{u}) (c : Cocone F) (hc : IsColimit c)

include hc

/-- Every finite set of elements of a filtered ring colimit lies in the image
of a single colimit cocone map. -/
lemma CommRingCat.exists_finite_subset_range_ι_app
    (s : Set c.pt) (hs : s.Finite) :
    ∃ i : I, s ⊆ Set.range (c.ι.app i) := by
  classical
  have hc' := isColimitOfPreserves (forget CommRingCat) hc
  choose j x hx using fun a : s ↦ Types.jointly_surjective_of_isColimit hc' a.1
  let : Fintype s := hs.fintype
  obtain ⟨i, hi⟩ := IsFiltered.sup_objs_exists (Finset.univ.image j)
  refine ⟨i, fun a ha ↦ ?_⟩
  let f : j ⟨a, ha⟩ ⟶ i := (hi (Finset.mem_image.mpr ⟨⟨a, ha⟩, by simp, rfl⟩)).some
  refine ⟨F.map f (x ⟨a, ha⟩), ?_⟩
  change (F.map f ≫ c.ι.app i) (x ⟨a, ha⟩) = a
  rw [c.w]
  exact hx ⟨a, ha⟩

namespace Algebra.Presentation

variable {A : Type v} [CommRing A] [Algebra c.pt A]

/-- A finite presentation has an actual finitely presented model at one
filtered stage. The displayed generators map to the specified generators
of the original presentation under the scalar-extension isomorphism. -/
lemma exists_model_of_isColimit {n m : ℕ}
    (P : Presentation c.pt A (Fin n) (Fin m)) :
    ∃ (i : I) (B : Type u) (_ : CommRing B) (_ : Algebra (F.obj i) B),
      Algebra.FinitePresentation (F.obj i) B ∧
      letI : Algebra (F.obj i) c.pt := (c.ι.app i).hom.toAlgebra
      ∃ (e : c.pt ⊗[F.obj i] B ≃ₐ[c.pt] A) (g : Fin n → B),
        ∀ j, e (1 ⊗ₜ[F.obj i] g j) = P.val j := by
  obtain ⟨i, hi⟩ := CommRingCat.exists_finite_subset_range_ι_app F c hc
    P.coeffs P.finite_coeffs
  let : Algebra (F.obj i) c.pt := (c.ι.app i).hom.toAlgebra
  let : Algebra (F.obj i) A :=
    ((algebraMap c.pt A).comp (c.ι.app i).hom).toAlgebra
  let : IsScalarTower (F.obj i) c.pt A :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : P.HasCoeffs (F.obj i) := ⟨hi⟩
  refine ⟨i, P.ModelOfHasCoeffs (F.obj i), inferInstance, inferInstance,
    inferInstance, P.tensorModelOfHasCoeffsEquiv (F.obj i),
    fun j ↦ Ideal.Quotient.mk _ (MvPolynomial.X j), ?_⟩
  intro j
  simp

end Algebra.Presentation

/-- Every finitely presented algebra over an actual filtered ring colimit
is the scalar extension of a finitely presented algebra at some stage. -/
lemma Algebra.FinitePresentation.exists_model_of_isColimit
    (A : Type v) [CommRing A] [Algebra c.pt A] [Algebra.FinitePresentation c.pt A] :
    ∃ (i : I) (B : Type u) (_ : CommRing B) (_ : Algebra (F.obj i) B),
      Algebra.FinitePresentation (F.obj i) B ∧
      letI : Algebra (F.obj i) c.pt := (c.ι.app i).hom.toAlgebra
      Nonempty (c.pt ⊗[F.obj i] B ≃ₐ[c.pt] A) := by
  obtain ⟨i, B, hB, hAB, hfp, e, g, hg⟩ :=
    (Algebra.Presentation.ofFinitePresentation c.pt A).exists_model_of_isColimit F c hc
  exact ⟨i, B, hB, hAB, hfp, ⟨e⟩⟩
