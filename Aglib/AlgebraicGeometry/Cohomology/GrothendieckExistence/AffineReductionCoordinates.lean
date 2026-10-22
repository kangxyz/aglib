/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.AffineQuotient

/-! # Whole coordinates for an original reduction isomorphism -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules.Coherent
universe u v w

/-- Compose quotient coordinates with a reduction while retaining its original
transition. All arrows are abstract before geometric specialization. -/
def quotientReductionCoordinates {R : Type u} [CommRing R]
    {C : Type v} [Category.{w} C] (Γ : C ⥤ ModuleCat R) {M Q N : C}
    (J : Ideal R) (u : M ⟶ Q)
    (e : (Γ.obj M ⧸ (J • (⊤ : Submodule R (Γ.obj M)))) ≃ₗ[R] Γ.obj Q)
    (he : ∀ x, e (Submodule.Quotient.mk x) = Γ.map u x)
    (d : Q ≅ N) (t : M ⟶ N) (ht : u ≫ d.hom = t) :
    {c : (Γ.obj M ⧸ (J • (⊤ : Submodule R (Γ.obj M)))) ≃ₗ[R] Γ.obj N //
      ∀ x, c (Submodule.Quotient.mk x) = Γ.map t x} := by
  refine ⟨e.trans (Γ.mapIso d).toLinearEquiv, ?_⟩
  intro x
  change Γ.map d.hom (e (Submodule.Quotient.mk x)) = _
  rw [he]
  have hh := congrArg (fun g => Γ.map g x) ht
  simpa only [Functor.map_comp, ConcreteCategory.comp_apply] using hh

/-- Preserve quotient coordinates and their unit proof as one supplied value.
Projection and composition are checked before specializing the section functor. -/
def quotientReductionCoordinatesOfComparison {R : Type u} [CommRing R]
    {C : Type v} [Category.{w} C] (Γ : C ⥤ ModuleCat R) {M Q N : C}
    (J : Ideal R) (u : M ⟶ Q)
    (c : {e : (Γ.obj M ⧸ (J • (⊤ : Submodule R (Γ.obj M)))) ≃ₗ[R] Γ.obj Q //
      ∀ x, e (Submodule.Quotient.mk x) = Γ.map u x})
    (d : Q ≅ N) (t : M ⟶ N) (ht : u ≫ d.hom = t) :
    {e : (Γ.obj M ⧸ (J • (⊤ : Submodule R (Γ.obj M)))) ≃ₗ[R] Γ.obj N //
      ∀ x, e (Submodule.Quotient.mk x) = Γ.map t x} :=
  quotientReductionCoordinates Γ J u c.val c.property d t ht

end AlgebraicGeometry.Scheme.Modules.Coherent
