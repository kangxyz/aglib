/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Coherent.AdicSystem.QuotientCongr
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.SpecSectionsCoordinates

/-! # Transport whole original quotient coordinates before specialization -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules.Coherent
universe u v w z

/-- Original quotient coordinates transported together with their unit law.
The category, section functor, object family, and units are all abstract. -/
def quotientCoordinatesTransport {R : Type u} [CommRing R]
    {C : Type v} [Category.{w} C] {T : Type z}
    (Γ : C ⥤ ModuleCat R) (Q : T → C) {M : C}
    (η : ∀ t, M ⟶ Q t) (J : Ideal R) {a b : T}
    (e : (Γ.obj M ⧸ (J • (⊤ : Submodule R (Γ.obj M)))) ≃ₗ[R] Γ.obj (Q a))
    (he : ∀ x, e (Submodule.Quotient.mk x) = Γ.map (η a) x) (h : a = b) :
    {d : (Γ.obj M ⧸ (J • (⊤ : Submodule R (Γ.obj M)))) ≃ₗ[R] Γ.obj (Q b) //
      ∀ x, d (Submodule.Quotient.mk x) = Γ.map (η b) x} := by
  let c := arrowFamilyIso Q η h
  refine ⟨e.trans (Γ.mapIso c.val).toLinearEquiv, ?_⟩
  intro x
  change Γ.map c.val.hom (e (Submodule.Quotient.mk x)) = _
  rw [he]
  have hh := congrArg (fun g => Γ.map g x) c.property
  simpa only [Functor.map_comp, ConcreteCategory.comp_apply] using hh

end AlgebraicGeometry.Scheme.Modules.Coherent
