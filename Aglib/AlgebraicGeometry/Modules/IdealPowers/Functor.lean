/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.IdealPowers.Scalars

/-! # Functoriality and the scalar universal property of ideal quotients -/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

universe u

variable (X : Scheme.{u}) {A : Type u} [CommRing A]
variable (α : A →+* Γ(X, ⊤)) {F G H : X.Modules}

/-- Killing each defining scalar is equivalent to killing the actual ideal image. -/
theorem idealMultipleι_comp_eq_zero (J : Ideal A) (f : F ⟶ G)
    (h : ∀ a : J, globalScalarEndomorphism X F (α a) ≫ f = 0) :
    idealMultipleι X α F J ≫ f = 0 := by
  apply (cancel_epi (factorThruImage (idealEvaluation X α F J))).mp
  change factorThruImage (idealEvaluation X α F J) ≫
    (image.ι (idealEvaluation X α F J) ≫ f) = _ ≫ 0
  rw [← Category.assoc, image.fac, comp_zero]
  apply Sigma.hom_ext
  intro a
  simpa only [idealEvaluation, Sigma.ι_comp_desc_assoc, comp_zero] using h a

/-- Descend a morphism along the original quotient after checking scalar annihilation. -/
def idealQuotientDesc (J : Ideal A) (f : F ⟶ G)
    (h : ∀ a : J, globalScalarEndomorphism X F (α a) ≫ f = 0) :
    idealQuotient X α F J ⟶ G :=
  cokernel.desc _ f (idealMultipleι_comp_eq_zero X α J f h)

@[reassoc (attr := simp)]
theorem idealQuotientπ_desc (J : Ideal A) (f : F ⟶ G)
    (h : ∀ a : J, globalScalarEndomorphism X F (α a) ≫ f = 0) :
    idealQuotientπ X α F J ≫ idealQuotientDesc X α J f h = f :=
  cokernel.π_desc _ _ _

/-- A map into a sheaf annihilated by the ideal descends canonically. -/
def idealQuotientDescOfAnnihilated (J : Ideal A) (f : F ⟶ G)
    (h : ∀ a : J, globalScalarEndomorphism X G (α a) = 0) :
    idealQuotient X α F J ⟶ G :=
  idealQuotientDesc X α J f (fun a => by
    rw [← (globalScalarCenter X (α a)).naturality f]
    change f ≫ globalScalarEndomorphism X G (α a) = 0
    rw [h a, comp_zero])

@[reassoc (attr := simp)]
theorem idealQuotientπ_descOfAnnihilated (J : Ideal A) (f : F ⟶ G)
    (h : ∀ a : J, globalScalarEndomorphism X G (α a) = 0) :
    idealQuotientπ X α F J ≫ idealQuotientDescOfAnnihilated X α J f h = f :=
  idealQuotientπ_desc X α J f _

/-- The map of ideal quotients induced by an actual coefficient morphism. -/
def idealQuotientHom (J : Ideal A) (f : F ⟶ G) :
    idealQuotient X α F J ⟶ idealQuotient X α G J :=
  idealQuotientDescOfAnnihilated X α J (f ≫ idealQuotientπ X α G J)
    (idealQuotient_scalar_eq_zero X α G J)

@[reassoc (attr := simp)]
theorem idealQuotientπ_hom (J : Ideal A) (f : F ⟶ G) :
    idealQuotientπ X α F J ≫ idealQuotientHom X α J f =
      f ≫ idealQuotientπ X α G J :=
  idealQuotientπ_descOfAnnihilated X α J _ _

@[simp]
theorem idealQuotientHom_id (J : Ideal A) (F : X.Modules) :
    idealQuotientHom X α J (𝟙 F) = 𝟙 _ := by
  apply (cancel_epi (idealQuotientπ X α F J)).mp
  simp

@[reassoc, simp]
theorem idealQuotientHom_comp (J : Ideal A) (f : F ⟶ G) (g : G ⟶ H) :
    idealQuotientHom X α J (f ≫ g) =
      idealQuotientHom X α J f ≫ idealQuotientHom X α J g := by
  apply (cancel_epi (idealQuotientπ X α F J)).mp
  simp

/-- Quotient by a fixed ideal, preserving the original quotient objects and maps. -/
def idealQuotientFunctor (J : Ideal A) : X.Modules ⥤ X.Modules where
  obj F := idealQuotient X α F J
  map f := idealQuotientHom X α J f
  map_id F := idealQuotientHom_id X α J F
  map_comp f g := idealQuotientHom_comp X α J f g

/-- Coefficient morphisms commute with reduction along inclusions of ideals. -/
@[reassoc]
theorem idealQuotientHom_map {J K : Ideal A} (h : J ≤ K) (f : F ⟶ G) :
    idealQuotientHom X α J f ≫ idealQuotientMap X α G h =
      idealQuotientMap X α F h ≫ idealQuotientHom X α K f := by
  apply (cancel_epi (idealQuotientπ X α F J)).mp
  simp

end AlgebraicGeometry.Scheme.Modules
