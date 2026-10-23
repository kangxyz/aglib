/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Formal.Approximation.FiniteData
public import Aglib.AlgebraicGeometry.Modules.IdealPowers.ThickeningSections
public import Mathlib.RingTheory.AdicCompletion.Algebra

/-!
# Original closed-fibre comparison from coefficient precision

Equality of the original quotient-valued algebra maps gives equality of
the actual morphisms from the original closed fibre to a coefficient model.
The native pullback composition isomorphisms then compare the actual bundles.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules.Invertible

universe u

variable {R A C : Type u} [CommRing R] [CommRing A] [CommRing C]
  [Algebra R A] [Algebra R C] {X : Scheme.{u}}

/-- The original spectral morphism of an algebra homomorphism is over the
original coefficient spectrum. -/
@[reassoc (attr := simp)]
theorem specAlgHom_over (b : C →ₐ[R] A) :
    Spec.map (CommRingCat.ofHom (b : C →+* A)) ≫ Spec.algebraMap R C =
      Spec.algebraMap R A := by
  rw [← Spec.map_comp]
  congr 1
  ext r
  exact b.commutes r

/-- The actual coefficient base-change map induced by an algebra homomorphism. -/
def coefficientBaseChangeMap (f : X ⟶ Spec (CommRingCat.of R)) (b : C →ₐ[R] A) :
    Limits.pullback (Spec.algebraMap R A) f ⟶
      Limits.pullback (Spec.algebraMap R C) f :=
  Limits.pullback.lift
    (Limits.pullback.fst (Spec.algebraMap R A) f ≫
      Spec.map (CommRingCat.ofHom (b : C →+* A)))
    (Limits.pullback.snd (Spec.algebraMap R A) f)
    (by rw [Category.assoc, specAlgHom_over]; exact Limits.pullback.condition)

@[reassoc (attr := simp)]
theorem coefficientBaseChangeMap_fst (f : X ⟶ Spec (CommRingCat.of R)) (b : C →ₐ[R] A) :
    coefficientBaseChangeMap f b ≫ Limits.pullback.fst (Spec.algebraMap R C) f =
      Limits.pullback.fst (Spec.algebraMap R A) f ≫
        Spec.map (CommRingCat.ofHom (b : C →+* A)) :=
  Limits.pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem coefficientBaseChangeMap_snd (f : X ⟶ Spec (CommRingCat.of R)) (b : C →ₐ[R] A) :
    coefficientBaseChangeMap f b ≫ Limits.pullback.snd (Spec.algebraMap R C) f =
      Limits.pullback.snd (Spec.algebraMap R A) f :=
  Limits.pullback.lift_snd _ _ _

/-- The native finite-subalgebra cone projection is exactly the original
coefficient base-change map of the original subalgebra inclusion. -/
theorem finiteType_coneProjection_eq
    (f : X ⟶ Spec (CommRingCat.of R)) (s : Finset A) :
    (Scheme.FiniteTypeSubalgebraLimit.schemeCone R A f).π.app (op s) =
      coefficientBaseChangeMap f (Algebra.FiniteTypeSubalgebraLimit.stage R A s).val := rfl

/-- An actual algebra-valued point specializes the coefficient model back
to the original scheme. -/
def coefficientSpecialization (f : X ⟶ Spec (CommRingCat.of R)) (a : C →ₐ[R] R) :
    X ⟶ Limits.pullback (Spec.algebraMap R C) f :=
  Limits.pullback.lift (f ≫ Spec.map (CommRingCat.ofHom (a : C →+* R))) (𝟙 X)
    (by rw [Category.assoc, specAlgHom_over]; simp [Spec.algebraMap])

@[reassoc (attr := simp)]
theorem coefficientSpecialization_fst
    (f : X ⟶ Spec (CommRingCat.of R)) (a : C →ₐ[R] R) :
    coefficientSpecialization f a ≫ Limits.pullback.fst (Spec.algebraMap R C) f =
      f ≫ Spec.map (CommRingCat.ofHom (a : C →+* R)) :=
  Limits.pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem coefficientSpecialization_snd
    (f : X ⟶ Spec (CommRingCat.of R)) (a : C →ₐ[R] R) :
    coefficientSpecialization f a ≫ Limits.pullback.snd (Spec.algebraMap R C) f = 𝟙 X :=
  Limits.pullback.lift_snd _ _ _

/-- The original quotient-valued coefficient map gives a map from the original
ideal closed fibre to the actual coefficient base change. -/
def closedFiberCoefficientMap (f : X ⟶ Spec (CommRingCat.of R)) (I : Ideal R)
    (d : A →ₐ[R] R ⧸ I) :
    idealThickeningSpace f I ⟶ Limits.pullback (Spec.algebraMap R A) f :=
  Limits.pullback.lift
    (idealThickeningStructure f I ≫ Spec.map (CommRingCat.ofHom (d : A →+* R ⧸ I)))
    (idealThickeningι f I)
    (by rw [Category.assoc, specAlgHom_over]; exact Limits.pullback.condition.symm)

@[reassoc (attr := simp)]
theorem closedFiberCoefficientMap_fst (f : X ⟶ Spec (CommRingCat.of R)) (I : Ideal R)
    (d : A →ₐ[R] R ⧸ I) :
    closedFiberCoefficientMap f I d ≫ Limits.pullback.fst (Spec.algebraMap R A) f =
      idealThickeningStructure f I ≫ Spec.map (CommRingCat.ofHom (d : A →+* R ⧸ I)) :=
  Limits.pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem closedFiberCoefficientMap_snd (f : X ⟶ Spec (CommRingCat.of R)) (I : Ideal R)
    (d : A →ₐ[R] R ⧸ I) :
    closedFiberCoefficientMap f I d ≫ Limits.pullback.snd (Spec.algebraMap R A) f =
      idealThickeningι f I :=
  Limits.pullback.lift_snd _ _ _

/-- Original quotient precision gives equality of the actual two maps from
the original closed fibre to the original coefficient model. -/
theorem coefficientSpecialization_closedFiber
    (f : X ⟶ Spec (CommRingCat.of R)) (I : Ideal R)
    (a : C →ₐ[R] R) (b : C →ₐ[R] A) (d : A →ₐ[R] R ⧸ I)
    (h : (Ideal.Quotient.mkₐ R I).comp a = d.comp b) :
    idealThickeningι f I ≫ coefficientSpecialization f a =
      closedFiberCoefficientMap f I d ≫ coefficientBaseChangeMap f b := by
  have hs : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫
      Spec.map (CommRingCat.ofHom (a : C →+* R)) =
      Spec.map (CommRingCat.ofHom (d : A →+* R ⧸ I)) ≫
        Spec.map (CommRingCat.ofHom (b : C →+* A)) := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext c
    exact DFunLike.congr_fun h c
  apply Limits.pullback.hom_ext
  · simp only [Category.assoc, coefficientSpecialization_fst, coefficientBaseChangeMap_fst,
      closedFiberCoefficientMap_fst_assoc]
    rw [← Category.assoc, show idealThickeningι f I ≫ f =
      idealThickeningStructure f I ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) from
        Limits.pullback.condition, Category.assoc, hs]
  · simp only [Category.assoc, coefficientSpecialization_snd, coefficientBaseChangeMap_snd,
      closedFiberCoefficientMap_snd, Category.comp_id]

/-- The specified coefficient-model comparison and original quotient precision
give an actual bundle isomorphism on the original closed fibre. -/
def coefficientSpecializationClosedFiberIso
    (f : X ⟶ Spec (CommRingCat.of R)) (I : Ideal R)
    (a : C →ₐ[R] R) (b : C →ₐ[R] A) (d : A →ₐ[R] R ⧸ I)
    (h : (Ideal.Quotient.mkₐ R I).comp a = d.comp b)
    (N : (Limits.pullback (Spec.algebraMap R C) f).Modules)
    (L : (Limits.pullback (Spec.algebraMap R A) f).Modules)
    (e : (pullback (coefficientBaseChangeMap f b)).obj N ≅ L) :
    (pullback (idealThickeningι f I)).obj ((pullback (coefficientSpecialization f a)).obj N) ≅
      (pullback (closedFiberCoefficientMap f I d)).obj L :=
  (pullbackComp (idealThickeningι f I) (coefficientSpecialization f a)).app N ≪≫
    (pullbackCongr (coefficientSpecialization_closedFiber f I a b d h)).app N ≪≫
    ((pullbackComp (closedFiberCoefficientMap f I d) (coefficientBaseChangeMap f b)).app N).symm ≪≫
    (pullback (closedFiberCoefficientMap f I d)).mapIso e

end AlgebraicGeometry.Scheme.Modules.Invertible
