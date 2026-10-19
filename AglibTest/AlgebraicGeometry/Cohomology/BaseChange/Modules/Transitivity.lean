/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.Transitivity

/-! Focused consumer of the transitivity of cohomology base change (Nitsure,
arXiv:math/0504590v1, proof of Thm 4.3, (C), p. 21), with axiom guards. -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

/-- Transitivity in every degree, through the fibre comparison `(X_B)_C ≅ X_C`. -/
example {X : Scheme.{u}} {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : X ⟶ Spec (CommRingCat.of A)) (σ : A →+* B) (τ : B →+* C) (M : X.Modules) (n : ℕ)
    (h₁ : IsIso (Scheme.Cohomology.moduleCohomologyBaseChangeMap f σ M n))
    (h₂ : IsIso (Scheme.Cohomology.moduleCohomologyBaseChangeMap
      (pullback.snd f (Spec.map (CommRingCat.ofHom σ))) τ
      ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom σ)))).obj M) n)) :
    IsIso (Scheme.Cohomology.moduleCohomologyBaseChangeMap f (τ.comp σ) M n) ∧
      Function.Bijective (Scheme.Cohomology.baseChangeTransCohomologyHom f σ τ M n) :=
  ⟨Scheme.Cohomology.moduleCohomologyBaseChangeMap_isIso_comp f σ τ M n h₁ h₂,
    ConcreteCategory.bijective_of_isIso _⟩

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.moduleCohomologyBaseChangeMap_isIso_comp' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.moduleCohomologyBaseChangeMap_isIso_comp

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.baseChangeTransCohomologyHom_bijective' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.baseChangeTransCohomologyHom_bijective

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.moduleCohomologyMapAlong_pullbackSquareCoefficientArrow' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  AlgebraicGeometry.Scheme.Cohomology.moduleCohomologyMapAlong_pullbackSquareCoefficientArrow

/--
info: 'ModuleCat.extendScalarsComp_hom_app_comp_map_comp_one_tmul' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.extendScalarsComp_hom_app_comp_map_comp_one_tmul
