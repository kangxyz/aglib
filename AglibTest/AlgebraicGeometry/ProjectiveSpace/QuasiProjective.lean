/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.QuasiProjective
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Segre.QuasiProjective
public import Aglib.AlgebraicGeometry.ProjectiveSpace.AffineImmersion.QuasiProjective

/-!
# Quasi-projective and projective schemes over an affine base

The declarations below restate the comparison of H-quasi-projective and H-projective morphisms
to `Spec R` with Mathlib's properties (proper, separated, quasi-compact, locally of finite type),
the closure under immersions and products, affine schemes of finite type (affine space), and the
description over a Noetherian ring by immersions into projective space, and guard their axioms.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AglibTest.QuasiProjective

variable {R : CommRingCat.{u}} {X Y : Scheme.{u}}

/-- H-projective is H-quasi-projective and proper. -/
theorem isHProjective_iff (f : X ⟶ Spec R) :
    IsHProjective f ↔ IsHQuasiProjective f ∧ IsProper f :=
  isHProjective_iff_isHQuasiProjective_and_isProper f

/-- An H-quasi-projective morphism is separated, quasi-compact and locally of finite type. -/
theorem properties (f : X ⟶ Spec R) [IsHQuasiProjective f] :
    IsSeparated f ∧ QuasiCompact f ∧ LocallyOfFiniteType f :=
  ⟨inferInstance, inferInstance, inferInstance⟩

/-- Projective space with finitely many coordinates, and its closed subschemes, are H-projective;
quasi-compact immersions into H-quasi-projective schemes are H-quasi-projective. -/
theorem closure (A : Type u) [CommRing A] (ι : Type u) [Finite ι]
    (I : (ProjectiveSpace A ι).IdealSheafData) (i : X ⟶ Y) (g : Y ⟶ Spec R) [IsImmersion i]
    [QuasiCompact i] [IsHQuasiProjective g] :
    IsHProjective (I.subschemeι ≫ ProjectiveSpace.toSpec A ι) ∧ IsHQuasiProjective (i ≫ g) :=
  ⟨inferInstance, inferInstance⟩

/-- Over a Noetherian ring, H-quasi-projective means admitting an immersion into projective space
over the base, every immersion into an H-quasi-projective scheme is H-quasi-projective, and
H-quasi-projective schemes are Noetherian. -/
theorem noetherian [IsNoetherianRing R] (f : X ⟶ Spec R) (i : Y ⟶ X) [IsImmersion i]
    [IsHQuasiProjective f] :
    (IsHQuasiProjective f ↔ ∃ (ι : Type u) (_ : Finite ι) (j : X ⟶ ProjectiveSpace R ι),
      IsImmersion j ∧ j ≫ ProjectiveSpace.toSpec R ι = f) ∧
    IsHQuasiProjective (i ≫ f) ∧ IsNoetherian X :=
  ⟨isHQuasiProjective_iff_exists_isImmersion f, IsHQuasiProjective.comp_of_isImmersion i f,
    IsHQuasiProjective.isNoetherian f⟩

/-- Fibre products of H-quasi-projective (H-projective) schemes over `Spec R` are
H-quasi-projective (H-projective), by the Segre embedding. -/
theorem products (f : X ⟶ Spec R) (g : Y ⟶ Spec R) [IsHQuasiProjective f]
    [IsHQuasiProjective g] :
    IsHQuasiProjective (pullback.fst f g ≫ f) ∧ IsHQuasiProjective (pullback.snd f g ≫ g) :=
  ⟨inferInstance, isHQuasiProjective_pullback_snd_comp f g⟩

/-- Fibre products of H-projective schemes over `Spec R` are H-projective. -/
theorem products_projective (f : X ⟶ Spec R) (g : Y ⟶ Spec R) [IsHProjective f]
    [IsHProjective g] : IsHProjective (pullback.fst f g ≫ f) :=
  inferInstance

/-- Affine schemes of finite type, for example affine space `A^n_R`, are H-quasi-projective. -/
theorem affine {A : Type u} [CommRing A] (B : Type u) [CommRing B] (φ : A →+* B)
    (hφ : φ.FiniteType) (n : ℕ) :
    IsHQuasiProjective (Spec.map (CommRingCat.ofHom φ)) ∧
      IsHQuasiProjective (Spec.map (CommRingCat.ofHom (algebraMap A (MvPolynomial (Fin n) A)))) :=
  ⟨isHQuasiProjective_spec_map_of_finiteType φ hφ,
    isHQuasiProjective_spec_map_of_finiteType _ (RingHom.finiteType_algebraMap.mpr inferInstance)⟩

/-- info: 'AglibTest.QuasiProjective.isHProjective_iff' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.QuasiProjective.isHProjective_iff

/-- info: 'AglibTest.QuasiProjective.properties' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.QuasiProjective.properties

/-- info: 'AglibTest.QuasiProjective.closure' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.QuasiProjective.closure

/-- info: 'AglibTest.QuasiProjective.noetherian' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.QuasiProjective.noetherian

/-- info: 'AglibTest.QuasiProjective.products' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.QuasiProjective.products

/-- info: 'AglibTest.QuasiProjective.products_projective' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.QuasiProjective.products_projective

/-- info: 'AglibTest.QuasiProjective.affine' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.QuasiProjective.affine

end AglibTest.QuasiProjective
