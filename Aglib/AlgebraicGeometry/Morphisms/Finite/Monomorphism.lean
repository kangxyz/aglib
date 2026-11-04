/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteFlat.Degree
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Monomorphisms of finite schemes with equal structural degree

The original monomorphism is finite and hence a closed immersion. Its original
map on global sections is a surjective linear map for the structural field
actions. Equal finite-scheme degrees make this map bijective, so the same
scheme morphism is an isomorphism. Nilpotents, empty schemes and all fields
are allowed; no geometric-point count is used.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Scheme.OverField

universe u

namespace AlgebraicGeometry.Scheme.Hom

attribute [local instance] coordinateAlgebra

private theorem finite_globalSections_of_isFinite
    {k : Type u} [Field k] (X : FScheme k) [IsFinite X.hom] :
    Module.Finite k Γ(X.left, ⊤) := by
  let : IsAffine X.left := isAffine_of_isAffineHom X.hom
  let a : CommRingCat.of k ⟶ Γ(X.left, ⊤) :=
    (Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop
  have hs : X.left.isoSpec.inv ≫ X.hom = Spec.map a := by
    rw [← Scheme.isoSpec_inv_naturality, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
  have hfinite : IsFinite (Spec.map a) := by
    rw [← hs]
    infer_instance
  have ha : a.hom.Finite := (IsFinite.SpecMap_iff a).mp hfinite
  change (algebraMap k Γ(X.left, ⊤)).Finite at ha
  exact (RingHom.finite_algebraMap).mp ha

private def finiteFieldCoordinateMap {k : Type u} [Field k] {X Y : FScheme k}
    (f : X ⟶ Y) : Γ(Y.left, ⊤) →ₐ[k] Γ(X.left, ⊤) :=
  {
    f.left.appTop.hom with
    commutes' := fun x => by
      have h : (Scheme.ΓSpecIso (.of k)).inv ≫ Y.hom.appTop ≫ f.left.appTop =
          (Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop := by
        rw [← Scheme.Hom.comp_appTop, Over.w f]
      exact congrArg (fun q : CommRingCat.of k ⟶ Γ(X.left, ⊤) => q x) h }

private theorem finiteFieldCoordinateMap_surjective_of_mono
    {k : Type u} [Field k] {X Y : FScheme k}
    [IsFinite X.hom] [IsFinite Y.hom] (f : X ⟶ Y) [Mono f] :
    Function.Surjective (finiteFieldCoordinateMap f).toLinearMap := by
  let : IsAffine X.left := isAffine_of_isAffineHom X.hom
  let : IsAffine Y.left := isAffine_of_isAffineHom Y.hom
  have hcomp : IsFinite (f.left ≫ Y.hom) := by rw [Over.w f]; infer_instance
  let : IsFinite f.left := IsFinite.of_comp f.left Y.hom
  let : IsClosedImmersion f.left :=
    (IsClosedImmersion.iff_isFinite_and_mono f.left).mpr ⟨inferInstance, inferInstance⟩
  exact f.left.app_surjective ⊤ (isAffineOpen_top Y.left)

/-- A monomorphism between the original finite field schemes cannot
increase structural degree. This counts the full original scheme. -/
theorem finiteSchemeDegree_le_of_mono
    {k : Type u} [Field k] {X Y : FScheme k}
    [IsFinite X.hom] [IsFinite Y.hom] (f : X ⟶ Y) [Mono f] :
    finiteSchemeDegree k X.hom ≤ finiteSchemeDegree k Y.hom := by
  let : Module.Finite k Γ(Y.left, ⊤) := finite_globalSections_of_isFinite Y
  exact LinearMap.finrank_le_finrank_of_surjective (finiteFieldCoordinateMap_surjective_of_mono f)

/-- A monomorphism between the original finite field schemes of equal
structural degree is an isomorphism, including its nonreduced structure. -/
theorem isIso_of_mono_of_finiteSchemeDegree_eq
    {k : Type u} [Field k] {X Y : FScheme k}
    [IsFinite X.hom] [IsFinite Y.hom] (f : X ⟶ Y) [Mono f]
    (hdegree : finiteSchemeDegree k X.hom = finiteSchemeDegree k Y.hom) : IsIso f := by
  let : IsAffine X.left := isAffine_of_isAffineHom X.hom
  let : IsAffine Y.left := isAffine_of_isAffineHom Y.hom
  let : Module.Finite k Γ(X.left, ⊤) := finite_globalSections_of_isFinite X
  let : Module.Finite k Γ(Y.left, ⊤) := finite_globalSections_of_isFinite Y
  let a := finiteFieldCoordinateMap f
  have hsurj : Function.Surjective a.toLinearMap := finiteFieldCoordinateMap_surjective_of_mono f
  have hdim : Module.finrank k Γ(Y.left, ⊤) = Module.finrank k Γ(X.left, ⊤) :=
    hdegree.symm
  have hinj : Function.Injective a.toLinearMap :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hsurj
  let : IsIso f.left.appTop :=
    (ConcreteCategory.isIso_iff_bijective f.left.appTop).mpr ⟨hinj, hsurj⟩
  have heq : X.left.isoSpec.hom ≫ Spec.map f.left.appTop ≫ Y.left.isoSpec.inv = f.left := by
    rw [← Category.assoc, Scheme.isoSpec_hom_naturality]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  let : IsIso f.left := heq ▸ inferInstance
  have : IsIso ((Over.forget (Base k)).map f) := by
    change IsIso f.left
    infer_instance
  exact isIso_of_reflects_iso f (Over.forget (Base k))

end AlgebraicGeometry.Scheme.Hom
