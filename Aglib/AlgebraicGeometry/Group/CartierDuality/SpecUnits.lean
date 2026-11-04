/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Group.MultiplicativeGroup
public import Mathlib.AlgebraicGeometry.Group.Affine

/-!
# Native unit coordinates on affine schemes over an arbitrary ring

The existing multiplicative group represents units on every test scheme.
These constructions preserve the actual Gamma/Spec comparison and the native
monoidal Spec comparison. No field or finiteness hypothesis is needed.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.Scheme.Group.CartierDuality

universe u

variable {k : Type u} [CommRing k]

/-- The native braided Spec structure used for products of affine schemes. -/
local instance instBraidedAlgSpecUnits : (AlgebraicGeometry.algSpec (CommRingCat.of k)).Braided :=
  AlgebraicGeometry.braidedAlgSpec

/-- The original multiplicative group law on the target of a represented unit. -/
local instance instCommGrpObjSpecUnits :
    CommGrpObj (MultiplicativeGroup.scheme (Spec (CommRingCat.of k))) :=
  MultiplicativeGroup.commGroup (Spec (CommRingCat.of k))

/-- The existing native Spec comparison between a product and its tensor coordinates. -/
def algSpecTensorIso (A B : CommAlgCat.{u} k) :
    (AlgebraicGeometry.algSpec (CommRingCat.of k)).obj (op A) ⊗
        (AlgebraicGeometry.algSpec (CommRingCat.of k)).obj (op B) ≅
      (AlgebraicGeometry.algSpec (CommRingCat.of k)).obj (op (A ⊗ B)) :=
  CategoryTheory.Functor.Monoidal.μIso (AlgebraicGeometry.algSpec (CommRingCat.of k))
    (op A) (op B)

/-- A unit gives its original represented morphism from native Spec into the existing Gm. -/
def specUnitMap (B : CommAlgCat.{u} k) (u : Bˣ) :
    (AlgebraicGeometry.algSpec (CommRingCat.of k)).obj (op B) ⟶
      MultiplicativeGroup.scheme (Spec (CommRingCat.of k)) :=
  (MultiplicativeGroup.sectionsUnitsEquiv (Spec (CommRingCat.of k))
    ((AlgebraicGeometry.algSpec (CommRingCat.of k)).obj (op B))).symm
      (Units.map (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom.toMonoidHom u)

/-- The represented map has exactly the original unit coordinate. -/
theorem specUnitMap_units (B : CommAlgCat.{u} k) (u : Bˣ) :
    MultiplicativeGroup.sectionsUnitsEquiv (Spec (CommRingCat.of k))
        ((AlgebraicGeometry.algSpec (CommRingCat.of k)).obj (op B)) (specUnitMap B u) =
      Units.map (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom.toMonoidHom u := by
  exact Equiv.apply_symm_apply _ _

/-- Pulling back the represented unit on any original test scheme uses its actual section map. -/
theorem specUnitMap_comp_units (B : CommAlgCat.{u} k) (u : Bˣ) (T : Over (Spec (CommRingCat.of k)))
    (a : T ⟶ (AlgebraicGeometry.algSpec (CommRingCat.of k)).obj (op B)) :
    MultiplicativeGroup.sectionsUnitsEquiv (Spec (CommRingCat.of k)) T (a ≫ specUnitMap B u) =
      Units.map
        (((Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ a.left.appTop).hom.toMonoidHom) u := by
  have h := (MultiplicativeGroup.unitsRepresentable (Spec (CommRingCat.of k))).homEquiv_comp
    a (specUnitMap B u)
  change MultiplicativeGroup.sectionsUnitsEquiv (Spec (CommRingCat.of k)) T (a ≫ specUnitMap B u) =
    Units.map a.left.appTop.hom.toMonoidHom
      (MultiplicativeGroup.sectionsUnitsEquiv (Spec (CommRingCat.of k))
        ((AlgebraicGeometry.algSpec (CommRingCat.of k)).obj (op B)) (specUnitMap B u)) at h
  rw [specUnitMap_units] at h
  rw [h]
  apply Units.ext
  rfl

/-- The same pullback equation with the original two composable test maps kept together. -/
theorem specUnitMap_comp_comp_units (B : CommAlgCat.{u} k) (u : Bˣ)
    (S T : Over (Spec (CommRingCat.of k)))
    (a : S ⟶ (AlgebraicGeometry.algSpec (CommRingCat.of k)).obj (op B)) (p : T ⟶ S) :
    MultiplicativeGroup.sectionsUnitsEquiv (Spec (CommRingCat.of k)) T (p ≫ a ≫ specUnitMap B u) =
      Units.map (((Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫
        (p ≫ a).left.appTop).hom.toMonoidHom) u := by
  rw [← Category.assoc]
  exact specUnitMap_comp_units B u T (p ≫ a)

/-- Native Spec pullback of the same unit map is the map of the original pulled-back unit. -/
theorem specUnitMap_naturality {A B : CommAlgCat.{u} k} (f : A ⟶ B) (u : Aˣ) :
    (AlgebraicGeometry.algSpec (CommRingCat.of k)).map f.op ≫ specUnitMap A u =
      specUnitMap B (Units.map f.hom.toMonoidHom u) := by
  apply (MultiplicativeGroup.sectionsUnitsEquiv (Spec (CommRingCat.of k))
    ((AlgebraicGeometry.algSpec (CommRingCat.of k)).obj (op B))).injective
  rw [specUnitMap_comp_units, specUnitMap_units]
  apply Units.ext
  change (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
      (Spec.map (CommRingCat.ofHom f.hom.toRingHom)).appTop).hom (u : A)) =
    ((CommRingCat.ofHom f.hom.toRingHom ≫
      (Scheme.ΓSpecIso (CommRingCat.of B)).inv).hom (u : A))
  exact congrArg
    (fun q : CommRingCat.of A ⟶ Γ(Spec (CommRingCat.of B), ⊤) => q.hom (u : A))
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f.hom.toRingHom)).symm

/-- The same represented unit map preserves multiplication on the original Gm-valued sections. -/
theorem specUnitMap_mul (B : CommAlgCat.{u} k) (u v : Bˣ) :
    specUnitMap B (u * v) = specUnitMap B u * specUnitMap B v := by
  apply (MultiplicativeGroup.sectionsUnitsEquiv (Spec (CommRingCat.of k))
    ((AlgebraicGeometry.algSpec (CommRingCat.of k)).obj (op B))).injective
  rw [MultiplicativeGroup.sectionsUnitsEquiv_mul, specUnitMap_units,
    specUnitMap_units, specUnitMap_units, map_mul]
  rfl

/-- The original unit represents the original identity-valued morphism. -/
theorem specUnitMap_one (B : CommAlgCat.{u} k) : specUnitMap B 1 = 1 := by
  have h := specUnitMap_mul B (1 : Bˣ) 1
  have h' : specUnitMap B 1 * specUnitMap B 1 = specUnitMap B 1 * 1 := by
    simpa only [one_mul, mul_one] using h.symm
  exact mul_left_cancel h'

/-- Unit coordinates on the original native affine scheme, with its original inverse. -/
def specUnitsEquiv (B : CommAlgCat.{u} k) :
    (((AlgebraicGeometry.algSpec (CommRingCat.of k)).obj (op B)) ⟶
      MultiplicativeGroup.scheme (Spec (CommRingCat.of k))) ≃ Bˣ :=
  (MultiplicativeGroup.sectionsUnitsEquiv (Spec (CommRingCat.of k))
    ((AlgebraicGeometry.algSpec (CommRingCat.of k)).obj (op B))).trans
      (Units.mapEquiv
        (Scheme.ΓSpecIso (CommRingCat.of B)).commRingCatIsoToRingEquiv.toMulEquiv).toEquiv

/-- The inverse unit coordinate map is exactly the existing represented morphism. -/
theorem specUnitsEquiv_symm_apply (B : CommAlgCat.{u} k) (u : Bˣ) :
    (specUnitsEquiv B).symm u = specUnitMap B u := rfl

@[simp]
theorem specUnitsEquiv_specUnitMap (B : CommAlgCat.{u} k) (u : Bˣ) :
    specUnitsEquiv B (specUnitMap B u) = u :=
  (specUnitsEquiv B).apply_symm_apply u

@[simp]
theorem specUnitMap_specUnitsEquiv (B : CommAlgCat.{u} k)
    (f : (AlgebraicGeometry.algSpec (CommRingCat.of k)).obj (op B) ⟶
      MultiplicativeGroup.scheme (Spec (CommRingCat.of k))) :
    specUnitMap B (specUnitsEquiv B f) = f :=
  (specUnitsEquiv B).symm_apply_apply f

end AlgebraicGeometry.Scheme.Group.CartierDuality
