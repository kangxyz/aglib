/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.CategoryTheory.Localization.Composition
public import Aglib.CategoryTheory.Abelian.SerreClass.Exact
public import Mathlib.CategoryTheory.Abelian.SerreClass.Bousfield

/-!
# Composition, equivalence and natural-isomorphism transport of kernel Serre localizations

The localization premises remain explicit.

Source: `lean/R5Lab/Aglib/CategoryTheory/Localization/SerreKernel.lean`
at frozen R5 `f8a3314ddecffcada2ec721d26d56a937bed9690`.
SHA-256: `1c449ffcdec1622c46dacd81533bebece8419e4131c15c6061a1c63649c20c71`.
Native objects and canonical maps are reused; provenance does not select declaration namespaces.
-/

@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Functor
universe u₁ u₂ u₃ v₁ v₂ v₃

/-- Composition of actual exact Serre localizations localizes by its own
kernel. The numerator of a fraction is inverted by the composite precisely
when the represented target arrow is inverted by the second functor. -/
theorem isLocalization_comp_kernel
    {A : Type u₁} {B : Type u₂} {C : Type u₃}
    [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C]
    [Abelian A] [Abelian B] [Abelian C]
    (F : A ⥤ B) (G : B ⥤ C)
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [F.IsLocalization F.kernel.isoModSerre]
    [G.IsLocalization G.kernel.isoModSerre] :
    (F ⋙ G).IsLocalization (F ⋙ G).kernel.isoModSerre := by
  let W := (F ⋙ G).kernel.isoModSerre
  have hW (M N : A) (f : M ⟶ N) : W f ↔ IsIso (G.map (F.map f)) := by
    change (F ⋙ G).kernel.isoModSerre f ↔ _
    rw [Abelian.isoModSerre_kernel_eq_inverseImage_isomorphisms]
    rfl
  apply Functor.IsLocalization.comp F G F.kernel.isoModSerre G.kernel.isoModSerre W
  · intro M N f hf
    exact (hW M N f).mp hf
  · intro M N f hf
    have : IsIso (F.map f) := Localization.inverts F F.kernel.isoModSerre f hf
    exact (hW M N f).mpr inferInstance
  · intro M N f hf
    have : F.EssSurj := Localization.essSurj F F.kernel.isoModSerre
    let eM := F.objObjPreimageIso M
    let eN := F.objObjPreimageIso N
    let a := eM.hom ≫ f ≫ eN.inv
    obtain ⟨φ, hφ⟩ := Localization.exists_rightFraction F F.kernel.isoModSerre a
    have hs : IsIso (F.map φ.s) :=
      Localization.inverts F F.kernel.isoModSerre φ.s φ.hs
    have ha : F.map φ.s ≫ a = F.map φ.f := by
      rw [hφ]
      exact φ.map_s_comp_map F (Localization.inverts F F.kernel.isoModSerre)
    have hf' : IsIso (G.map f) :=
      Localization.inverts G G.kernel.isoModSerre f hf
    have hnum : W φ.f := by
      apply (hW _ _ _).mpr
      rw [← ha]
      dsimp [a]
      rw [G.map_comp, G.map_comp, G.map_comp]
      infer_instance
    refine ⟨_, _, φ.f, hnum, ⟨Arrow.isoMk (asIso (F.map φ.s) ≪≫ eM) eN ?_⟩⟩
    dsimp [a] at ha
    simpa using congrArg (fun k => k ≫ eN.hom) ha


theorem isLocalization_kernel_of_equivalence
    {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]
    [Abelian A] [Abelian B] (F : A ⥤ B) [F.IsEquivalence] :
    F.IsLocalization F.kernel.isoModSerre := by
  apply Functor.IsLocalization.of_isEquivalence F F.kernel.isoModSerre
  intro M N f hf
  rw [Abelian.isoModSerre_kernel_eq_inverseImage_isomorphisms] at hf
  have : IsIso (F.map f) := hf
  exact isIso_of_reflects_iso f F

theorem isLocalization_kernel_of_natIso
    {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]
    [Abelian A] [Abelian B] {F G : A ⥤ B}
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [F.IsLocalization F.kernel.isoModSerre] (e : F ≅ G) :
    G.IsLocalization G.kernel.isoModSerre := by
  have hk : F.kernel = G.kernel := by
    funext M
    apply propext
    exact ⟨fun h => h.of_iso (e.app M).symm, fun h => h.of_iso (e.app M)⟩
  have hW : F.kernel.isoModSerre = G.kernel.isoModSerre := by
    funext M N f
    change (F.kernel (CategoryTheory.Limits.kernel f) ∧ F.kernel (cokernel f)) =
      (G.kernel (CategoryTheory.Limits.kernel f) ∧ G.kernel (cokernel f))
    rw [hk]
  rw [← hW]
  exact Functor.IsLocalization.of_iso F.kernel.isoModSerre e

end CategoryTheory.Functor
