/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.RingTheory.LocalProperties.Exactness
public import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
public import Mathlib.Algebra.Category.ModuleCat.Products
/-!
# Localization and exactness of categorical module diagrams

Finite categorical products of localization maps are localization maps.
Exactness of an actual module short complex is detected by compatible maps to
short complexes localized at a set of elements generating the unit ideal.
-/
@[expose] public section


noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits
namespace ModuleCat

/-- Finite categorical products of module-localization maps localize. -/
lemma isLocalizedModule_piMap {R : Type u} [CommRing R] (S : Submonoid R)
    {ι : Type u} [Finite ι] {M N : ι → ModuleCat.{u} R}
    (f : ∀ i, M i ⟶ N i) [∀ i, IsLocalizedModule S (f i).hom] :
    IsLocalizedModule S (Limits.Pi.map f).hom := by
  let g : (∀ i, M i) →ₗ[R] (∀ i, N i) :=
    LinearMap.pi fun i => (f i).hom ∘ₗ LinearMap.proj i
  have hg : IsLocalizedModule S g := inferInstance
  have he : Limits.Pi.map f = (ModuleCat.piIsoPi M).hom ≫ ModuleCat.ofHom g ≫
      (ModuleCat.piIsoPi N).inv := by
    apply Pi.hom_ext
    intro i
    simp only [Category.assoc, ModuleCat.piIsoPi_inv_kernel_ι, Limits.Pi.map_π]
    change Limits.Pi.π M i ≫ f i = (ModuleCat.piIsoPi M).hom ≫ ModuleCat.ofHom
      ((LinearMap.proj i).comp g)
    change Limits.Pi.π M i ≫ f i = (ModuleCat.piIsoPi M).hom ≫
      (ModuleCat.ofHom (LinearMap.proj i) ≫ f i)
    rw [← Category.assoc, ModuleCat.piIsoPi_hom_ker_subtype]
  rw [he]
  exact IsLocalizedModule.of_linearEquiv S
    (g ∘ₗ (ModuleCat.piIsoPi M).toLinearEquiv.toLinearMap)
    (ModuleCat.piIsoPi N).symm.toLinearEquiv

/-- Compatible localizations at a generating set detect exactness of an
actual module short complex. -/
lemma shortComplex_exact_of_isLocalized_span {R : Type u} [CommRing R]
    (S : ShortComplex (ModuleCat.{u} R)) (s : Set R) (hs : Ideal.span s = ⊤)
    (T : s → ShortComplex (ModuleCat.{u} R)) (q : ∀ r, S ⟶ T r)
    [∀ r, IsLocalizedModule.Away r.val (q r).τ₁.hom]
    [∀ r, IsLocalizedModule.Away r.val (q r).τ₂.hom]
    [∀ r, IsLocalizedModule.Away r.val (q r).τ₃.hom]
    (hT : ∀ r, (T r).Exact) : S.Exact := by
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
  apply exact_of_isLocalized_span s hs
    (fun r => (T r).X₁) (fun r => (q r).τ₁.hom)
    (fun r => (T r).X₂) (fun r => (q r).τ₂.hom)
    (fun r => (T r).X₃) (fun r => (q r).τ₃.hom)
  intro r
  have hf : IsLocalizedModule.map (.powers r.val) (q r).τ₁.hom
      (q r).τ₂.hom S.f.hom = (T r).f.hom := by
    apply IsLocalizedModule.linearMap_ext (.powers r.val) (q r).τ₁.hom (q r).τ₂.hom
    rw [IsLocalizedModule.map_comp]
    exact (congrArg ModuleCat.Hom.hom (q r).comm₁₂).symm
  have hg : IsLocalizedModule.map (.powers r.val) (q r).τ₂.hom
      (q r).τ₃.hom S.g.hom = (T r).g.hom := by
    apply IsLocalizedModule.linearMap_ext (.powers r.val) (q r).τ₂.hom (q r).τ₃.hom
    rw [IsLocalizedModule.map_comp]
    exact (congrArg ModuleCat.Hom.hom (q r).comm₂₃).symm
  rw [hf, hg]
  exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp (hT r)


end ModuleCat
