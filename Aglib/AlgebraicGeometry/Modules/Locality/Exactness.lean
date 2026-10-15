/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Locality.Isomorphisms
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
/-!
# Detecting module-sheaf exactness on open covers

Zero objects, isomorphisms and short exact sequences are detected on a jointly surjective family
of open immersions. The proofs use original restricted stalks, kernels, cokernels and homology.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u v
namespace AlgebraicGeometry.Scheme.Modules
variable {X : Scheme.{u}} {ι : Type v} (Y : ι → Scheme.{u}) (a : ∀ i, Y i ⟶ X)
  [∀ i, IsOpenImmersion (a i)] (hcover : ∀ x : X, ∃ (i : ι) (y : Y i), a i y = x)

include hcover
lemma isZero_of_restrict_openCover (M : X.Modules)
    (hM : ∀ i, IsZero (M.restrict (a i))) : IsZero M := by
  rw [isZero_iff_stalks]
  intro x
  obtain ⟨i, y, rfl⟩ := hcover x
  exact ((stalkFunctor (Y i) y).map_isZero (hM i)).of_iso
    ((Scheme.Modules.restrictStalkNatIso (a i) y).app M).symm

lemma isIso_of_restrict_openCover {M N : X.Modules} (f : M ⟶ N)
    (hf : ∀ i, IsIso ((Scheme.Modules.restrictFunctor (a i)).map f)) : IsIso f := by
  apply (Scheme.Modules.moduleSheaf_isIso_iff_stalks _).mpr
  intro x
  obtain ⟨i, y, rfl⟩ := hcover x
  let := hf i
  exact (NatIso.isIso_map_iff (Scheme.Modules.restrictStalkNatIso (a i) y) f).mp
    (inferInstanceAs (IsIso ((stalkFunctor (Y i) y).map
      ((Scheme.Modules.restrictFunctor (a i)).map f))))

lemma shortExact_of_restrict_openCover (S : ShortComplex X.Modules)
    (hS : ∀ i, (S.map (Scheme.Modules.restrictFunctor (a i))).ShortExact) : S.ShortExact where
  mono_f := by
    apply Preadditive.mono_of_isZero_kernel
    apply isZero_of_restrict_openCover Y a hcover
    intro i
    let : Mono ((Scheme.Modules.restrictFunctor (a i)).map S.f) := (hS i).mono_f
    exact (isZero_kernel_of_mono ((Scheme.Modules.restrictFunctor (a i)).map S.f)).of_iso
      (PreservesKernel.iso (Scheme.Modules.restrictFunctor (a i)) S.f)
  epi_g := by
    apply Preadditive.epi_of_isZero_cokernel
    apply isZero_of_restrict_openCover Y a hcover
    intro i
    let : Epi ((Scheme.Modules.restrictFunctor (a i)).map S.g) := (hS i).epi_g
    exact (isZero_cokernel_of_epi ((Scheme.Modules.restrictFunctor (a i)).map S.g)).of_iso
      (PreservesCokernel.iso (Scheme.Modules.restrictFunctor (a i)) S.g)
  exact := by
    rw [ShortComplex.exact_iff_isZero_homology]
    apply isZero_of_restrict_openCover Y a hcover
    intro i
    exact ((ShortComplex.exact_iff_isZero_homology _).mp (hS i).exact).of_iso
      (S.mapHomologyIso (Scheme.Modules.restrictFunctor (a i))).symm

end AlgebraicGeometry.Scheme.Modules
