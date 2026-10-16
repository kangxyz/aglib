/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Flat.Generators
public import Mathlib.Algebra.Homology.LeftResolution.Basic
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.Algebra.Homology.QuasiIso

/-!
# Functorial actual flat sheaf resolutions

The canonical open-free cover is functorial in the target module sheaf.
Iterating it on actual kernels produces an actual complex of stalkwise-flat
module sheaves, exact in every positive degree. Nothing in the construction
assumes the existence of a flat replacement or of a derived equivalence.

Source: Quillen/AlgebraicGeometry/Scheme/Sheaf/FlatResolution.lean,
actual dirty integration with Git HEAD 6db56ddd3fdb898ef5de29d5fe51a0c61f9ba116.
SHA256: 6061d66af29ce7c8648c6a925fd146c9dbf2fe89412f461e97d3ef25b259f7d4.
Selection: the complete ordinary flat-resolution producer. Universes,
objects, actual cover/augmentation maps and proofs are unchanged.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open HomologicalComplex
namespace AlgebraicGeometry.Scheme.Modules

/-- The map of explicit free covers sends each local-section generator to its image. -/
def flatCoverMap {X : Scheme.{u}} {M N : X.Modules} (p : M ⟶ N) :
    flatCover M ⟶ flatCover N :=
  Sigma.desc (fun s : localSectionIndex M =>
    Sigma.ι (fun t : localSectionIndex N => openFree X t.1)
      (⟨s.1, p.app s.1 s.2⟩ : localSectionIndex N))

/-- Actual open-free covers form a functor on all module sheaves. -/
def flatCoverFunctor (X : Scheme.{u}) : X.Modules ⥤ X.Modules where
  obj := flatCover
  map := flatCoverMap
  map_id M := by
    apply Sigma.hom_ext
    intro s
    simp only [flatCoverMap, Sigma.ι_comp_desc]
    erw [Category.comp_id]
    rfl
  map_comp p q := by
    apply Sigma.hom_ext
    intro s
    simp [flatCoverMap]

/-- The actual epimorphic cover is natural in the target module sheaf. -/
def flatCoverAugmentation (X : Scheme.{u}) : flatCoverFunctor X ⟶ 𝟭 X.Modules where
  app := flatCoverπ
  naturality {M N} p := by
    apply Sigma.hom_ext
    intro s
    dsimp [flatCoverFunctor, flatCoverMap, flatCoverπ]
    simp only [Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc]
    apply (openFreeHomEquiv X s.1 N).injective
    simp only [Equiv.apply_symm_apply, openFreeHomEquiv_comp]

/-- A genuine left resolution datum, constructed from the proved open-free covers. -/
def flatSheafLeftResolution (X : Scheme.{u}) :
    Abelian.LeftResolution (stalkwiseFlat X).ι where
  F := (stalkwiseFlat X).lift (flatCoverFunctor X) (fun M => flatCover_stalkwiseFlat M)
  π := flatCoverAugmentation X
  epi_π_app M := flatCoverπ_epi M

/-- The explicit flat resolution, regarded in the ambient module-sheaf category. -/
def flatResolution (X : Scheme.{u}) : X.Modules ⥤ ChainComplex X.Modules ℕ :=
  (flatSheafLeftResolution X).chainComplexFunctor ⋙
    (stalkwiseFlat X).ι.mapHomologicalComplex (ComplexShape.down ℕ)

/-- Every term of this actual resolution has flat actual module stalks. -/
theorem flatResolution_term_flat (X : Scheme.{u}) (M : X.Modules) (n : ℕ) :
    stalkwiseFlat X (((flatResolution X).obj M).X n) :=
  (((flatSheafLeftResolution X).chainComplex M).X n).property

/-- Exactness of the actual kernel-by-kernel flat resolution in all positive degrees. -/
theorem flatResolution_exactAt_succ (X : Scheme.{u}) (M : X.Modules) (n : ℕ) :
    ((flatResolution X).obj M).ExactAt (n + 1) :=
  (flatSheafLeftResolution X).exactAt_map_chainComplex_succ M n

/-- The augmentation in degree zero of the actual flat resolution. -/
def flatResolutionπ (X : Scheme.{u}) (M : X.Modules) :
    ((flatResolution X).obj M).X 0 ⟶ M :=
  (stalkwiseFlat X).ι.map ((flatSheafLeftResolution X).chainComplexXZeroIso M).hom ≫
    flatCoverπ M

instance flatResolutionπ_epi (X : Scheme.{u}) (M : X.Modules) : Epi (flatResolutionπ X M) := by
  unfold flatResolutionπ
  infer_instance

/-- The augmentation kills the first actual differential. -/
theorem flatResolution_d_comp_π (X : Scheme.{u}) (M : X.Modules) :
    ((flatResolution X).obj M).d 1 0 ≫ flatResolutionπ X M = 0 := by
  change (stalkwiseFlat X).ι.map (((flatSheafLeftResolution X).chainComplex M).d 1 0) ≫
    ((stalkwiseFlat X).ι.map ((flatSheafLeftResolution X).chainComplexXZeroIso M).hom ≫
      flatCoverπ M) = 0
  rw [Abelian.LeftResolution.map_chainComplex_d_1_0]
  simp [flatSheafLeftResolution, flatCoverAugmentation]

/-- The actual augmented chain map from the flat resolution to the original sheaf. -/
def flatResolutionToSingle (X : Scheme.{u}) (M : X.Modules) :
    (flatResolution X).obj M ⟶ (ChainComplex.single₀ X.Modules).obj M :=
  (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨flatResolutionπ X M, flatResolution_d_comp_π X M⟩

/-- Exactness at the augmentation: its kernel is the image of the first differential. -/
theorem flatResolution_exact_at_augmentation (X : Scheme.{u}) (M : X.Modules) :
    (ShortComplex.mk _ _ (flatResolution_d_comp_π X M)).Exact := by
  let I := (stalkwiseFlat X).ι
  let Λ := flatSheafLeftResolution X
  let T := ShortComplex.mk (kernel.ι (flatCoverπ M)) (flatCoverπ M) (kernel.condition _)
  let φ : ShortComplex.mk _ _ (flatResolution_d_comp_π X M) ⟶ T :=
    { τ₁ := I.map (Λ.chainComplexXOneIso M).hom ≫ flatCoverπ (kernel (flatCoverπ M))
      τ₂ := I.map (Λ.chainComplexXZeroIso M).hom
      τ₃ := 𝟙 M
      comm₁₂ := by
        change _ = I.map ((Λ.chainComplex M).d 1 0) ≫ _
        rw [Abelian.LeftResolution.map_chainComplex_d_1_0]
        simp [T, I, Λ, flatSheafLeftResolution, flatCoverAugmentation]
      comm₂₃ := by simp [T, I, Λ, flatResolutionπ] }
  have : Epi φ.τ₁ := by dsimp [φ]; infer_instance
  have : IsIso φ.τ₂ := by dsimp [φ]; infer_instance
  have : Mono φ.τ₃ := by dsimp [φ]; infer_instance
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mpr
    (T.exact_of_f_is_kernel (kernelIsKernel (flatCoverπ M)))

/-- The actual functorial flat resolution is quasi-isomorphic to the original sheaf. -/
instance flatResolutionToSingle_quasiIso (X : Scheme.{u}) (M : X.Modules) :
    QuasiIso (flatResolutionToSingle X M) := ⟨fun n => by
  cases n with
  | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
      · exact ⟨flatResolution_exact_at_augmentation X M, flatResolutionπ_epi X M⟩
      all_goals simp [HomologicalComplex.shortComplexFunctor']
  | succ n =>
      rw [quasiIsoAt_iff_exactAt']
      · exact flatResolution_exactAt_succ X M n
      · exact ChainComplex.exactAt_succ_single_obj M n⟩

end AlgebraicGeometry.Scheme.Modules
