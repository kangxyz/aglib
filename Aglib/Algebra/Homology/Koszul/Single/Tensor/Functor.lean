/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Motivic Cohomology contributors
-/
module

public import Aglib.Algebra.Homology.Koszul.Single.Tensor.Differential

/-!
# Additive functors and one-element Koszul tensors

The two-column decomposition gives an explicit comparison between applying an
additive functor to a one-element tensor complex and tensoring the image
complex. When the functor preserves multiplication by the chosen scalar, the
comparison respects differentials and is a genuine chain isomorphism.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace ChainComplex.Koszul

variable {R : Type u} [CommRing R]
variable (F : ModuleCat R ⥤ ModuleCat R) [F.Additive]
variable (a : R) (K : ChainComplex (ModuleCat R) ℕ)

/-- The image complex under an additive module functor. -/
abbrev mappedComplex := (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K

set_option backward.isDefEq.respectTransparency false in
/-- Mapped old-column and new-column inclusions jointly detect maps in positive degrees. -/
theorem mappedSingleTensor_hom_ext {A : ModuleCat R} (n : ℕ)
    {f g : F.obj ((HomologicalComplex.tensorObj (singleComplex R a) K).X (n + 1)) ⟶ A}
    (h₀ : F.map (singleTensorιZero a K (n + 1)) ≫ f =
      F.map (singleTensorιZero a K (n + 1)) ≫ g)
    (h₁ : F.map (singleTensorιOne a K n) ≫ f = F.map (singleTensorιOne a K n) ≫ g) :
    f = g := by
  have hd : F.map (singleTensorπZero a K (n + 1)) ≫
        F.map (singleTensorιZero a K (n + 1)) +
      F.map (singleTensorπOne a K n) ≫ F.map (singleTensorιOne a K n) = 𝟙 _ := by
    rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_add, singleTensor_decomposition]
    exact F.map_id _
  have h := congrArg (fun p => p ≫ f) hd
  have h' := congrArg (fun p => p ≫ g) hd
  simp only [Preadditive.add_comp, Category.assoc, Category.id_comp] at h h'
  rw [h₀, h₁] at h
  exact h.symm.trans h'

omit [F.Additive] in
set_option backward.isDefEq.respectTransparency false in
/-- The mapped old-column inclusion detects maps in degree zero. -/
theorem mappedSingleTensor_hom_ext_zero {A : ModuleCat R}
    {f g : F.obj ((HomologicalComplex.tensorObj (singleComplex R a) K).X 0) ⟶ A}
    (h : F.map (singleTensorιZero a K 0) ≫ f = F.map (singleTensorιZero a K 0) ≫ g) :
    f = g := by
  have hd : F.map (singleTensorπZero a K 0) ≫ F.map (singleTensorιZero a K 0) = 𝟙 _ := by
    rw [← Functor.map_comp, singleTensor_decomposition_zero]
    exact F.map_id _
  have h' := congrArg (fun p => F.map (singleTensorπZero a K 0) ≫ p) h
  simpa only [← Category.assoc, hd, Category.id_comp] using h'

/-- The explicit termwise comparison from the image of a one-element tensor. -/
noncomputable def singleTensorMapToX : (n : ℕ) →
    F.obj ((HomologicalComplex.tensorObj (singleComplex R a) K).X n) ⟶
      (HomologicalComplex.tensorObj (singleComplex R a) (mappedComplex F K)).X n
  | 0 => F.map (singleTensorπZero a K 0) ≫ singleTensorιZero a (mappedComplex F K) 0
  | n + 1 =>
      F.map (singleTensorπZero a K (n + 1)) ≫
          singleTensorιZero a (mappedComplex F K) (n + 1) +
        F.map (singleTensorπOne a K n) ≫ singleTensorιOne a (mappedComplex F K) n

/-- The explicit inverse comparison on terms. -/
noncomputable def singleTensorMapFromX : (n : ℕ) →
    (HomologicalComplex.tensorObj (singleComplex R a) (mappedComplex F K)).X n ⟶
      F.obj ((HomologicalComplex.tensorObj (singleComplex R a) K).X n)
  | 0 => singleTensorπZero a (mappedComplex F K) 0 ≫ F.map (singleTensorιZero a K 0)
  | n + 1 =>
      singleTensorπZero a (mappedComplex F K) (n + 1) ≫
          F.map (singleTensorιZero a K (n + 1)) +
        singleTensorπOne a (mappedComplex F K) n ≫ F.map (singleTensorιOne a K n)

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem mappedιZero_singleTensorMapToX (n : ℕ) :
    F.map (singleTensorιZero a K n) ≫ singleTensorMapToX F a K n =
      singleTensorιZero a (mappedComplex F K) n := by
  cases n <;> simp [singleTensorMapToX, Preadditive.comp_add, ← Category.assoc,
    ← Functor.map_comp]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem mappedιOne_singleTensorMapToX (n : ℕ) :
    F.map (singleTensorιOne a K n) ≫ singleTensorMapToX F a K (n + 1) =
      singleTensorιOne a (mappedComplex F K) n := by
  simp [singleTensorMapToX, Preadditive.comp_add, ← Category.assoc, ← Functor.map_comp]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem ιZero_singleTensorMapFromX (n : ℕ) :
    singleTensorιZero a (mappedComplex F K) n ≫ singleTensorMapFromX F a K n =
      F.map (singleTensorιZero a K n) := by
  cases n <;> simp [singleTensorMapFromX, Preadditive.comp_add, ← Category.assoc]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem ιOne_singleTensorMapFromX (n : ℕ) :
    singleTensorιOne a (mappedComplex F K) n ≫ singleTensorMapFromX F a K (n + 1) =
      F.map (singleTensorιOne a K n) := by
  simp [singleTensorMapFromX, Preadditive.comp_add, ← Category.assoc]

/-- The comparison is an actual isomorphism in every degree. -/
noncomputable def singleTensorMapXIso (n : ℕ) :
    F.obj ((HomologicalComplex.tensorObj (singleComplex R a) K).X n) ≅
      (HomologicalComplex.tensorObj (singleComplex R a) (mappedComplex F K)).X n where
  hom := singleTensorMapToX F a K n
  inv := singleTensorMapFromX F a K n
  hom_inv_id := by
    cases n with
    | zero =>
      apply mappedSingleTensor_hom_ext_zero F a K
      simp only [← Category.assoc, mappedιZero_singleTensorMapToX,
        ιZero_singleTensorMapFromX, Category.comp_id]
    | succ n =>
      apply mappedSingleTensor_hom_ext F a K n
      · simp only [← Category.assoc, mappedιZero_singleTensorMapToX,
          ιZero_singleTensorMapFromX, Category.comp_id]
      · simp only [← Category.assoc, mappedιOne_singleTensorMapToX,
          ιOne_singleTensorMapFromX, Category.comp_id]
  inv_hom_id := by
    cases n with
    | zero =>
      apply singleTensor_hom_ext_zero a (mappedComplex F K)
      simp only [← Category.assoc, ιZero_singleTensorMapFromX,
        mappedιZero_singleTensorMapToX, Category.comp_id]
    | succ n =>
      apply singleTensor_hom_ext a (mappedComplex F K) n
      · simp only [← Category.assoc, ιZero_singleTensorMapFromX,
          mappedιZero_singleTensorMapToX, Category.comp_id]
      · simp only [← Category.assoc, ιOne_singleTensorMapFromX,
          mappedιOne_singleTensorMapToX, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/-- Scalar compatibility makes the explicit comparison commute with differentials. -/
theorem singleTensorMapToX_comm
    (ha : ∀ X : ModuleCat R, F.map (ModuleCat.ofHom (LinearMap.lsmul R X a)) =
      ModuleCat.ofHom (LinearMap.lsmul R (F.obj X) a)) (n : ℕ) :
    singleTensorMapToX F a K (n + 1) ≫
        (HomologicalComplex.tensorObj (singleComplex R a) (mappedComplex F K)).d (n + 1) n =
      F.map ((HomologicalComplex.tensorObj (singleComplex R a) K).d (n + 1) n) ≫
        singleTensorMapToX F a K n := by
  apply mappedSingleTensor_hom_ext F a K n
  · rw [← Category.assoc, mappedιZero_singleTensorMapToX, singleTensorιZero_d]
    rw [← Category.assoc, ← Functor.map_comp, singleTensorιZero_d,
      Functor.map_comp, Category.assoc, mappedιZero_singleTensorMapToX]
    rfl
  · rw [← Category.assoc, mappedιOne_singleTensorMapToX]
    cases n with
    | zero =>
      rw [singleTensorιOne_zero_d, ← Category.assoc, ← Functor.map_comp,
        singleTensorιOne_zero_d, Functor.map_comp, Category.assoc,
        mappedιZero_singleTensorMapToX, ha]
      rfl
    | succ n =>
      rw [singleTensorιOne_d, ← Category.assoc, ← Functor.map_comp,
        singleTensorιOne_d, Functor.map_sub, Preadditive.sub_comp, Functor.map_comp,
        Functor.map_comp, Category.assoc, Category.assoc,
        mappedιZero_singleTensorMapToX, mappedιOne_singleTensorMapToX, ha]
      rfl

/-- An additive functor preserving the scalar gives a genuine one-element tensor comparison. -/
noncomputable def singleTensorMapIso
    (ha : ∀ X : ModuleCat R, F.map (ModuleCat.ofHom (LinearMap.lsmul R X a)) =
      ModuleCat.ofHom (LinearMap.lsmul R (F.obj X) a)) :
    mappedComplex F (HomologicalComplex.tensorObj (singleComplex R a) K) ≅
      HomologicalComplex.tensorObj (singleComplex R a) (mappedComplex F K) :=
  HomologicalComplex.Hom.isoOfComponents (singleTensorMapXIso F a K) (by
    intro i j hij
    have hi : j + 1 = i := hij
    subst i
    exact singleTensorMapToX_comm F a K ha j)

end ChainComplex.Koszul
