/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.Flat.BoundedAcyclic
public import Aglib.Algebra.Homology.Flat.Kernel
public import Aglib.Algebra.Homology.CochainComplex.MapTruncation
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric

/-!
# Arbitrary module tensor on bounded flat complexes and good truncations

Native tensor with an arbitrary base module preserves acyclicity of an actually
bounded-above flat complex. It consequently preserves the original quasi-isomorphism
between two such complexes, by tensoring the actual bounded flat cone and using its
native mapped-cone comparison. No flatness of the tensor coefficient is assumed.

Universal boundary tensor exactness also proves the precise native kernel preservation
needed for the existing good-truncation comparison. Its forward map retains the
original mapped truncation inclusion. No preservation-of-homology instance is installed.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomologicalComplex

universe u

namespace CochainComplex

variable {R : Type u} [CommRing R]

/-- The actual left tensor by any module preserves an acyclic bounded-above flat complex. -/
theorem acyclic_tensorLeft_of_flat (J : ModuleCat.{u} R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (b : ℤ)
    [K.IsStrictlyLE b] [∀ i, Module.Flat R (K.X i)] (hK : K.Acyclic) :
    (((tensorLeft J).mapHomologicalComplex (.up ℤ)).obj K).Acyclic := by
  intro i
  apply (exactAt_iff' _ (i - 1) i (i + 1) (by simp) (by simp)).mpr
  apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
  exact K.universally_lTensor_exact_of_acyclic b hK i J

/-- The actual right tensor by any module preserves an acyclic bounded-above flat complex. -/
theorem acyclic_tensorRight_of_flat (J : ModuleCat.{u} R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (b : ℤ)
    [K.IsStrictlyLE b] [∀ i, Module.Flat R (K.X i)] (hK : K.Acyclic) :
    (((tensorRight J).mapHomologicalComplex (.up ℤ)).obj K).Acyclic := by
  have h := acyclic_tensorLeft_of_flat J K b hK
  let e := (NatIso.mapHomologicalComplex
    (BraidedCategory.tensorLeftIsoTensorRight J) (.up ℤ)).app K
  intro i
  exact (h i).of_iso e

/-- The literal tensor of a quasi-isomorphism between bounded-above flat complexes is a
quasi-isomorphism for any module, by the original bounded flat cone. -/
theorem quasiIso_tensorRight_of_flat (J : ModuleCat.{u} R)
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L)
    (a b : ℤ) [K.IsStrictlyLE a] [L.IsStrictlyLE b]
    [∀ i, Module.Flat R (K.X i)] [∀ i, Module.Flat R (L.X i)] [QuasiIso f] :
    QuasiIso (((tensorRight J).mapHomologicalComplex (.up ℤ)).map f) := by
  let (i : ℤ) : Module.Flat R ((mappingCone f).X i) := flat_X_mappingCone f i
  let : (mappingCone f).IsStrictlyLE (max a b) := by
    rw [isStrictlyLE_iff]
    intro i hi
    apply (mappingCone.isZero_X_iff f i).mpr
    exact ⟨K.isZero_of_isStrictlyLE a (i + 1) (by omega),
      L.isZero_of_isStrictlyLE b i (by omega)⟩
  have h := acyclic_tensorRight_of_flat J (mappingCone f) (max a b)
    (mappingCone_acyclic_of_quasiIso f)
  apply quasiIso_of_mappingCone_acyclic
  intro i
  exact (h i).of_iso (mappingCone.mapHomologicalComplexIso f (tensorRight J))

end CochainComplex

namespace CategoryTheory.ShortComplex

variable {R : Type u} [CommRing R] (S : ShortComplex (ModuleCat.{u} R))
  [Module.Flat R S.X₂] [Module.Flat R S.X₃]

/-- Universal tensor exactness proves preservation of this original kernel under native
left tensor by an arbitrary module. -/
theorem tensorLeft_preservesKernel_of_universally_lTensor_exact (J : ModuleCat.{u} R)
    (h : ∀ (N : Type u) [AddCommGroup N] [Module R N],
      Function.Exact (S.f.hom.lTensor N) (S.g.hom.lTensor N)) :
    PreservesLimit (parallelPair S.f 0) (tensorLeft J) := by
  let F := tensorLeft J
  have H : Function.Exact
      (F.map (ModuleCat.ofHom (LinearMap.ker S.f.hom).subtype)).hom (F.map S.f).hom ∧
      Function.Injective (F.map (ModuleCat.ofHom (LinearMap.ker S.f.hom).subtype)).hom :=
    S.kernel_lTensor_exact_and_injective_of_universally_exact h J
  apply preservesLimit_of_preserves_limit_cone (ModuleCat.kernelIsLimit S.f)
  refine (KernelFork.isLimitMapConeEquiv (ModuleCat.kernelCone S.f) F).symm ?_
  exact ModuleCat.isLimitKernelFork
    (F.map (ModuleCat.ofHom (LinearMap.ker S.f.hom).subtype)) (F.map S.f) H.1 H.2

/-- Universal tensor exactness proves preservation of this original kernel under native
right tensor by an arbitrary module. -/
theorem tensorRight_preservesKernel_of_universally_lTensor_exact (J : ModuleCat.{u} R)
    (h : ∀ (N : Type u) [AddCommGroup N] [Module R N],
      Function.Exact (S.f.hom.lTensor N) (S.g.hom.lTensor N)) :
    PreservesLimit (parallelPair S.f 0) (tensorRight J) := by
  let := S.tensorLeft_preservesKernel_of_universally_lTensor_exact J h
  exact preservesLimit_of_natIso (parallelPair S.f 0)
    (BraidedCategory.tensorLeftIsoTensorRight J)

end CategoryTheory.ShortComplex

namespace CochainComplex

variable {R : Type u} [CommRing R] (J : ModuleCat.{u} R)
  (K : CochainComplex (ModuleCat.{u} R) ℤ) (b : ℤ)
  [Module.Flat R (K.X (b + 1))] [Module.Flat R (K.X (b + 2))]

/-- The native good truncation commutes with arbitrary module tensor when universal
boundary exactness proves its original kernel is preserved. -/
def tensorRightTruncLEIso
    (h : ∀ (N : Type u) [AddCommGroup N] [Module R N],
      Function.Exact ((K.d b (b + 1)).hom.lTensor N)
        ((K.d (b + 1) (b + 2)).hom.lTensor N)) :
    ((tensorRight J).mapHomologicalComplex (.up ℤ)).obj (K.truncLE b) ≅
      CochainComplex.truncLE (((tensorRight J).mapHomologicalComplex (.up ℤ)).obj K) b := by
  let S := K.sc' b (b + 1) (b + 2)
  let : Module.Flat R S.X₂ := inferInstanceAs (Module.Flat R (K.X (b + 1)))
  let : Module.Flat R S.X₃ := inferInstanceAs (Module.Flat R (K.X (b + 2)))
  let : PreservesLimit (parallelPair (K.d b (b + 1)) 0) (tensorRight J) :=
    S.tensorRight_preservesKernel_of_universally_lTensor_exact J h
  exact K.mapTruncLEIso (tensorRight J) b

/-- The canonical tensor/truncation comparison retains the literal mapped original inclusion. -/
@[reassoc]
theorem tensorRightTruncLEIso_hom_ιTruncLE
    (h : ∀ (N : Type u) [AddCommGroup N] [Module R N],
      Function.Exact ((K.d b (b + 1)).hom.lTensor N)
        ((K.d (b + 1) (b + 2)).hom.lTensor N)) :
    (tensorRightTruncLEIso J K b h).hom ≫
        CochainComplex.ιTruncLE
          (((tensorRight J).mapHomologicalComplex (.up ℤ)).obj K) b =
      ((tensorRight J).mapHomologicalComplex (.up ℤ)).map (K.ιTruncLE b) := by
  let S := K.sc' b (b + 1) (b + 2)
  let : Module.Flat R S.X₂ := inferInstanceAs (Module.Flat R (K.X (b + 1)))
  let : Module.Flat R S.X₃ := inferInstanceAs (Module.Flat R (K.X (b + 2)))
  let : PreservesLimit (parallelPair (K.d b (b + 1)) 0) (tensorRight J) :=
    S.tensorRight_preservesKernel_of_universally_lTensor_exact J h
  exact K.mapTruncLEIso_hom_ιTruncLE (tensorRight J) b

end CochainComplex
