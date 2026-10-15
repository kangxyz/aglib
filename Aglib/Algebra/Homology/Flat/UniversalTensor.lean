/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Aglib.RingTheory.Flat.Exact
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Actual terminal-cycle flatness from universal tensor exactness

For an original three-term module complex, exactness in its middle after
tensoring with every test module makes the original opcycles map universally
injective. Flatness of the last term therefore makes the actual opcycles
flat. Flatness of the two earlier terms then makes the original image and
kernel flat, through their original quotient and range-restriction maps.
The resulting cochain criterion proves flatness of the actual cycle object.
No flat terminal cycle, purity interface or replacement complex is assumed.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace CategoryTheory.ShortComplex

variable {R : Type u} [CommRing R] (S : ShortComplex (ModuleCat.{v} R))

/-- Actual tensor exactness in the middle makes the tensor of the original
map from opcycles injective. Only tensor right exactness of the original
opcycles projection is needed. -/
theorem fromOpcycles_lTensor_injective_of_exact (N : Type w)
    [AddCommGroup N] [Module R N]
    (h : Function.Exact (S.f.hom.lTensor N) (S.g.hom.lTensor N)) :
    Function.Injective (S.fromOpcycles.hom.lTensor N) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro z hz
  change (S.fromOpcycles.hom.lTensor N) z = 0 at hz
  have hp : Function.Surjective S.pOpcycles.hom :=
    (ModuleCat.epi_iff_surjective S.pOpcycles).mp inferInstance
  obtain ⟨x, rfl⟩ := LinearMap.lTensor_surjective N hp z
  have hg : (S.g.hom.lTensor N) x = 0 := by
    have he := congrArg (fun f : S.X₂ ⟶ S.X₃ => f.hom) S.p_fromOpcycles
    change S.fromOpcycles.hom.comp S.pOpcycles.hom = S.g.hom at he
    rw [← he, LinearMap.lTensor_comp_apply]
    exact hz
  obtain ⟨y, rfl⟩ := (h x).mp hg
  change (S.pOpcycles.hom.lTensor N) ((S.f.hom.lTensor N) y) = 0
  have he := congrArg (fun f : S.X₁ ⟶ S.opcycles => f.hom) S.f_pOpcycles
  change S.pOpcycles.hom.comp S.f.hom = 0 at he
  rw [← LinearMap.lTensor_comp_apply, he]
  simp

/-- The actual native opcycles are flat when all original middle tensor
complexes are exact and the last original term is flat. -/
theorem flat_opcycles_of_universally_lTensor_exact [Module.Flat R S.X₃]
    (h : ∀ (N : Type u) [AddCommGroup N] [Module R N],
      Function.Exact (S.f.hom.lTensor N) (S.g.hom.lTensor N)) :
    Module.Flat R S.opcycles := by
  apply Module.Flat.of_universally_lTensor_injective S.fromOpcycles.hom
  intro N _ _
  exact S.fromOpcycles_lTensor_injective_of_exact N (h N)

/-- The actual image of the first map is flat, using the original cokernel
projection onto the actual flat opcycles. -/
theorem flat_range_f_of_universally_lTensor_exact [Module.Flat R S.X₂] [Module.Flat R S.X₃]
    (h : ∀ (N : Type u) [AddCommGroup N] [Module R N],
      Function.Exact (S.f.hom.lTensor N) (S.g.hom.lTensor N)) :
    Module.Flat R (LinearMap.range S.f.hom) := by
  let := S.flat_opcycles_of_universally_lTensor_exact h
  have hp : Function.Surjective S.pOpcycles.hom :=
    (ModuleCat.epi_iff_surjective S.pOpcycles).mp inferInstance
  let := Module.Flat.ker_of_surjective S.pOpcycles.hom hp
  let T := ShortComplex.mk S.f S.pOpcycles S.f_pOpcycles
  have ht : T.Exact := T.exact_of_g_is_cokernel S.opcyclesIsCokernel
  have he : LinearMap.range S.f.hom = LinearMap.ker S.pOpcycles.hom :=
    ht.moduleCat_range_eq_ker
  exact Module.Flat.of_linearEquiv (LinearEquiv.ofEq _ _ he)

/-- Flatness of all three original terms and universal middle tensor
exactness imply flatness of the actual kernel of the first map. -/
theorem flat_ker_f_of_universally_lTensor_exact
    [Module.Flat R S.X₁] [Module.Flat R S.X₂] [Module.Flat R S.X₃]
    (h : ∀ (N : Type u) [AddCommGroup N] [Module R N],
      Function.Exact (S.f.hom.lTensor N) (S.g.hom.lTensor N)) :
    Module.Flat R (LinearMap.ker S.f.hom) := by
  let := S.flat_range_f_of_universally_lTensor_exact h
  let := Module.Flat.ker_of_surjective S.f.hom.rangeRestrict S.f.hom.surjective_rangeRestrict
  exact Module.Flat.of_linearEquiv
    (LinearEquiv.ofEq _ _ S.f.hom.ker_rangeRestrict.symm)

end CategoryTheory.ShortComplex

namespace CochainComplex

variable {R : Type u} [CommRing R]

/-- The actual terminal cycles are flat when the three neighboring original
terms are flat and the following middle degree remains exact after every
module tensor product. This criterion assumes no bound or model comparison. -/
theorem flat_cycles_of_universally_lTensor_exact (K : CochainComplex (ModuleCat.{v} R) ℤ)
    (b : ℤ) [Module.Flat R (K.X b)] [Module.Flat R (K.X (b + 1))]
    [Module.Flat R (K.X (b + 2))]
    (h : ∀ (N : Type u) [AddCommGroup N] [Module R N],
      Function.Exact ((K.d b (b + 1)).hom.lTensor N)
        ((K.d (b + 1) (b + 2)).hom.lTensor N)) : Module.Flat R (K.cycles b) := by
  let S := K.sc' b (b + 1) (b + 2)
  let : Module.Flat R S.X₁ := by
    change Module.Flat R (K.X b)
    infer_instance
  let : Module.Flat R S.X₂ := by
    change Module.Flat R (K.X (b + 1))
    infer_instance
  let : Module.Flat R S.X₃ := by
    change Module.Flat R (K.X (b + 2))
    infer_instance
  let : Module.Flat R (LinearMap.ker (K.d b (b + 1)).hom) :=
    S.flat_ker_f_of_universally_lTensor_exact h
  let : Module.Flat R ((ModuleCat.kernelCone (K.d b (b + 1))).pt) := by
    change Module.Flat R (LinearMap.ker (K.d b (b + 1)).hom)
    infer_instance
  let E := (K.cyclesIsKernel b (b + 1) (by simp)).conePointUniqueUpToIso
    (ModuleCat.kernelIsLimit (K.d b (b + 1)))
  exact Module.Flat.of_linearEquiv E.toLinearEquiv

end CochainComplex
