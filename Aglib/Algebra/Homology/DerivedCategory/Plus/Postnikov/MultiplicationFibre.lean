/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Plus.Postnikov.Unit

/-! # The original first homology of a multiplication fibre

Only the original distinguished triangle and the actual H0 epimorphism are used
for the kernel identification. No upper bound on the fibre is assumed.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v w
namespace DerivedCategory.Plus

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- The ACTUAL first homology object is the actual kernel of the next original H1 arrow. -/
def homologyOneKernelIsoOfEpiZero
    (T : Triangle (Plus C)) (hT : T ∈ distTriang (Plus C))
    [Epi ((homologyFunctor C 0).map T.mor₂)] :
    (homologyFunctor C 1).obj T.obj₁ ≅ kernel ((homologyFunctor C 1).map T.mor₂) := by
  let : Mono (homologyOneShortComplex T hT).f := by
    let H := homologyFunctor C 0
    have hEpi : Epi ((H.shift (0 : ℤ)).map T.mor₂) := by
      let e := H.isoShiftZero ℤ
      have hw : (H.shift (0 : ℤ)).map T.mor₂ =
          e.hom.app T.obj₂ ≫ H.map T.mor₂ ≫ e.inv.app T.obj₃ := by
        calc
          _ = ((H.shift (0 : ℤ)).map T.mor₂ ≫ e.hom.app T.obj₃) ≫ e.inv.app T.obj₃ := by
            simp
          _ = _ := by rw [e.hom.naturality]; simp only [Category.assoc]
      rw [hw]
      infer_instance
    have hz : H.homologySequenceδ T 0 1 (by omega) = 0 :=
      (H.homologySequence_epi_shift_map_mor₂_iff T hT 0 1 (by omega)).mp hEpi
    exact (H.homologySequence_mono_shift_map_mor₁_iff T hT 0 1 (by omega)).mpr hz
  have h : (homologyOneShortComplex T hT).Exact :=
    (homologyFunctor C 0).homologySequence_exact₂ T hT 1
  exact h.fIsKernel.conePointUniqueUpToIso (limit.isLimit _)

/-- Kernel uniqueness keeps the literal original H1 inclusion. -/
@[reassoc]
theorem homologyOneKernelIsoOfEpiZero_hom_ι
    (T : Triangle (Plus C)) (hT : T ∈ distTriang (Plus C))
    [Epi ((homologyFunctor C 0).map T.mor₂)] :
    (homologyOneKernelIsoOfEpiZero T hT).hom ≫ kernel.ι ((homologyFunctor C 1).map T.mor₂) =
      (homologyFunctor C 1).map T.mor₁ := by
  dsimp only [homologyOneKernelIsoOfEpiZero]
  exact IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingParallelPair.zero

variable {F B0 : Plus C} (n : ℕ) (i : F ⟶ B0) (δ : B0 ⟶ F⟦(1 : ℤ)⟧)
    (hT : Triangle.mk i (n • 𝟙 B0) δ ∈ distTriang (Plus C))
    [Epi ((homologyFunctor C 0).map (n • 𝟙 B0))]
    {J : C} (e : (homologyFunctor C 1).obj B0 ≅ J)

/-- Any supplied actual H1 identification gives the original scalar kernel, without replacing B0. -/
def homologyOneMultiplicationKernelIso :
    (homologyFunctor C 1).obj F ≅ kernel (n • 𝟙 J) := by
  let : Epi ((homologyFunctor C 0).map (Triangle.mk i (n • 𝟙 B0) δ).mor₂) :=
    inferInstanceAs (Epi ((homologyFunctor C 0).map (n • 𝟙 B0)))
  exact homologyOneKernelIsoOfEpiZero (Triangle.mk i (n • 𝟙 B0) δ) hT ≪≫
    kernel.mapIso ((homologyFunctor C 1).map (n • 𝟙 B0)) (n • 𝟙 J) e e (by
      simp only [CategoryTheory.Functor.map_nsmul, CategoryTheory.Functor.map_id,
        Preadditive.nsmul_comp, Preadditive.comp_nsmul, Category.id_comp, Category.comp_id])

/-- The actual fibre-to-B0 map becomes the actual kernel inclusion under the supplied H1 iso. -/
@[reassoc]
theorem homologyOneMultiplicationKernelIso_hom_ι :
    (homologyOneMultiplicationKernelIso n i δ hT e).hom ≫ kernel.ι (n • 𝟙 J) =
      (homologyFunctor C 1).map i ≫ e.hom := by
  let : Epi ((homologyFunctor C 0).map (Triangle.mk i (n • 𝟙 B0) δ).mor₂) :=
    inferInstanceAs (Epi ((homologyFunctor C 0).map (n • 𝟙 B0)))
  have h := homologyOneKernelIsoOfEpiZero_hom_ι (Triangle.mk i (n • 𝟙 B0) δ) hT
  simp only [homologyOneMultiplicationKernelIso, Iso.trans_hom, Category.assoc,
    kernel.mapIso_hom, kernel.map, kernel.lift_ι]
  rw [← Category.assoc]
  exact congrArg (fun z => z ≫ e.hom) h

end DerivedCategory.Plus
