/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Coherent.Gluing
public import Aglib.AlgebraicGeometry.Modules.Coherent.Homology
public import Aglib.CategoryTheory.Limits.Shapes.Products

/-!
# Coherent subobjects on a finite open cover

The kernel of the product of the original adjunction/cokernel obstructions
assembles compatible local subobjects. The local comparison isomorphisms
retain the original inclusions into the ambient module sheaf.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

namespace AlgebraicGeometry.Scheme.Modules.Coherent

universe u

/-- Compatible coherent subobjects of an ambient module on a finite open cover
are the restrictions of one coherent subobject, with unchanged inclusions. -/
theorem exists_coherent_glued_subobject_of_finite_openImmersionCover
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    {ι : Type u} [Finite ι] (U : ι → Scheme.{u})
    (j : ∀ i, U i ⟶ X) [∀ i, IsOpenImmersion (j i)]
    (hcover : ∀ x : X, ∃ i, x ∈ (j i).opensRange)
    (M : X.Modules) (A : ∀ i, (U i).Modules)
    (hA : ∀ i, affineLocallyFiniteType (U i) (A i))
    (s : ∀ i, A i ⟶ M.restrict (j i)) [∀ i, Mono (s i)]
    (e : ∀ i k, (A i).restrict (pullback.fst (j i) (j k)) ≅
      (A k).restrict (pullback.snd (j i) (j k)))
    (he : ∀ i k, (restrictFunctor (pullback.fst (j i) (j k))).map (s i) ≫
        (overlapRestrictIso (j i) (j k)).hom.app M =
      (e i k).hom ≫ (restrictFunctor (pullback.snd (j i) (j k))).map (s k)) :
    ∃ (N : FiniteTypeSheaves X) (t : N.obj ⟶ M), Mono t ∧
      ∃ (c : ∀ i, N.obj.restrict (j i) ≅ A i),
        ∀ i, (restrictFunctor (j i)).map t = (c i).hom ≫ s i := by
  classical
  let T : ι → X.Modules := fun i => (pushforward (j i)).obj (cokernel (s i))
  let f : ∀ i, M ⟶ T i := fun i => subobjectObstruction (j i) (s i)
  let l : M ⟶ ∏ᶜ T := Pi.lift f
  have hzero (i : ι) : s i ≫ (restrictFunctor (j i)).map l = 0 := by
    apply map_pi_lift_comp_eq_zero
    intro k
    exact (overlapCompatible_obstruction_zero (j i) (j k) (s i) (s k)
      (e i k) (he i k)).1
  let hlocal (i : ι) := isKernelOfComp
    ((restrictFunctor (j i)).map (Pi.π T i))
    ((restrictFunctor (j i)).map (f i))
    (subobjectObstructionKernelIsLimit (j i) (s i)) (hzero i)
    (by rw [← Functor.map_comp, Pi.lift_comp_π])
  let hglobal (i : ι) :=
    KernelFork.mapIsLimit _ (kernelIsKernel l) (restrictFunctor (j i))
  let c (i : ι) : (kernel l).restrict (j i) ≅ A i :=
    (hglobal i).conePointUniqueUpToIso (hlocal i)
  have hcoh : affineLocallyFiniteType X (kernel l) := by
    apply affineLocallyFiniteType_of_openNeighborhoods
    intro x
    obtain ⟨i, hi⟩ := hcover x
    refine ⟨(j i).opensRange, hi, ?_⟩
    exact affineLocallyFiniteType_restrict_opensRange (j i) (kernel l)
      ((affineLocallyFiniteType (U i)).prop_of_iso (c i).symm (hA i))
  refine ⟨⟨kernel l, hcoh⟩, kernel.ι l, inferInstance, c, ?_⟩
  intro i
  exact ((hglobal i).conePointUniqueUpToIso_hom_comp (hlocal i)
    WalkingParallelPair.zero).symm

end AlgebraicGeometry.Scheme.Modules.Coherent
