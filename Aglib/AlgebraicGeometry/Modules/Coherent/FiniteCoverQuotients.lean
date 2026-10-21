/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Coherent.FiniteCoverGluing

/-!
# Coherent quotients from finite local presentations

Compatible quotients of one coherent ambient sheaf are glued by their actual
relation kernels. The resulting quotient retains the specified epimorphism
on every chart. No global realization is supplied as a hypothesis.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

namespace AlgebraicGeometry.Scheme.Modules.Coherent

universe u

/-- Coherent local quotients glue once their actual relation subobjects agree.
The comparisons preserve the original quotient maps, not merely their targets. -/
theorem exists_coherent_glued_quotient_of_finite_openImmersionCover
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    {ι : Type u} [Finite ι] (U : ι → Scheme.{u})
    (j : ∀ i, U i ⟶ X) [∀ i, IsOpenImmersion (j i)]
    (hcover : ∀ x : X, ∃ i, x ∈ (j i).opensRange)
    (M : X.Modules) (hM : affineLocallyFiniteType X M)
    (Q : ∀ i, (U i).Modules)
    (hQ : ∀ i, affineLocallyFiniteType (U i) (Q i))
    (q : ∀ i, M.restrict (j i) ⟶ Q i) [∀ i, Epi (q i)]
    (e : ∀ i k, (kernel (q i)).restrict (pullback.fst (j i) (j k)) ≅
      (kernel (q k)).restrict (pullback.snd (j i) (j k)))
    (he : ∀ i k,
      (restrictFunctor (pullback.fst (j i) (j k))).map (kernel.ι (q i)) ≫
        (overlapRestrictIso (j i) (j k)).hom.app M =
      (e i k).hom ≫
        (restrictFunctor (pullback.snd (j i) (j k))).map (kernel.ι (q k))) :
    ∃ (G : FiniteTypeSheaves X) (p : M ⟶ G.obj), Epi p ∧
      ∃ (c : ∀ i, G.obj.restrict (j i) ≅ Q i),
        ∀ i, (restrictFunctor (j i)).map p ≫ (c i).hom = q i := by
  have hK (i : ι) : affineLocallyFiniteType (U i) (kernel (q i)) := by
    let : IsLocallyNoetherian (U i) := isLocallyNoetherian_of_isOpenImmersion (j i)
    exact (affineLocallyFiniteType (U i)).prop_kernel (q i)
      (affineLocallyFiniteType_restrict (j i) hM) (hQ i)
  obtain ⟨K, s, hs, c, hc⟩ :=
    exists_coherent_glued_subobject_of_finite_openImmersionCover U j hcover M
      (fun i => kernel (q i)) hK (fun i => kernel.ι (q i)) e he
  let : Mono s := hs
  have hG : affineLocallyFiniteType X (cokernel s) :=
    (affineLocallyFiniteType X).prop_cokernel s K.property hM
  let d (i : ι) : cokernel (kernel.ι (q i)) ≅ Q i :=
    (cokernelIsCokernel (kernel.ι (q i))).coconePointUniqueUpToIso
      (Abelian.epiIsCokernelOfKernel _ (limit.isLimit (parallelPair (q i) 0)))
  have hd (i : ι) : cokernel.π (kernel.ι (q i)) ≫ (d i).hom = q i :=
    (cokernelIsCokernel (kernel.ι (q i))).comp_coconePointUniqueUpToIso_hom
      (Abelian.epiIsCokernelOfKernel _ (limit.isLimit (parallelPair (q i) 0)))
      WalkingParallelPair.one
  let b (i : ι) : (cokernel s).restrict (j i) ≅ Q i :=
    PreservesCokernel.iso (restrictFunctor (j i)) s ≪≫
      cokernel.mapIso ((restrictFunctor (j i)).map s) (kernel.ι (q i))
        (c i) (Iso.refl _) (by simpa only [Iso.refl_hom, Category.comp_id] using hc i) ≪≫
      d i
  refine ⟨⟨cokernel s, hG⟩, cokernel.π s, inferInstance, b, ?_⟩
  intro i
  dsimp only [b, Iso.trans_hom]
  rw [← Category.assoc, PreservesCokernel.π_iso_hom]
  simp only [cokernel.mapIso_hom, cokernel.map, cokernel.π_desc_assoc, Iso.refl_hom,
    Category.id_comp, hd]

end AlgebraicGeometry.Scheme.Modules.Coherent
