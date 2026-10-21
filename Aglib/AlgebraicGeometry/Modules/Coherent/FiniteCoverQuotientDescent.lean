/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Coherent.FiniteCoverQuotients

/-!
# Descent of the original finite-cover quotient maps

Overlap comparisons of local quotient modules induce compatible relation
kernels automatically. Thus local presentations glue without separately
postulating relation gluing data or any global coefficient realization.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

namespace AlgebraicGeometry.Scheme.Modules.Coherent

universe u

/-- Local quotients of a coherent module, with overlap identifications that
preserve their actual epimorphisms, determine a global coherent quotient.
No independent cocycle condition is necessary: the original epimorphisms
force the relation subobjects on every overlap to agree. -/
theorem exists_coherent_quotient_of_finite_openImmersionCover
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    {ι : Type u} [Finite ι] (U : ι → Scheme.{u})
    (j : ∀ i, U i ⟶ X) [∀ i, IsOpenImmersion (j i)]
    (hcover : ∀ x : X, ∃ i, x ∈ (j i).opensRange)
    (M : X.Modules) (hM : affineLocallyFiniteType X M)
    (Q : ∀ i, (U i).Modules)
    (hQ : ∀ i, affineLocallyFiniteType (U i) (Q i))
    (q : ∀ i, M.restrict (j i) ⟶ Q i) [∀ i, Epi (q i)]
    (e : ∀ i k, (Q i).restrict (pullback.fst (j i) (j k)) ≅
      (Q k).restrict (pullback.snd (j i) (j k)))
    (he : ∀ i k,
      (restrictFunctor (pullback.fst (j i) (j k))).map (q i) ≫ (e i k).hom =
      (overlapRestrictIso (j i) (j k)).hom.app M ≫
        (restrictFunctor (pullback.snd (j i) (j k))).map (q k)) :
    ∃ (G : FiniteTypeSheaves X) (p : M ⟶ G.obj), Epi p ∧
      ∃ (c : ∀ i, G.obj.restrict (j i) ≅ Q i),
        ∀ i, (restrictFunctor (j i)).map p ≫ (c i).hom = q i := by
  let d (i k : ι) :=
    PreservesKernel.iso (restrictFunctor (pullback.fst (j i) (j k))) (q i) ≪≫
      kernel.mapIso
        ((restrictFunctor (pullback.fst (j i) (j k))).map (q i))
        ((restrictFunctor (pullback.snd (j i) (j k))).map (q k))
        ((overlapRestrictIso (j i) (j k)).app M) (e i k) (he i k) ≪≫
      (PreservesKernel.iso (restrictFunctor (pullback.snd (j i) (j k))) (q k)).symm
  apply exists_coherent_glued_quotient_of_finite_openImmersionCover U j hcover M hM
    Q hQ q d
  intro i k
  dsimp only [d, Iso.trans_hom, Iso.symm_hom]
  simp only [Category.assoc, PreservesKernel.iso_inv_ι, kernel.mapIso_hom,
    kernel.map, kernel.lift_ι, PreservesKernel.iso_hom, kernelComparison_comp_ι_assoc]
  rfl

end AlgebraicGeometry.Scheme.Modules.Coherent
