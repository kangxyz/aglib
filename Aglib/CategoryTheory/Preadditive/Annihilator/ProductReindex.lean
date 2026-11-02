/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Preadditive.Annihilator.Kernels

/-! # Original-index scalar-kernel products and reindex comparison

The scalar kernel of the original product of functor images is the product of
the same functors applied to the original scalar kernels. The construction
uses the actual preserved-kernel comparisons. Its original kernel inclusions
and product projections identify it with the comparison obtained by reindexing
through any equivalent index type. No positivity condition on the scalar or
choice of a finite enumeration is needed for the construction.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits

namespace CategoryTheory.Preadditive

universe uC vC uD vD w w'

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  {D : Type uD} [Category.{vD} D] [Preadditive D]

private theorem scalarKernelIso_hom_ι
    (L : D ⥤ C) [L.Additive] [PreservesFiniteLimits L] (A : D) (n : ℕ)
    [HasKernel (n • 𝟙 A)] [HasKernel (n • 𝟙 (L.obj A))] :
    (nsmulKernelIso L A n).hom ≫ kernel.ι (n • 𝟙 (L.obj A)) =
      L.map (kernel.ι (n • 𝟙 A)) := by
  apply (cancel_epi (nsmulKernelIso L A n).inv).mp
  simpa only [Iso.inv_hom_id_assoc] using (nsmulKernelIso_inv_ι L A n).symm

section Products

variable (n : ℕ) {I : Type w} (L : I → D ⥤ C) (A : I → D)
  [∀ i, (L i).Additive] [∀ i, PreservesFiniteLimits (L i)]
  [∀ i, HasKernel (n • 𝟙 (A i))]
  [∀ i, HasKernel (n • 𝟙 ((L i).obj (A i)))]
  [HasProduct (fun i => (L i).obj (A i))]
  [HasProduct (nsmulKernelProductFamily n (fun i => (L i).obj (A i)))]
  [HasProduct (fun i => (L i).obj (kernel (n • 𝟙 (A i))))]

variable [HasKernel (n • 𝟙 (∏ᶜ fun i => (L i).obj (A i)))]

/-- The complete original-index scalar-kernel product comparison, using the
actual additive left exact functors and their original value kernels. -/
def nsmulKernelProductFunctorIso :
    kernel (n • 𝟙 (∏ᶜ fun i => (L i).obj (A i))) ≅
      ∏ᶜ fun i => (L i).obj (kernel (n • 𝟙 (A i))) :=
  nsmulKernelProductIso n (fun i => (L i).obj (A i)) ≪≫ {
    hom := Limits.Pi.map
      (f := nsmulKernelProductFamily n (fun i => (L i).obj (A i)))
      (g := fun i => (L i).obj (kernel (n • 𝟙 (A i))))
      (fun i => (nsmulKernelIso (L i) (A i) n).inv)
    inv := Limits.Pi.map
      (f := fun i => (L i).obj (kernel (n • 𝟙 (A i))))
      (g := nsmulKernelProductFamily n (fun i => (L i).obj (A i)))
      (fun i => (nsmulKernelIso (L i) (A i) n).hom)
    hom_inv_id := by simp only [Limits.Pi.map_comp_map, Iso.inv_hom_id, Limits.Pi.map_id]
    inv_hom_id := by simp only [Limits.Pi.map_comp_map, Iso.hom_inv_id, Limits.Pi.map_id] }

/-- Every backward coordinate retains the original mapped value-kernel
inclusion, after the original whole-product kernel inclusion. -/
@[reassoc]
theorem nsmulKernelProductFunctorIso_inv_ι_π (i : I) :
    (nsmulKernelProductFunctorIso n L A).inv ≫
        kernel.ι (n • 𝟙 (∏ᶜ fun i => (L i).obj (A i))) ≫
          Pi.π (fun i => (L i).obj (A i)) i =
      Pi.π (fun i => (L i).obj (kernel (n • 𝟙 (A i)))) i ≫
        (L i).map (kernel.ι (n • 𝟙 (A i))) := by
  simp only [nsmulKernelProductFunctorIso, Iso.trans_inv, Category.assoc]
  change Limits.Pi.map
      (f := fun i => (L i).obj (kernel (n • 𝟙 (A i))))
      (g := nsmulKernelProductFamily n (fun i => (L i).obj (A i)))
      (fun i => (nsmulKernelIso (L i) (A i) n).hom) ≫
        nsmulKernelProductBackward n (fun i => (L i).obj (A i)) ≫
        kernel.ι (n • 𝟙 (∏ᶜ fun i => (L i).obj (A i))) ≫
          Pi.π (fun i => (L i).obj (A i)) i = _
  rw [nsmulKernelProductBackward_inclusion_assoc, nsmulKernelProductInclusion,
    Pi.map_π, ← Category.assoc, Pi.map_π, Category.assoc, scalarKernelIso_hom_ι]

/-- Every forward coordinate retains the same original projection and both
actual kernel inclusions. -/
@[reassoc]
theorem nsmulKernelProductFunctorIso_hom_π_ι (i : I) :
    (nsmulKernelProductFunctorIso n L A).hom ≫
        Pi.π (fun i => (L i).obj (kernel (n • 𝟙 (A i)))) i ≫
          (L i).map (kernel.ι (n • 𝟙 (A i))) =
      kernel.ι (n • 𝟙 (∏ᶜ fun i => (L i).obj (A i))) ≫
        Pi.π (fun i => (L i).obj (A i)) i := by
  apply (cancel_epi (nsmulKernelProductFunctorIso n L A).inv).mp
  simpa only [Iso.inv_hom_id_assoc] using
    (nsmulKernelProductFunctorIso_inv_ι_π n L A i).symm

private theorem scalarKernelProductMapIso_inv_ι_π [HasProductsOfShape I C] (i : I) :
    (nsmulKernelProductIso n (fun i => (L i).obj (A i)) ≪≫
        Pi.mapIso (fun i => (nsmulKernelIso (L i) (A i) n).symm)).inv ≫
          kernel.ι (n • 𝟙 (∏ᶜ fun i => (L i).obj (A i))) ≫
            Pi.π (fun i => (L i).obj (A i)) i =
      Pi.π (fun i => (L i).obj (kernel (n • 𝟙 (A i)))) i ≫
        (L i).map (kernel.ι (n • 𝟙 (A i))) := by
  simp only [Iso.trans_inv, Category.assoc]
  change (Pi.mapIso (fun i => (nsmulKernelIso (L i) (A i) n).symm)).inv ≫
      nsmulKernelProductBackward n (fun i => (L i).obj (A i)) ≫
        kernel.ι (n • 𝟙 (∏ᶜ fun i => (L i).obj (A i))) ≫
          Pi.π (fun i => (L i).obj (A i)) i = _
  rw [nsmulKernelProductBackward_inclusion_assoc, nsmulKernelProductInclusion,
    Pi.map_π, ← Category.assoc, Pi.mapIso_inv_π, Category.assoc, Iso.symm_inv,
    scalarKernelIso_hom_ι]

/-- The original-index construction equals the literal comparison obtained by
transporting the whole kernel and both actual products through an index
equivalence. The all-products assumption on the reindexed type is only used
to name the original `Pi.mapIso` expression. -/
theorem nsmulKernelProductFunctorIso_eq_reindex {J : Type w'}
    [HasProductsOfShape J C] (E : J ≃ I)
    [hProdE : HasKernel (n • 𝟙 (∏ᶜ fun j => (L (E j)).obj (A (E j))))] :
    let eP : (∏ᶜ fun j => (L (E j)).obj (A (E j))) ≅
        ∏ᶜ fun i => (L i).obj (A i) :=
      Pi.reindex E (fun i => (L i).obj (A i))
    let eAnn : kernel (n • 𝟙 (∏ᶜ fun j => (L (E j)).obj (A (E j)))) ≅
        kernel (n • 𝟙 (∏ᶜ fun i => (L i).obj (A i))) :=
      kernel.mapIso
        (n • 𝟙 (∏ᶜ fun j => (L (E j)).obj (A (E j))))
        (n • 𝟙 (∏ᶜ fun i => (L i).obj (A i))) eP eP (by
          simp only [nsmul_comp, Category.id_comp, comp_nsmul, Category.comp_id])
    nsmulKernelProductFunctorIso n L A =
      eAnn.symm ≪≫
        (nsmulKernelProductIso n (fun j => (L (E j)).obj (A (E j))) ≪≫
          Pi.mapIso (fun j => (nsmulKernelIso (L (E j)) (A (E j)) n).symm)) ≪≫
        Pi.reindex E (fun i => (L i).obj (kernel (n • 𝟙 (A i)))) := by
  let G : I → C := fun i => (L i).obj (A i)
  let K : I → C := fun i => (L i).obj (kernel (n • 𝟙 (A i)))
  have (i : I) : HasKernel (n • 𝟙 (G i)) :=
    inferInstanceAs (HasKernel (n • 𝟙 ((L i).obj (A i))))
  have (j : J) : HasKernel (n • 𝟙 ((G ∘ E) j)) :=
    inferInstanceAs (HasKernel (n • 𝟙 ((L (E j)).obj (A (E j)))))
  have : HasProduct G := inferInstanceAs (HasProduct (fun i => (L i).obj (A i)))
  have : HasProduct (nsmulKernelProductFamily n G) :=
    inferInstanceAs (HasProduct (nsmulKernelProductFamily n (fun i => (L i).obj (A i))))
  have : HasProduct K :=
    inferInstanceAs (HasProduct (fun i => (L i).obj (kernel (n • 𝟙 (A i)))))
  have : HasKernel (n • 𝟙 (∏ᶜ G)) :=
    inferInstanceAs (HasKernel (n • 𝟙 (∏ᶜ fun i => (L i).obj (A i))))
  have : HasKernel (n • 𝟙 (∏ᶜ (G ∘ E))) := hProdE
  let eP : (∏ᶜ (G ∘ E)) ≅ ∏ᶜ G := Pi.reindex E G
  let eAnn : kernel (n • 𝟙 (∏ᶜ (G ∘ E))) ≅ kernel (n • 𝟙 (∏ᶜ G)) :=
    kernel.mapIso (n • 𝟙 (∏ᶜ (G ∘ E))) (n • 𝟙 (∏ᶜ G)) eP eP (by
      simp only [nsmul_comp, Category.id_comp, comp_nsmul, Category.comp_id])
  let eFin : kernel (n • 𝟙 (∏ᶜ (G ∘ E))) ≅ ∏ᶜ (K ∘ E) :=
    nsmulKernelProductIso n (G ∘ E) ≪≫
      Pi.mapIso (f := nsmulKernelProductFamily n (G ∘ E)) (g := K ∘ E)
        (fun j => (nsmulKernelIso (L (E j)) (A (E j)) n).symm)
  let eK : (∏ᶜ (K ∘ E)) ≅ ∏ᶜ K := Pi.reindex E K
  change nsmulKernelProductFunctorIso n L A = eAnn.symm ≪≫ eFin ≪≫ eK
  apply Iso.ext_inv
  apply (cancel_mono (kernel.ι (n • 𝟙 (∏ᶜ G)))).mp
  apply Pi.hom_ext
  intro i
  obtain ⟨j, rfl⟩ := E.surjective i
  have hAnn : eAnn.hom ≫ kernel.ι (n • 𝟙 (∏ᶜ G)) =
      kernel.ι (n • 𝟙 (∏ᶜ (G ∘ E))) ≫ eP.hom :=
    kernel.lift_ι _ _ _
  have hFin : eFin.inv ≫ kernel.ι (n • 𝟙 (∏ᶜ (G ∘ E))) ≫ Pi.π (G ∘ E) j =
      Pi.π (K ∘ E) j ≫ (L (E j)).map (kernel.ι (n • 𝟙 (A (E j)))) :=
    scalarKernelProductMapIso_inv_ι_π n (fun j => L (E j)) (fun j => A (E j)) j
  simp only [Category.assoc]
  rw [nsmulKernelProductFunctorIso_inv_ι_π]
  symm
  calc
    (eAnn.symm ≪≫ eFin ≪≫ eK).inv ≫ kernel.ι (n • 𝟙 (∏ᶜ G)) ≫ Pi.π G (E j) =
        eK.inv ≫ eFin.inv ≫ (eAnn.hom ≫ kernel.ι (n • 𝟙 (∏ᶜ G))) ≫
          Pi.π G (E j) := by
      simp only [Iso.trans_inv, Iso.symm_inv, Category.assoc]
    _ = eK.inv ≫ eFin.inv ≫
        (kernel.ι (n • 𝟙 (∏ᶜ (G ∘ E))) ≫ eP.hom) ≫ Pi.π G (E j) :=
      congrArg (fun a => eK.inv ≫ eFin.inv ≫ a ≫ Pi.π G (E j)) hAnn
    _ = eK.inv ≫
        (eFin.inv ≫ kernel.ι (n • 𝟙 (∏ᶜ (G ∘ E))) ≫ Pi.π (G ∘ E) j) := by
      simp only [Category.assoc, eP, Pi.reindex_hom_π]
    _ = eK.inv ≫ (Pi.π (K ∘ E) j ≫
        (L (E j)).map (kernel.ι (n • 𝟙 (A (E j))))) :=
      congrArg (fun a => eK.inv ≫ a) hFin
    _ = Pi.π K (E j) ≫ (L (E j)).map (kernel.ι (n • 𝟙 (A (E j)))) := by
      simp only [eK, Pi.reindex_inv_π_assoc]

end Products

end CategoryTheory.Preadditive
