/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.Cech.Exactness
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequence
/-!
# Differentials and short exact sequences for generic Cech complexes

The component formula `cech_d_comp_π` retains the differential of Mathlib's
original `cechComplexFunctor` on an arbitrary category with finite products.

`cech_shortExact_of_sections` proves short exactness of the original module-valued
Cech complexes from the supplied short exactness on all finite products of the
selected objects. Products of module short exact sequences are handled
explicitly. No topological-space or sheaf condition is imposed.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe w v v' v'' u u' u''
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
namespace CategoryTheory.Cech

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]
  {A : Type u'} [Category.{v'} A] [Preadditive A] [HasProducts.{w} A]
  {ι : Type w} (U : ι → C) (P : Cᵒᵖ ⥤ A)

lemma cech_d_comp_π (n : ℕ) (a : Fin (n + 2) → ι) :
    ((cechComplexFunctor U).obj P).d n (n + 1) ≫
      Pi.π (fun b : Fin (n + 2) → ι => P.obj (op (∏ᶜ fun i => U (b i)))) a =
    ∑ j : Fin (n + 2), (-1 : ℤ) ^ (j : ℕ) •
      (Pi.π (fun b : Fin (n + 1) → ι => P.obj (op (∏ᶜ fun i => U (b i))))
          (fun k => a (j.succAbove k)) ≫
        P.map (Pi.lift (fun k => Pi.π (fun i => U (a i)) (j.succAbove k))).op) := by
  simp [cechComplexFunctor, FormalCoproduct.cochainComplexFunctor,
    AlgebraicTopology.AlternatingCofaceMapComplex.obj,
    AlgebraicTopology.AlternatingCofaceMapComplex.objD,
    FormalCoproduct.cosimplicialObjectFunctor, CosimplicialObject.δ,
    FormalCoproduct.evalOp, FormalCoproduct.cech, FormalCoproduct.mapPower,
    Preadditive.sum_comp, Function.comp_def, SimplexCategory.δ]

end CategoryTheory.Cech


namespace CategoryTheory.Cech

variable {R : Type u} [Ring R] {ι : Type u}

lemma module_pi_map_hom_apply {M N : ι → ModuleCat.{u} R} (f : ∀ i, M i ⟶ N i)
    (z : ↑(∏ᶜ M)) (i : ι) :
    ((ModuleCat.piIsoPi N).hom (Limits.Pi.map f z)) i = f i (((ModuleCat.piIsoPi M).hom z) i) := by
  have H : Limits.Pi.map f ≫ (ModuleCat.piIsoPi N).hom ≫
      ModuleCat.ofHom (LinearMap.proj i) =
      (ModuleCat.piIsoPi M).hom ≫ ModuleCat.ofHom (LinearMap.proj i) ≫ f i := by
    simp only [ModuleCat.piIsoPi_hom_ker_subtype, ← Category.assoc, Limits.Pi.map_π]
  exact ConcreteCategory.congr_hom H z

lemma module_pi_map_surjective {M N : ι → ModuleCat.{u} R} (f : ∀ i, M i ⟶ N i)
    (hf : ∀ i, Function.Surjective (f i)) : Function.Surjective (Limits.Pi.map f) := by
  intro z
  choose y hy using fun i => hf i (((ModuleCat.piIsoPi N).hom z) i)
  refine ⟨(ModuleCat.piIsoPi M).inv y, ?_⟩
  apply (ModuleCat.piIsoPi N).toLinearEquiv.injective
  funext i
  change ((ModuleCat.piIsoPi N).hom (Limits.Pi.map f ((ModuleCat.piIsoPi M).inv y))) i = _
  rw [module_pi_map_hom_apply, Iso.inv_hom_id_apply]
  exact hy i

/-- The short complex of products of the module short complexes `S`, with both arrows induced
componentwise. -/
def moduleProductShortComplex (S : ι → ShortComplex (ModuleCat.{u} R)) :
    ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk (Limits.Pi.map fun i => (S i).f) (Limits.Pi.map fun i => (S i).g) (by
    apply Pi.hom_ext
    intro i
    simp only [Category.assoc, Limits.Pi.map_π, Limits.Pi.map_π_assoc, (S i).zero, comp_zero,
      zero_comp])

lemma moduleProductShortComplex_shortExact (S : ι → ShortComplex (ModuleCat.{u} R))
    (hS : ∀ i, (S i).ShortExact) : (moduleProductShortComplex S).ShortExact := by
  let (i : ι) : Mono (S i).f := (hS i).mono_f
  refine { mono_f := by change Mono (Limits.Pi.map (fun i => (S i).f)); infer_instance
           epi_g := (ModuleCat.epi_iff_surjective _).mpr
             (module_pi_map_surjective _ (fun i => (hS i).moduleCat_surjective_g))
           exact := ?_ }
  · rw [ShortComplex.moduleCat_exact_iff]
    intro z hz
    change ↑(∏ᶜ fun i => (S i).X₂) at z
    have hz' (i : ι) : (S i).g (((ModuleCat.piIsoPi (fun i => (S i).X₂)).hom z) i) = 0 := by
      have h := congrArg (fun t => ((ModuleCat.piIsoPi (fun i => (S i).X₃)).hom t) i) hz
      change ((ModuleCat.piIsoPi (fun i => (S i).X₃)).hom (Limits.Pi.map (fun i => (S i).g) z)) i =
        _ at h
      erw [module_pi_map_hom_apply] at h
      simp only [map_zero] at h
      change _ = 0 at h
      exact h
    choose y hy using fun i => (ShortComplex.moduleCat_exact_iff _).mp (hS i).exact _ (hz' i)
    refine ⟨(ModuleCat.piIsoPi (fun i => (S i).X₁)).inv y, ?_⟩
    apply (ModuleCat.piIsoPi (fun i => (S i).X₂)).toLinearEquiv.injective
    funext i
    change ((ModuleCat.piIsoPi (fun i => (S i).X₂)).hom (Limits.Pi.map (fun i => (S i).f) _)) i = _
    rw [module_pi_map_hom_apply, Iso.inv_hom_id_apply]
    exact hy i

section CechFunctor
variable {C : Type v} [Category.{w} C] [HasFiniteProducts C]
  (U : ι → C)

instance cechComplexFunctor_additive : (cechComplexFunctor (A := ModuleCat.{u} R) U).Additive where
  map_add := by
    intro P Q f g
    ext n : 1
    apply Pi.hom_ext
    intro a
    simp [cechComplexFunctor, FormalCoproduct.cochainComplexFunctor,
      FormalCoproduct.cosimplicialObjectFunctor, FormalCoproduct.evalOp,
      AlgebraicTopology.AlternatingCofaceMapComplex.map, Preadditive.add_comp]

lemma cech_shortExact_of_sections (S : ShortComplex (Cᵒᵖ ⥤ ModuleCat.{u} R))
    (hS : ∀ (n : ℕ) (a : Fin (n + 1) → ι),
      (S.map ((evaluation Cᵒᵖ (ModuleCat.{u} R)).obj (op (∏ᶜ fun i => U (a i))))).ShortExact) :
    (S.map (cechComplexFunctor U)).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  exact moduleProductShortComplex_shortExact
    (fun a : Fin (n + 1) → ι => S.map
      ((evaluation Cᵒᵖ (ModuleCat.{u} R)).obj (op (∏ᶜ fun i => U (a i))))) (hS n)

end CechFunctor
end CategoryTheory.Cech
