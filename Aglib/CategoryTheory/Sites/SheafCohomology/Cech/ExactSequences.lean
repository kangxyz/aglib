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
public import Mathlib.Tactic.FinCases
/-!
# Original Cech differentials, cocycles, and exact sequences

The component formula `cech_d_comp_π` retains the differential of mathlib's
original `cechComplexFunctor`. `exists_cechOne_coboundary_of_exact` turns
exactness in degree one into the literal section equation on pairwise
intersections, starting with the ordinary cocycle equation on triple
intersections. It does not assume the presheaf is a sheaf.

`cech_shortExact_of_sections` proves short exactness of the original Cech
complexes from short exactness of sections over their finite intersections.
Arbitrary products of module short exact sequences are handled explicitly.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe w v v' v'' u u' u''
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
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
variable {X : TopCat.{u}} {R : Type u} [Ring R] {ι : Type u}
  (U : ι → Opens X) (P : (Opens X)ᵒᵖ ⥤ ModuleCat.{u} R)

/-- The finite intersection of the `n + 1` opens selected by the tuple `a`. -/
abbrev tupleOpen (n : ℕ) (a : Fin (n + 1) → ι) : Opens X := ∏ᶜ fun i => U (a i)

lemma tupleOpen_le (n : ℕ) (a : Fin (n + 1) → ι) (i : Fin (n + 1)) :
    tupleOpen U n a ≤ U (a i) := leOfHom (Pi.π _ i)

lemma pair_le_tupleOpen (i j : ι) :
    U i ⊓ U j ≤ tupleOpen U 1 ![i, j] := by
  apply leOfHom (Pi.lift fun k => homOfLE ?_)
  fin_cases k
  · exact inf_le_left
  · exact inf_le_right

/-- The `R`-linear restriction of presheaf sections from `W` to `V` along the inclusion `h : V ≤
W`. -/
abbrev sectionRes {V W : Opens X} (h : V ≤ W) : P.obj (op W) →ₗ[R] P.obj (op V) :=
  (P.map (homOfLE h).op).hom

@[simp]
lemma sectionRes_comp {V W T : Opens X} (h : V ≤ W) (k : W ≤ T) (s : P.obj (op T)) :
    sectionRes P h (sectionRes P k s) = sectionRes P (h.trans k) s := by
  change (P.map (homOfLE k).op ≫ P.map (homOfLE h).op) s = _
  rw [← P.map_comp]
  rfl

/-- The degree-`n` Cech cochain associated to the family of sections `s` over all `(n + 1)`-fold
intersections. -/
abbrev cochainVector (n : ℕ) (s : ∀ a : Fin (n + 1) → ι, P.obj (op (tupleOpen U n a))) :
    ((cechComplexFunctor U).obj P).X n :=
  (ModuleCat.piIsoPi _).inv s

lemma cochainVector_component (n : ℕ)
    (s : ∀ a : Fin (n + 1) → ι, P.obj (op (tupleOpen U n a))) (a : Fin (n + 1) → ι) :
    Pi.π (fun b => P.obj (op (tupleOpen U n b))) a (cochainVector U P n s) = s a := by
  exact ConcreteCategory.congr_hom (ModuleCat.piIsoPi_inv_kernel_ι (fun b : Fin (n + 1) → ι => P.obj
    (op (tupleOpen U n b))) a) s

lemma cech_d_apply_component (n : ℕ)
    (s : ((cechComplexFunctor U).obj P).X n) (a : Fin (n + 2) → ι) :
    Pi.π (fun b => P.obj (op (tupleOpen U (n + 1) b))) a
        (((cechComplexFunctor U).obj P).d n (n + 1) s) =
      ∑ j : Fin (n + 2), (-1 : ℤ) ^ (j : ℕ) •
        sectionRes P (leOfHom (Pi.lift (fun k => Pi.π (fun i => U (a i)) (j.succAbove k))))
          (Pi.π (fun b => P.obj (op (tupleOpen U n b))) (fun k => a (j.succAbove k)) s) := by
  have h := congrArg (fun f : ((cechComplexFunctor U).obj P).X n ⟶
      P.obj (op (tupleOpen U (n + 1) a)) => f.hom s) (cech_d_comp_π U P n a)
  simp only [ModuleCat.hom_sum, ModuleCat.hom_zsmul, LinearMap.sum_apply,
    LinearMap.smul_apply, ModuleCat.hom_comp, LinearMap.comp_apply] at h
  erw [h]
  apply Finset.sum_congr rfl
  intro j hj
  congr 1

lemma cechOne_vector_closed
    (c : ∀ i j, P.obj (op (U i ⊓ U j)))
    (hc : ∀ a : Fin 3 → ι,
      sectionRes P (le_inf (tupleOpen_le U 2 a 0) (tupleOpen_le U 2 a 1)) (c (a 0) (a 1)) +
      sectionRes P (le_inf (tupleOpen_le U 2 a 1) (tupleOpen_le U 2 a 2)) (c (a 1) (a 2)) =
      sectionRes P (le_inf (tupleOpen_le U 2 a 0) (tupleOpen_le U 2 a 2)) (c (a 0) (a 2))) :
    ((cechComplexFunctor U).obj P).d 1 2
      (cochainVector U P 1 (fun a => sectionRes P
        (le_inf (tupleOpen_le U 1 a 0) (tupleOpen_le U 1 a 1)) (c (a 0) (a 1)))) = 0 := by
  apply (ModuleCat.piIsoPi (fun b : Fin 3 → ι => P.obj (op (tupleOpen U 2
    b)))).toLinearEquiv.injective
  ext a
  have he (z) : ((ModuleCat.piIsoPi
      (fun b => P.obj (op (tupleOpen U 2 b)))).hom z) a =
      Pi.π (fun b => P.obj (op (tupleOpen U 2 b))) a z :=
    ConcreteCategory.congr_hom (ModuleCat.piIsoPi_hom_ker_subtype _ a) z
  change ((ModuleCat.piIsoPi
      (fun b => P.obj (op (tupleOpen U 2 b)))).hom _) a =
      ((ModuleCat.piIsoPi (fun b => P.obj (op (tupleOpen U 2 b)))).hom 0) a
  rw [he]
  simp only [map_zero]
  change _ = 0
  rw [cech_d_apply_component]
  simp only [cochainVector_component, sectionRes_comp, Fin.sum_univ_succ]
  norm_num [Fin.succAbove]
  change sectionRes P (le_inf (tupleOpen_le U 2 a 1) (tupleOpen_le U 2 a 2)) (c (a 1) (a 2)) +
    (-sectionRes P (le_inf (tupleOpen_le U 2 a 0) (tupleOpen_le U 2 a 2)) (c (a 0) (a 2)) +
      sectionRes P (le_inf (tupleOpen_le U 2 a 0) (tupleOpen_le U 2 a 1)) (c (a 0) (a 1))) = 0
  rw [← hc a]
  abel

lemma le_tupleOpen_const (i : ι) : U i ≤ tupleOpen U 0 (fun _ => i) :=
  leOfHom (Pi.lift fun _ => 𝟙 _)

@[simp]
lemma sectionRes_refl {V : Opens X} (h : V ≤ V) (s : P.obj (op V)) :
    sectionRes P h s = s := by
  simp [sectionRes]

lemma sectionRes_component_congr (n : ℕ)
    (b : ↑(∏ᶜ fun a : Fin (n + 1) → ι => P.obj (op (tupleOpen U n a))))
    {a a' : Fin (n + 1) → ι} (e : a = a') {V : Opens X}
    (h : V ≤ tupleOpen U n a) (h' : V ≤ tupleOpen U n a') :
    sectionRes P h (Pi.π (fun a => P.obj (op (tupleOpen U n a))) a b) =
      sectionRes P h' (Pi.π (fun a => P.obj (op (tupleOpen U n a))) a' b) := by
  subst a'
  rfl

lemma cechOne_coboundary_of_exact
    (hex : ((cechComplexFunctor U).obj P).ExactAt 1)
    (c : ∀ i j, P.obj (op (U i ⊓ U j)))
    (hc : ∀ a : Fin 3 → ι,
      sectionRes P (le_inf (tupleOpen_le U 2 a 0) (tupleOpen_le U 2 a 1)) (c (a 0) (a 1)) +
      sectionRes P (le_inf (tupleOpen_le U 2 a 1) (tupleOpen_le U 2 a 2)) (c (a 1) (a 2)) =
      sectionRes P (le_inf (tupleOpen_le U 2 a 0) (tupleOpen_le U 2 a 2)) (c (a 0) (a 2))) :
    ∃ b : ∀ i, P.obj (op (U i)), ∀ i j,
      sectionRes P inf_le_right (b j) - sectionRes P inf_le_left (b i) = c i j := by
  let z := cochainVector U P 1 (fun a => sectionRes P
    (le_inf (tupleOpen_le U 1 a 0) (tupleOpen_le U 1 a 1)) (c (a 0) (a 1)))
  rw [HomologicalComplex.exactAt_iff' _ 0 1 2 (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff] at hex
  obtain ⟨b, hb⟩ := hex z (cechOne_vector_closed U P c hc)
  change ↑(∏ᶜ fun a : Fin 1 → ι => P.obj (op (tupleOpen U 0 a))) at b
  refine ⟨fun i => sectionRes P (le_tupleOpen_const U i)
    (Pi.π (fun a => P.obj (op (tupleOpen U 0 a))) (fun _ => i) b), ?_⟩
  intro i j
  have hh := congrArg (fun t => sectionRes P (pair_le_tupleOpen U i j)
    (Pi.π (fun a => P.obj (op (tupleOpen U 1 a))) ![i, j] t)) hb
  change sectionRes P (pair_le_tupleOpen U i j)
      (Pi.π (fun a => P.obj (op (tupleOpen U 1 a))) ![i, j]
        (((cechComplexFunctor U).obj P).d 0 1 b)) =
    sectionRes P (pair_le_tupleOpen U i j)
      (Pi.π (fun a => P.obj (op (tupleOpen U 1 a))) ![i, j] z) at hh
  rw [cech_d_apply_component] at hh
  dsimp [z] at hh
  erw [cochainVector_component, sectionRes_comp, sectionRes_refl] at hh
  have h₀ : (fun k : Fin 1 => (![i, j] : Fin 2 → ι) ((0 : Fin 2).succAbove k)) =
      (fun _ => j) := by funext k; fin_cases k; rfl
  have h₁ : (fun k : Fin 1 => (![i, j] : Fin 2 → ι) ((1 : Fin 2).succAbove k)) =
      (fun _ => i) := by funext k; fin_cases k; rfl
  simp only [Fin.sum_univ_two, Fin.val_zero, pow_zero, one_zsmul, Fin.val_one,
    pow_one, neg_one_zsmul] at hh
  simp only [map_add, map_neg, sectionRes_comp] at hh
  erw [sectionRes_component_congr U P 0 b h₀ _
      (inf_le_right.trans (le_tupleOpen_const U j)),
    sectionRes_component_congr U P 0 b h₁ _
      (inf_le_left.trans (le_tupleOpen_const U i))] at hh
  change _ = c i j at hh
  simpa only [sectionRes_comp, sub_eq_add_neg] using hh

theorem exists_cechOne_coboundary_of_exact
    (hex : ((cechComplexFunctor U).obj P).ExactAt 1)
    (c : ∀ i j, P.obj (op (U i ⊓ U j)))
    (hc : ∀ i j k,
      sectionRes P (inf_le_left : (U i ⊓ U j) ⊓ U k ≤ _) (c i j) +
      sectionRes P (inf_le_inf inf_le_right le_rfl) (c j k) =
      sectionRes P (inf_le_inf inf_le_left le_rfl) (c i k)) :
    ∃ b : ∀ i, P.obj (op (U i)), ∀ i j,
      sectionRes P inf_le_right (b j) - sectionRes P inf_le_left (b i) = c i j := by
  apply cechOne_coboundary_of_exact U P hex c
  intro a
  have h := congrArg (sectionRes P
    (le_inf (le_inf (tupleOpen_le U 2 a 0) (tupleOpen_le U 2 a 1)) (tupleOpen_le U 2 a 2)))
      (hc (a 0) (a 1) (a 2))
  simpa only [map_add, sectionRes_comp] using h

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
