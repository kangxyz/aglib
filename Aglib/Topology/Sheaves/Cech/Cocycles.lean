/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.Cech.ExactSequences
public import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.Tactic.FinCases

/-!
# Cocycles and coboundaries on actual topological opens

For a module-valued presheaf on the opens of a topological space, the original
Cech differential has its literal restriction formula. Degree-one exactness
turns the pairwise/triple-intersection cocycle equation into an actual
coboundary. The ring, space and index universes retain their original context;
no sheaf condition, covering hypothesis or exactness supplier is added.

Existing implementation split from
`Aglib.CategoryTheory.Sites.SheafCohomology.Cech.ExactSequences`
at source revision `451aeda6b8bb5b44402b574dd6cf60f912360f8c`.
The original declaration contexts, maps and proof bodies are retained.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe w v v' v'' u u' u''
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped Simplicial

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
