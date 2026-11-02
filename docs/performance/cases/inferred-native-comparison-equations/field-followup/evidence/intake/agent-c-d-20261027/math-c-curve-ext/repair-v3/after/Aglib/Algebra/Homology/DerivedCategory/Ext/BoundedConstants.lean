/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Ext.ShortExactComparison
public import Aglib.Algebra.Category.Grp.FinitelyGeneratedColimit
public import Mathlib.GroupTheory.FiniteAbelian.Basic

/-! # Finite split and bounded coefficient passage for the original Ext map

All comparisons are the existing exact-functor/source-precomposition map.
Finite coefficients retain their original carrier. Their actual cyclic split
maps, and the literal finite-subgroup inclusion cocone, supply the reductions.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits CategoryTheory.Abelian
open scoped BigOperators DirectSum

namespace CategoryTheory

universe u v u' v' w e e' z

private theorem split_family_apply
    {C : Type u} [Category.{v} C] [Preadditive C]
    (P : C ⥤ AddCommGrpCat.{e}) [P.Additive]
    {Y : C} {ι : Type z} [Fintype ι] (B : ι → C)
    (s : ∀ i, B i ⟶ Y) (r : ∀ i, Y ⟶ B i)
    (hs : ∑ i, r i ≫ s i = 𝟙 Y) (x : P.obj Y) :
    (∑ i, P.map (s i) (P.map (r i) x)) = x := by
  classical
  have hadd (f g : Y ⟶ Y) : P.map (f + g) x = P.map f x + P.map g x :=
    congrArg (fun t : P.obj Y ⟶ P.obj Y => t x) (P.map_add (f := f) (g := g))
  have hzero : P.map (0 : Y ⟶ Y) x = 0 :=
    congrArg (fun t : P.obj Y ⟶ P.obj Y => t x) (P.map_zero Y Y)
  have heval (t : Finset ι) :
      P.map (∑ i ∈ t, r i ≫ s i) x = ∑ i ∈ t, P.map (r i ≫ s i) x := by
    induction t using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using hzero
    | @insert i t hi ih =>
        rw [Finset.sum_insert hi, Finset.sum_insert hi, hadd, ih]
  have hsum : (∑ i, P.map (r i ≫ s i) x) = x := by
    rw [← heval Finset.univ, hs, P.map_id]
    rfl
  refine (Finset.sum_congr rfl (fun i _ => ?_)).trans hsum
  exact (congrArg (fun t : P.obj Y ⟶ P.obj Y => t x) (P.map_comp (r i) (s i))).symm

private theorem exists_bounded_cyclic_split
    (V : AddCommGrpCat.{w}) [Finite V] (N : ℕ) (hV : ∀ x : V, N • x = 0)
    (B : ℕ → AddCommGrpCat.{w}) (eB : ∀ m, B m ≃+ ZMod m) :
    ∃ (ι : Type) (hι : Fintype ι),
      letI := hι
      ∃ (m : ι → ℕ) (s : ∀ i, B (m i) ⟶ V) (r : ∀ i, V ⟶ B (m i)),
        (∀ i, 0 < m i ∧ m i ∣ N) ∧ (∑ i, r i ≫ s i) = 𝟙 V := by
  classical
  obtain ⟨ι, hι, m, hm, ⟨e⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite' V
  let := hι
  have hdvd (i : ι) : m i ∣ N := by
    have he : N • (DirectSum.of (fun j => ZMod (m j)) i (1 : ZMod (m i))) = 0 := by
      have he := congrArg e (hV (e.symm (DirectSum.of (fun j => ZMod (m j)) i 1)))
      simpa only [map_nsmul, e.apply_symm_apply, map_zero] using he
    have hi := congrArg (DFinsupp.evalAddMonoidHom i) he
    rw [map_nsmul, map_zero] at hi
    change N • (DirectSum.of (fun j => ZMod (m j)) i (1 : ZMod (m i))) i = 0 at hi
    have hz : (N : ZMod (m i)) = 0 := by
      simpa only [DirectSum.of_eq_same, nsmul_eq_mul, mul_one] using hi
    exact (ZMod.natCast_eq_zero_iff N (m i)).mp hz
  let s : ∀ i, B (m i) ⟶ V := fun i => AddCommGrpCat.ofHom
    (e.symm.toAddMonoidHom.comp
      ((DirectSum.of (fun j => ZMod (m j)) i).comp (eB (m i)).toAddMonoidHom))
  let r : ∀ i, V ⟶ B (m i) := fun i => AddCommGrpCat.ofHom
    ((eB (m i)).symm.toAddMonoidHom.comp
      ((DFinsupp.evalAddMonoidHom i).comp e.toAddMonoidHom))
  have hs : (∑ i, r i ≫ s i) = 𝟙 V := by
    apply AddCommGrpCat.homAddEquiv.injective
    apply AddMonoidHom.ext
    intro x
    change (AddCommGrpCat.homAddEquiv (∑ i, r i ≫ s i)) x = x
    rw [map_sum, AddMonoidHom.finsetSum_apply]
    apply e.injective
    rw [map_sum]
    change (∑ i, e (e.symm (DirectSum.of (fun j => ZMod (m j)) i
      ((eB (m i)) ((eB (m i)).symm ((e x) i)))))) = e x
    simp only [AddEquiv.apply_symm_apply, DirectSum.sum_univ_of]
  exact ⟨ι, hι, m, s, r, fun i => ⟨lt_trans Nat.zero_lt_one (hm i), hdvd i⟩, hs⟩

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{e} C]
    {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{e'} D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {X : C} {A : D} (a : A ⟶ F.obj X)

/-- The original map is surjective on any actual finite split coefficient family. -/
theorem Functor.extPrecompMap_surjective_of_split_family
    {Y : C} {ι : Type z} [Fintype ι] (B : ι → C)
    (s : ∀ i, B i ⟶ Y) (r : ∀ i, Y ⟶ B i)
    (hs : ∑ i, r i ≫ s i = 𝟙 Y) (q : ℕ)
    (hB : ∀ i, Function.Surjective (F.extPrecompMap a (B i) q)) :
    Function.Surjective (F.extPrecompMap a Y q) := by
  classical
  let S : C ⥤ AddCommGrpCat.{e} := extFunctorObj X q
  let T : C ⥤ AddCommGrpCat.{e'} := F ⋙ extFunctorObj A q
  let t (Z : C) : S.obj Z →+ T.obj Z := F.extPrecompMap a Z q
  have hn {Y Z : C} (f : Y ⟶ Z) (x : S.obj Y) :
      t Z (S.map f x) = T.map f (t Y x) := by
    exact (congrArg
      (fun m : Ext.{e} X Y q →+ Ext.{e'} A (F.obj Z) q => m x)
      (F.extPrecompMap_postcomp a f q)).symm
  change Function.Surjective (t Y)
  have hB' (i : ι) : Function.Surjective (t (B i)) := hB i
  intro x
  choose y hy using fun i => hB' i (T.map (r i) x)
  refine ⟨∑ i, S.map (s i) (y i), ?_⟩
  calc
    t Y (∑ i, S.map (s i) (y i)) = ∑ i, T.map (s i) (t (B i) (y i)) := by
      exact (_root_.map_sum (t Y) (fun i => S.map (s i) (y i)) Finset.univ).trans
        (Finset.sum_congr rfl (fun i _ => hn (s i) (y i)))
    _ = ∑ i, T.map (s i) (T.map (r i) x) := by
      exact Finset.sum_congr rfl (fun i _ => congrArg (T.map (s i)) (hy i))
    _ = x := split_family_apply T B s r hs x

/-- The same actual split family also detects injectivity of the original map. -/
theorem Functor.extPrecompMap_bijective_of_split_family
    {Y : C} {ι : Type z} [Fintype ι] (B : ι → C)
    (s : ∀ i, B i ⟶ Y) (r : ∀ i, Y ⟶ B i)
    (hs : ∑ i, r i ≫ s i = 𝟙 Y) (q : ℕ)
    (hB : ∀ i, Function.Bijective (F.extPrecompMap a (B i) q)) :
    Function.Bijective (F.extPrecompMap a Y q) := by
  classical
  let S : C ⥤ AddCommGrpCat.{e} := extFunctorObj X q
  let T : C ⥤ AddCommGrpCat.{e'} := F ⋙ extFunctorObj A q
  refine ⟨?_, F.extPrecompMap_surjective_of_split_family a B s r hs q
    (fun i => (hB i).surjective)⟩
  intro x y hxy
  have hr (i : ι) : S.map (r i) x = S.map (r i) y := by
    apply (hB i).injective
    have hnat (z : Ext.{e} X Y q) :
        F.extPrecompMap a (B i) q (S.map (r i) z) =
          T.map (r i) (F.extPrecompMap a Y q z) :=
      (congrArg (fun m : Ext.{e} X Y q →+ Ext.{e'} A (F.obj (B i)) q => m z)
        (F.extPrecompMap_postcomp a (r i) q)).symm
    exact (hnat x).trans ((congrArg (T.map (r i)) hxy).trans (hnat y).symm)
  exact (split_family_apply S B s r hs x).symm.trans
    ((Finset.sum_congr rfl (fun i _ => congrArg (S.map (s i)) (hr i))).trans
      (split_family_apply S B s r hs y))

/-- Finite cyclic reduction keeps the original coefficient V, including its value universe. -/
theorem Functor.extPrecompMap_surjective_of_finite_cyclic
    (K : AddCommGrpCat.{w} ⥤ C) [K.Additive]
    (B : ℕ → AddCommGrpCat.{w}) (eB : ∀ m, B m ≃+ ZMod m)
    (V : AddCommGrpCat.{w}) [Finite V] (q N : ℕ) (hV : ∀ x : V, N • x = 0)
    (hcyclic : ∀ m, 0 < m → m ∣ N →
      Function.Surjective (F.extPrecompMap a (K.obj (B m)) q)) :
    Function.Surjective (F.extPrecompMap a (K.obj V) q) := by
  classical
  obtain ⟨ι, hι, h⟩ := exists_bounded_cyclic_split V N hV B eB
  let := hι
  obtain ⟨m, s, r, hm, hs⟩ := h
  have hK : (∑ i, K.map (r i) ≫ K.map (s i)) = 𝟙 (K.obj V) := by
    simpa only [Functor.map_sum, Functor.map_comp, Functor.map_id] using congrArg K.map hs
  exact F.extPrecompMap_surjective_of_split_family a (fun i => K.obj (B (m i)))
    (fun i => K.map (s i)) (fun i => K.map (r i)) hK q
    (fun i => hcyclic (m i) (hm i).1 (hm i).2)

/-- The original finite coefficient has bijective comparison when its actual cyclic factors do. -/
theorem Functor.extPrecompMap_bijective_of_finite_cyclic
    (K : AddCommGrpCat.{w} ⥤ C) [K.Additive]
    (B : ℕ → AddCommGrpCat.{w}) (eB : ∀ m, B m ≃+ ZMod m)
    (V : AddCommGrpCat.{w}) [Finite V] (q N : ℕ) (hV : ∀ x : V, N • x = 0)
    (hcyclic : ∀ m, 0 < m → m ∣ N →
      Function.Bijective (F.extPrecompMap a (K.obj (B m)) q)) :
    Function.Bijective (F.extPrecompMap a (K.obj V) q) := by
  classical
  obtain ⟨ι, hι, h⟩ := exists_bounded_cyclic_split V N hV B eB
  let := hι
  obtain ⟨m, s, r, hm, hs⟩ := h
  have hK : (∑ i, K.map (r i) ≫ K.map (s i)) = 𝟙 (K.obj V) := by
    simpa only [Functor.map_sum, Functor.map_comp, Functor.map_id] using congrArg K.map hs
  exact F.extPrecompMap_bijective_of_split_family a (fun i => K.obj (B (m i)))
    (fun i => K.map (s i)) (fun i => K.map (r i)) hK q
    (fun i => hcyclic (m i) (hm i).1 (hm i).2)

/-- The original finite-subgroup cocone passes bounded finite-stage bijectivity
without replacing its coefficient or assuming the desired colimit conclusion. -/
theorem Functor.extPrecompMap_bijective_of_finite_bounded
    (K : AddCommGrpCat.{w} ⥤ C) (V : AddCommGrpCat.{w}) (q n : ℕ)
    (hn : 0 < n) (hV : ∀ x : V, n • x = 0)
    [PreservesColimit (AddCommGrpCat.finiteSubsetDiagram V) K]
    [PreservesColimit (AddCommGrpCat.finiteSubsetDiagram V ⋙ K) (extFunctorObj X q)]
    [PreservesColimit (AddCommGrpCat.finiteSubsetDiagram V ⋙ K) (F ⋙ extFunctorObj A q)]
    (hfinite : ∀ W : AddCommGrpCat.{w}, Finite W → (∀ x : W, n • x = 0) →
      Function.Bijective (F.extPrecompMap a (K.obj W) q)) :
    Function.Bijective (F.extPrecompMap a (K.obj V) q) := by
  let D := AddCommGrpCat.finiteSubsetDiagram V
  let c := AddCommGrpCat.finiteSubsetCocone V
  have ht : IsAddTorsion V := fun x =>
    isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨n, hn, hV x⟩
  apply F.extPrecompMap_bijective_of_isColimit a (D ⋙ K) (K.mapCocone c)
    (isColimitOfPreserves K (AddCommGrpCat.finiteSubsetCoconeIsColimit V)) q
  intro s
  apply hfinite (D.obj s) (AddCommGrpCat.finite_finiteSubsetDiagram_of_isAddTorsion V ht s)
  intro x
  exact Subtype.ext (hV x.val)

end CategoryTheory
