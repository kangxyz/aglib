/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.TensorFaithful
public import Aglib.AlgebraicGeometry.Modules.Invertible.Affine
public import Aglib.AlgebraicGeometry.Modules.InternalHom.HomFunctor
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.LocalSplitting
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Tensor.Exact
public import Aglib.AlgebraicGeometry.Modules.Tensor.Sections
public import Aglib.AlgebraicGeometry.Modules.Pullback.Tensor.Unit
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono

/-!
# Cross relations for a finite generating row of a line bundle

For the original row `π : O_X^ι ⟶ L`, the pair `(i,j)` gives a section
of the actual `kernel π ⊗ L`. Its composite with the original tensor
inclusion is `e_i ⊗ s_j - e_j ⊗ s_i`, where `s_i = e_i ≫ π`.
If `ι` is finite and `π` is epic, these sections generate the actual
tensor kernel. Local splitting of the original row proves generation;
no global splitting or presentation of the kernel is supplied.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.InternalHom

universe u v w

namespace AlgebraicGeometry.Scheme.Modules.Invertible

section LinearCarriers

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

private theorem linear_from_ring (f : R →ₗ[R] M) (r : R) : f r = r • f 1 := by
  simpa only [smul_eq_mul, mul_one] using f.map_smul r (1 : R)

private theorem linear_frame_generator (a : M →ₗ[R] R) (b : R →ₗ[R] M)
    (h : ∀ m, b (a m) = m) (m : M) : a m • b 1 = m :=
  (linear_from_ring b (a m)).symm.trans (h m)

private theorem linear_frame_dual (a : M →ₗ[R] R) (b : R →ₗ[R] M)
    (h : ∀ m, b (a m) = m) (t : R →ₗ[R] M) (ell : M →ₗ[R] R) :
    ell (t 1) = a (t (ell (b 1))) := by
  have ht : a (t 1) • b 1 = t 1 := linear_frame_generator a b h (t 1)
  calc
    ell (t 1) = ell (a (t 1) • b 1) := congrArg ell ht.symm
    _ = a (t 1) * ell (b 1) := ell.map_smul _ _
    _ = ell (b 1) * a (t 1) := mul_comm _ _
    _ = a (ell (b 1) • t 1) := (a.map_smul _ _).symm
    _ = a (t (ell (b 1))) := congrArg a (linear_from_ring t _).symm

end LinearCarriers

section FiniteMatrix

variable {C : Type v} [Category.{w} C] [Preadditive C]

/-- The finite Bezout calculation is made in an abstract preadditive
category, so it never unfolds the concrete restriction or sheaf objects. -/
private theorem finite_cross_epi {ι : Type u} [Fintype ι]
    {O P K A : C} (inc : ι → (O ⟶ P)) (pr : ι → (P ⟶ O))
    (hη : ∑ i, pr i ≫ inc i = 𝟙 P)
    (q : P ⟶ O) (h : O ⟶ P) (hh : h ≫ q = 𝟙 O)
    (k : K ⟶ P) [Mono k] (hk : k ≫ q = 0)
    (c : A ⟶ K) (t : ι × ι → (O ⟶ A))
    (ht : ∀ i j, t (i, j) ≫ c ≫ k =
      (inc j ≫ q) ≫ inc i - (inc i ≫ q) ≫ inc j)
    (hcomm : ∀ a b : O ⟶ O, a ≫ b = b ≫ a) : Epi c := by
  let a (i : ι) : O ⟶ O := inc i ≫ q
  let b (j : ι) : O ⟶ O := h ≫ pr j
  let z (i : ι) : K ⟶ O := k ≫ pr i
  have hbez : ∑ j, b j ≫ a j = 𝟙 O := by
    calc
      ∑ j, b j ≫ a j = h ≫ (∑ j, pr j ≫ inc j) ≫ q := by
        simp only [a, b, Preadditive.comp_sum, Preadditive.sum_comp, Category.assoc]
      _ = 𝟙 O := by rw [hη, Category.id_comp, hh]
  have hker : ∑ i, z i ≫ a i = 0 := by
    calc
      ∑ i, z i ≫ a i = k ≫ (∑ i, pr i ≫ inc i) ≫ q := by
        simp only [a, z, Preadditive.comp_sum, Preadditive.sum_comp, Category.assoc]
      _ = 0 := by rw [hη, Category.id_comp, hk]
  have hηk : ∑ i, z i ≫ inc i = k := by
    calc
      ∑ i, z i ≫ inc i = k ≫ (∑ i, pr i ≫ inc i) := by
        simp only [z, Preadditive.comp_sum, Category.assoc]
      _ = k := by rw [hη, Category.comp_id]
  let r : K ⟶ A := ∑ i, ∑ j, z i ≫ b j ≫ t (i, j)
  have hterm (i j : ι) :
      (z i ≫ b j ≫ t (i, j)) ≫ c ≫ k =
        (z i ≫ b j ≫ a j) ≫ inc i - (z i ≫ a i ≫ b j) ≫ inc j := by
    have hswap : z i ≫ b j ≫ a i ≫ inc j = z i ≫ a i ≫ b j ≫ inc j := by
      simpa only [Category.assoc] using
        congrArg (fun f : O ⟶ O => z i ≫ f ≫ inc j) (hcomm (b j) (a i))
    calc
      (z i ≫ b j ≫ t (i, j)) ≫ c ≫ k =
          z i ≫ b j ≫ (t (i, j) ≫ c ≫ k) := by simp only [Category.assoc]
      _ = (z i ≫ b j ≫ a j) ≫ inc i - (z i ≫ a i ≫ b j) ≫ inc j := by
        rw [ht]
        change z i ≫ b j ≫ (a j ≫ inc i - a i ≫ inc j) = _
        simp only [Preadditive.comp_sub, Category.assoc]
        rw [hswap]
  have hpos : ∑ i, ∑ j, (z i ≫ b j ≫ a j) ≫ inc i = k := by
    calc
      ∑ i, ∑ j, (z i ≫ b j ≫ a j) ≫ inc i =
          ∑ i, z i ≫ (∑ j, b j ≫ a j) ≫ inc i := by
        simp only [Preadditive.comp_sum, Preadditive.sum_comp, Category.assoc]
      _ = ∑ i, z i ≫ inc i := by simp only [hbez, Category.id_comp]
      _ = k := hηk
  have hneg : ∑ i, ∑ j, (z i ≫ a i ≫ b j) ≫ inc j = 0 := by
    rw [Finset.sum_comm]
    calc
      ∑ j, ∑ i, (z i ≫ a i ≫ b j) ≫ inc j =
          ∑ j, (∑ i, z i ≫ a i) ≫ b j ≫ inc j := by
        simp only [Preadditive.sum_comp, Category.assoc]
      _ = 0 := by simp only [hker, zero_comp, Finset.sum_const_zero]
  have hrcv : r ≫ c ≫ k = k := by
    calc
      r ≫ c ≫ k =
          ∑ i, ∑ j, ((z i ≫ b j ≫ a j) ≫ inc i -
            (z i ≫ a i ≫ b j) ≫ inc j) := by
        simp only [r, Preadditive.sum_comp]
        exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hterm i j))
      _ = (∑ i, ∑ j, (z i ≫ b j ≫ a j) ≫ inc i) -
          (∑ i, ∑ j, (z i ≫ a i ≫ b j) ≫ inc j) := by
        simp only [Finset.sum_sub_distrib]
      _ = k := by rw [hpos, hneg, sub_zero]
  have hrc : r ≫ c = 𝟙 K := (cancel_mono k).mp (by simpa using hrcv)
  let : Epi (r ≫ c) := by rw [hrc]; infer_instance
  exact epi_of_epi r c

/-- The canonical finite coproduct inclusions and projections sum to the
identity, independently of any concrete sheaf-category presentation. -/
private theorem finite_coproduct_eta {ι : Type u} [Fintype ι] [DecidableEq ι]
    (O : C) [HasCoproductsOfShape ι C] :
    ∑ i : ι, (Sigma.desc (fun j : ι => if j = i then 𝟙 O else 0)) ≫
        Sigma.ι (fun _ : ι => O) i = 𝟙 (∐ fun _ : ι => O) := by
  apply Sigma.hom_ext
  intro j
  simp [Preadditive.comp_sum, ← Category.assoc, ite_comp]

end FiniteMatrix

section MappedCoproduct

variable {C : Type v} [Category.{w} C]

private theorem mapped_coproduct_inclusion {ι : Type u} [HasCoproductsOfShape ι C]
    (T : C ⥤ C) (f : ι → C) [PreservesColimit (Discrete.functor f) T]
    (O : C) (e : ∀ i, O ≅ T.obj (f i)) (i : ι) :
    Sigma.ι (fun _ : ι => O) i ≫
        (Sigma.mapIso e ≪≫ (PreservesCoproduct.iso T f).symm).hom =
      (e i).hom ≫ T.map (Sigma.ι f i) := by
  change Sigma.ι (fun _ : ι => O) i ≫
    (Sigma.mapIso e).hom ≫ sigmaComparison T f = _
  rw [Sigma.ι_mapIso_hom_assoc, ι_comp_sigmaComparison]

end MappedCoproduct

section CategoryBoundaries

variable {C D : Type*} [Category* C] [Category* D]

private theorem iso_of_hom_eq {A B : C} (p : A ⟶ B) (e : A ≅ B)
    (h : p = e.hom) : IsIso p := by
  subst p
  infer_instance

private theorem map_mono_with (F : C ⥤ D) {M N : C} (f : M ⟶ N)
    [PreservesLimit (cospan f f) F] (hf : Mono f) : Mono (F.map f) := by
  let := hf
  exact preserves_mono_of_preservesLimit F f

private theorem map_epi_with (F : C ⥤ D) {M N : C} (f : M ⟶ N)
    [PreservesColimit (span f f) F] (hf : Epi f) : Epi (F.map f) := by
  let := hf
  exact preserves_epi_of_preservesColimit F f

private theorem epi_iso_comp {A B E : C} (e : A ≅ B) (f : B ⟶ E)
    (hf : Epi f) : Epi (e.hom ≫ f) := by
  let := hf
  exact epi_comp e.hom f

private theorem evaluation_unit_cancel {A O V M W : C}
    (e : A ≅ O) (u : V ≅ M) (v : W ≅ O) (a : A ⟶ V) (b : W ⟶ V)
    (s : O ⟶ M) (ha : a ≫ u.hom = e.hom ≫ s)
    (hb : b ≫ u.hom = v.hom ≫ s) : e.inv ≫ a = v.inv ≫ b := by
  apply (cancel_mono u.hom).mp
  calc
    (e.inv ≫ a) ≫ u.hom = e.inv ≫ (a ≫ u.hom) := Category.assoc _ _ _
    _ = s := by rw [ha, Iso.inv_hom_id_assoc]
    _ = v.inv ≫ (b ≫ u.hom) := by rw [hb, Iso.inv_hom_id_assoc]
    _ = (v.inv ≫ b) ≫ u.hom := (Category.assoc _ _ _).symm

private theorem coproduct_desc_map {I : Type*} [HasCoproductsOfShape I C]
    (T : C ⥤ C) {A O K : C} (r : I → (A ⟶ K))
    (e : (∐ fun _ : I => O) ≅ T.obj (∐ fun _ : I => A))
    (v : O ⟶ T.obj A)
    (he : ∀ i, Sigma.ι (fun _ : I => O) i ≫ e.hom =
      v ≫ T.map (Sigma.ι (fun _ : I => A) i)) :
    Sigma.desc (fun i => v ≫ T.map (r i)) = e.hom ≫ T.map (Sigma.desc r) := by
  apply Sigma.hom_ext
  intro i
  rw [Sigma.ι_comp_desc, ← Category.assoc, he, Category.assoc, ← T.map_comp,
    Sigma.ι_comp_desc]

variable [Preadditive C] [Preadditive D]

private def OriginalCrossEquation {A B E W : C}
    (g : A ⟶ B) (k : B ⟶ E) (u : A ⟶ W) (x y : W ⟶ E) : Prop :=
  g ≫ k = u ≫ (x - y)

private theorem cross_equation_endpoints {A B E W : C}
    (g : A ⟶ B) (k : B ⟶ E) (u : A ⟶ W) (x y : W ⟶ E)
    (lhs rhs : A ⟶ E) (hlhs : lhs = g ≫ k) (hrhs : rhs = u ≫ (x - y))
    (h : OriginalCrossEquation g k u x y) : lhs = rhs := by
  change g ≫ k = u ≫ (x - y) at h
  exact hlhs.trans (h.trans hrhs.symm)

omit [Preadditive C] in
private theorem original_eq_post {A B E N : C}
    (g : A ⟶ B) (k : B ⟶ E) (rhs : A ⟶ E) (h : g ≫ k = rhs) (a : E ⟶ N) :
    g ≫ k ≫ a = rhs ≫ a :=
  (Category.assoc g k a).symm.trans (congrArg (fun f => f ≫ a) h)

private theorem mapped_eta {I : Type*} [Fintype I] (F : C ⥤ D) [F.Additive]
    {O P : C} (i : I → (O ⟶ P)) (p : I → (P ⟶ O))
    (h : ∑ a, p a ≫ i a = 𝟙 P) :
    ∑ a, F.map (p a) ≫ F.map (i a) = 𝟙 (F.obj P) := by
  have hm : ∑ a, F.map (p a) ≫ F.map (i a) = F.map (𝟙 P) := by
    simpa only [Functor.map_sum, Functor.map_comp] using congrArg F.map h
  exact hm.trans (F.map_id P)

private theorem mapped_zero_comp (F : C ⥤ D) [F.Additive]
    {A B E : C} (f : A ⟶ B) (g : B ⟶ E) (h : f ≫ g = 0) :
    F.map f ≫ F.map g = 0 :=
  (F.map_comp f g).symm.trans ((congrArg F.map h).trans (F.map_zero _ _))

private theorem mapped_cross_formula (F : C ⥤ D) [F.Additive]
    {O P L V K A : C} (ia ib : O ⟶ P) (q : P ⟶ L)
    (da db : V ⟶ O) (r : V ⟶ K) (k : K ⟶ P) (t : V ⟶ A) (c : A ⟶ K)
    (d : F.obj V ≅ F.obj O) (e : F.obj L ≅ F.obj O)
    (ht : t ≫ c = r) (hr : r ≫ k = db ≫ ia - da ≫ ib)
    (ha : F.map da = d.hom ≫ F.map (ia ≫ q) ≫ e.hom)
    (hb : F.map db = d.hom ≫ F.map (ib ≫ q) ≫ e.hom) :
    (d.inv ≫ F.map t) ≫ F.map c ≫ F.map k =
      (F.map ib ≫ F.map q ≫ e.hom) ≫ F.map ia -
        (F.map ia ≫ F.map q ≫ e.hom) ≫ F.map ib := by
  have ha' : F.map da = d.hom ≫ F.map ia ≫ F.map q ≫ e.hom := by
    rw [ha, Functor.map_comp]
    simp only [Category.assoc]
  have hb' : F.map db = d.hom ≫ F.map ib ≫ F.map q ≫ e.hom := by
    rw [hb, Functor.map_comp]
    simp only [Category.assoc]
  have htc : F.map t ≫ F.map c = F.map r :=
    (F.map_comp t c).symm.trans (congrArg F.map ht)
  have hrk : F.map r ≫ F.map k = F.map (db ≫ ia - da ≫ ib) :=
    (F.map_comp r k).symm.trans (congrArg F.map hr)
  calc
    (d.inv ≫ F.map t) ≫ F.map c ≫ F.map k =
        d.inv ≫ F.map (db ≫ ia - da ≫ ib) := by
      rw [Category.assoc, ← Category.assoc (F.map t) (F.map c), htc, hrk]
    _ = _ := by
      rw [Functor.map_sub, Functor.map_comp, Functor.map_comp, ha', hb']
      simp only [Preadditive.comp_sub, Category.assoc, Iso.inv_hom_id_assoc]

private theorem tensor_cross_paste (T : C ⥤ C) [T.Additive]
    {V O Q P K W : C} (ev : T.obj V ≅ O) (u : W ≅ O)
    (a b : V ⟶ Q) (i j : Q ⟶ P) (r : V ⟶ K) (k : K ⟶ P)
    (hr : r ≫ k = b ≫ i - a ≫ j)
    (ca cb : O ⟶ T.obj Q) (ha : ev.inv ≫ T.map a = ca)
    (hb : ev.inv ≫ T.map b = cb) (x y : W ⟶ T.obj P)
    (hx : cb ≫ T.map i = u.inv ≫ x) (hy : ca ≫ T.map j = u.inv ≫ y)
    (g : O ⟶ T.obj K) (hg : g = ev.inv ≫ T.map r) :
    OriginalCrossEquation g (T.map k) u.inv x y := by
  change g ≫ T.map k = u.inv ≫ (x - y)
  rw [hg]
  calc
    (ev.inv ≫ T.map r) ≫ T.map k = ev.inv ≫ T.map (r ≫ k) := by
      rw [Category.assoc, ← T.map_comp]
    _ = (ev.inv ≫ T.map b) ≫ T.map i - (ev.inv ≫ T.map a) ≫ T.map j := by
      rw [hr, Functor.map_sub, Functor.map_comp, Functor.map_comp]
      simp only [Preadditive.comp_sub, Category.assoc]
    _ = u.inv ≫ x - u.inv ≫ y := by rw [ha, hb, hx, hy]
    _ = u.inv ≫ (x - y) := (Preadditive.comp_sub _ _ _).symm

end CategoryBoundaries

variable {X : Scheme.{u}} {ι : Type u}

local notation "Oₓ" => (SheafOfModules.unit X.ringCatSheaf : X.Modules)
local notation "Pₓ" => (SheafOfModules.free (R := X.ringCatSheaf) ι : X.Modules)
/-- The original free basis inclusion, with its native scheme-module type. -/
public abbrev generatingRowInclusion (X : Scheme.{u}) {ι : Type u} (i : ι) :
    (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶
      (SheafOfModules.free (R := X.ringCatSheaf) ι : X.Modules) :=
  SheafOfModules.ιFree (R := X.ringCatSheaf) i

private instance lineSectionsModule (L : LineBundle X) (U : X.Opens) :
    Module Γ(X, U) Γ(L.val, U) :=
  (L.val.val.obj (op U)).isModule

private def freeProjection [DecidableEq ι] (i : ι) :
    Pₓ ⟶ Oₓ :=
  show (∐ fun _ : ι => Oₓ) ⟶ Oₓ from
    Sigma.desc (fun j : ι => if j = i then 𝟙 _ else 0)

private theorem free_eta [Fintype ι] [DecidableEq ι] :
    ∑ i : ι, freeProjection (X := X) i ≫ generatingRowInclusion X i = 𝟙 Pₓ :=
  finite_coproduct_eta (C := X.Modules) Oₓ

private def localDualLinear (L : LineBundle X) (U : X.Opens)
    (ell : (dualSheaf X L.val).val.obj (op U)) (V : (Over U)ᵒᵖ) :
    Γ(L.val, V.unop.left) →ₗ[Γ(X, V.unop.left)] Γ(X, V.unop.left) where
  toFun m := ell.val.app V m
  map_add' m n := (ell.val.app V).hom.map_add m n
  map_smul' r m := ell.property V r m

/-- On an actual line chart both module sections are multiples of the
same generator. Separation retains this equality on the original open. -/
private theorem line_scalar_exchange (L : LineBundle X) (U : X.Opens)
    (ell : (dualSheaf X L.val).val.obj (op U)) (m n : Γ(L.val, U)) :
    (show Γ(X, U) from ell.val.app (op (Over.mk (𝟙 U))) m) • n =
      (show Γ(X, U) from ell.val.app (op (Over.mk (𝟙 U))) n) • m := by
  let a : Γ(L.val, U) :=
    (show Γ(X, U) from ell.val.app (op (Over.mk (𝟙 U))) m) • n
  let b : Γ(L.val, U) :=
    (show Γ(X, U) from ell.val.app (op (Over.mk (𝟙 U))) n) • m
  have hc : Presheaf.equalizerSieve (F := L.val.val.presheaf) a b ∈
      (Opens.grothendieckTopology X) U := by
    intro x hxU
    obtain ⟨V, hxV, ⟨e⟩⟩ := (isLocallyRankOne_iff_local_unit X L.val).mp L.property x
    let W := V ⊓ U
    let i : W ⟶ U := homOfLE inf_le_right
    let j : W ⟶ V := homOfLE inf_le_left
    let T : (Over V)ᵒᵖ := op (Over.mk j)
    let m' : Γ(L.val, W) := L.val.val.map i.op m
    let n' : Γ(L.val, W) := L.val.val.map i.op n
    let r : Γ(X, W) := e.hom.val.app T m'
    let s : Γ(X, W) := e.hom.val.app T n'
    let v : Γ(L.val, W) := e.inv.val.app T (1 : Γ(X, W))
    let ev : Γ(L.val, W) → Γ(X, W) := ell.val.app (op (Over.mk i))
    let alpha : Γ(L.val, W) →ₗ[Γ(X, W)] Γ(X, W) := (e.hom.val.app T).hom
    let beta : Γ(X, W) →ₗ[Γ(X, W)] Γ(L.val, W) := (e.inv.val.app T).hom
    have hinv (z : Γ(L.val, W)) : beta (alpha z) = z :=
      congrArg (fun q : L.val.over V ⟶ L.val.over V => q.val.app T z) e.hom_inv_id
    have hgen (z : Γ(L.val, W)) : (show Γ(X, W) from e.hom.val.app T z) • v = z :=
      linear_frame_generator alpha beta hinv z
    have hlin (c : Γ(X, W)) (z : Γ(L.val, W)) : ev (c • z) = c * ev z :=
      (localDualLinear L U ell (op (Over.mk i))).map_smul c z
    have hm : r • v = m' := hgen m'
    have hn : s • v = n' := hgen n'
    have hem : ev m' = r * ev v := by rw [← hm, hlin]
    have hen : ev n' = s * ev v := by rw [← hn, hlin]
    have hlocal : ev m' • n' = ev n' • m' := by
      rw [hem, hen, ← hm, ← hn, smul_smul, smul_smul]
      congr 1
      ring
    have hnatm := NatTrans.naturality_apply ell.val
      (Over.homMk i : Over.mk i ⟶ Over.mk (𝟙 U)).op m
    have hnatn := NatTrans.naturality_apply ell.val
      (Over.homMk i : Over.mk i ⟶ Over.mk (𝟙 U)).op n
    change ev m' = X.presheaf.map i.op (ell.val.app (op (Over.mk (𝟙 U))) m) at hnatm
    change ev n' = X.presheaf.map i.op (ell.val.app (op (Over.mk (𝟙 U))) n) at hnatn
    refine ⟨W, i, ?_, hxV, hxU⟩
    let M : X.Modules := L.val
    have hresa : M.presheaf.map i.op a = ev m' • n' :=
      (Scheme.Modules.map_smul (M := M) i
        (show Γ(X, U) from ell.val.app (op (Over.mk (𝟙 U))) m) n).trans
        (congrArg (fun c : Γ(X, W) => c • n') hnatm.symm)
    have hresb : M.presheaf.map i.op b = ev n' • m' :=
      (Scheme.Modules.map_smul (M := M) i
        (show Γ(X, U) from ell.val.app (op (Over.mk (𝟙 U))) n) m).trans
        (congrArg (fun c : Γ(X, W) => c • m') hnatn.symm)
    change M.presheaf.map i.op a = M.presheaf.map i.op b
    exact hresa.trans (hlocal.trans hresb.symm)
  apply L.val.isSheaf.isSeparated U _ hc
  intro W j hj
  exact hj

private theorem dual_exchange (L : LineBundle X)
    (a b : Oₓ ⟶ (L.val : X.Modules)) :
    dualSection X b ≫ a = dualSection X a ≫ b := by
  apply SheafOfModules.hom_ext
  ext U : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro ell
  let : Module Γ(X, U.unop) (L.val.val.obj U) := (L.val.val.obj U).isModule
  let av : Γ(L.val, U.unop) := a.val.app U (1 : Γ(X, U.unop))
  let bv : Γ(L.val, U.unop) := b.val.app U (1 : Γ(X, U.unop))
  let r : Γ(X, U.unop) := ell.val.app (op (Over.mk (𝟙 U.unop))) bv
  let t : Γ(X, U.unop) := ell.val.app (op (Over.mk (𝟙 U.unop))) av
  change a.val.app U r = b.val.app U t
  let alpha : Γ(X, U.unop) →ₗ[Γ(X, U.unop)] Γ(L.val, U.unop) :=
    (a.val.app U).hom
  let beta : Γ(X, U.unop) →ₗ[Γ(X, U.unop)] Γ(L.val, U.unop) :=
    (b.val.app U).hom
  exact (linear_from_ring alpha r).trans
    ((line_scalar_exchange L U.unop ell bv av).trans (linear_from_ring beta t).symm)

/-- The original signed dual-evaluation relation, lifted through the
actual kernel of the same row. -/
public theorem generatingKernelRelation_comp (L : LineBundle X)
    (π : Pₓ ⟶ (L.val : X.Modules)) (i j : ι) :
    ((dualSection X (generatingRowInclusion X j ≫ π) ≫ generatingRowInclusion X i -
      dualSection X (generatingRowInclusion X i ≫ π) ≫ generatingRowInclusion X j) :
        ((dualLineBundle X L).val : X.Modules) ⟶ Pₓ) ≫ π = 0 := by
  let a : Oₓ ⟶ (L.val : X.Modules) := generatingRowInclusion X i ≫ π
  let b : Oₓ ⟶ (L.val : X.Modules) := generatingRowInclusion X j ≫ π
  let f : ((dualLineBundle X L).val : X.Modules) ⟶ Pₓ :=
    dualSection X b ≫ generatingRowInclusion X i
  let g : ((dualLineBundle X L).val : X.Modules) ⟶ Pₓ :=
    dualSection X a ≫ generatingRowInclusion X j
  have hf : f ≫ π = dualSection X b ≫ a := Category.assoc _ _ _
  have hg : g ≫ π = dualSection X a ≫ b := Category.assoc _ _ _
  have hfg : f ≫ π = g ≫ π := hf.trans ((dual_exchange L a b).trans hg.symm)
  exact (Preadditive.sub_comp f g π).trans (sub_eq_zero.mpr hfg)

/-- The canonical dual relation takes values in the actual kernel. -/
public def generatingKernelDualRelation (L : LineBundle X)
    (π : Pₓ ⟶ (L.val : X.Modules)) (i j : ι) :
    ((dualLineBundle X L).val : X.Modules) ⟶ kernel π :=
  kernel.lift π
    (dualSection X (generatingRowInclusion X j ≫ π) ≫ generatingRowInclusion X i -
      dualSection X (generatingRowInclusion X i ≫ π) ≫ generatingRowInclusion X j)
    (generatingKernelRelation_comp L π i j)

@[reassoc (attr := simp)]
private theorem generatingKernelDualRelation_ι (L : LineBundle X)
    (π : Pₓ ⟶ (L.val : X.Modules)) (i j : ι) :
    generatingKernelDualRelation L π i j ≫ kernel.ι π =
      dualSection X (generatingRowInclusion X j ≫ π) ≫ generatingRowInclusion X i -
        dualSection X (generatingRowInclusion X i ≫ π) ≫ generatingRowInclusion X j :=
  kernel.lift_ι _ _ _

private def crossDualRow (L : LineBundle X)
    (π : Pₓ ⟶ (L.val : X.Modules)) :
    (∐ fun _ : ι × ι => ((dualLineBundle X L).val : X.Modules)) ⟶ kernel π :=
  Sigma.desc (fun ij => generatingKernelDualRelation L π ij.1 ij.2)

private theorem crossDualRow_component (L : LineBundle X)
    (π : Pₓ ⟶ (L.val : X.Modules)) (ij : ι × ι) :
    Sigma.ι (fun _ : ι × ι => ((dualLineBundle X L).val : X.Modules)) ij ≫
        crossDualRow L π = generatingKernelDualRelation L π ij.1 ij.2 :=
  Sigma.ι_comp_desc (C := X.Modules)
    (fun ab : ι × ι => generatingKernelDualRelation L π ab.1 ab.2) ij

private theorem unitEnd_commute (U : X.Opens)
    (a b : SheafOfModules.unit (X.ringCatSheaf.over U) ⟶
      SheafOfModules.unit (X.ringCatSheaf.over U)) : a ≫ b = b ≫ a := by
  apply SheafOfModules.hom_ext
  ext V : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  change Γ(X, V.unop.left) at r
  let α : Γ(X, V.unop.left) →ₗ[Γ(X, V.unop.left)] Γ(X, V.unop.left) :=
    (a.val.app V).hom
  let β : Γ(X, V.unop.left) →ₗ[Γ(X, V.unop.left)] Γ(X, V.unop.left) :=
    (b.val.app V).hom
  have ha (z : Γ(X, V.unop.left)) : α z = z * α 1 := by
    simpa only [smul_eq_mul, mul_one] using α.map_smul z (1 : Γ(X, V.unop.left))
  have hb (z : Γ(X, V.unop.left)) : β z = z * β 1 := by
    simpa only [smul_eq_mul, mul_one] using β.map_smul z (1 : Γ(X, V.unop.left))
  change β (α r) = α (β r)
  rw [hb (α r), ha r, ha (β r), hb r]
  ring

private theorem dualSection_frame (L : LineBundle X) (U : X.Opens)
    (e : L.val.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (t : Oₓ ⟶ (L.val : X.Modules)) :
    (overRestriction U).map (dualSection X t) =
      (dualLocalIso X L.val U e).hom ≫ (overRestriction U).map t ≫ e.hom := by
  apply SheafOfModules.hom_ext
  ext V : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro ell
  let : Module Γ(X, V.unop.left) Γ(L.val, V.unop.left) :=
    (L.val.val.obj (op V.unop.left)).isModule
  let alpha : Γ(L.val, V.unop.left) →ₗ[Γ(X, V.unop.left)] Γ(X, V.unop.left) :=
    (e.hom.val.app V).hom
  let beta : Γ(X, V.unop.left) →ₗ[Γ(X, V.unop.left)] Γ(L.val, V.unop.left) :=
    (e.inv.val.app V).hom
  let tau : Γ(X, V.unop.left) →ₗ[Γ(X, V.unop.left)] Γ(L.val, V.unop.left) :=
    (t.val.app (op V.unop.left)).hom
  let ell' := localDualLinear L V.unop.left ell (op (Over.mk (𝟙 V.unop.left)))
  have hinv (m : Γ(L.val, V.unop.left)) : beta (alpha m) = m :=
    congrArg (fun q : L.val.over U ⟶ L.val.over U => q.val.app V m) e.hom_inv_id
  change ell' (tau 1) = alpha (tau (ell' (beta 1)))
  exact linear_frame_dual alpha beta hinv tau ell'

private theorem exists_row_section_frame (L : LineBundle X)
    (π : Pₓ ⟶ (L.val : X.Modules)) [Epi π] (x : X) :
    ∃ U : X.Opens, x ∈ U ∧
      ∃ (_e : L.val.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
        (h : L.val.over U ⟶ (SheafOfModules.free (R := X.ringCatSheaf) ι).over U),
          h ≫ π.over U = 𝟙 _ := by
  obtain ⟨U, hxU, ⟨e⟩⟩ := (isLocallyRankOne_iff_local_unit X L.val).mp L.property x
  let S : Sheaf ((Opens.grothendieckTopology X).over U) RingCat.{u} :=
    X.ringCatSheaf.over U
  let A : SheafOfModules.{u} S := L.val.over U
  let O : SheafOfModules.{u} S := SheafOfModules.unit S
  let ef : SheafOfModules.free (R := S) PUnit.{u + 1} ≅ A :=
    coproductUniqueIso (fun _ : PUnit.{u + 1} => O) ≪≫ e.symm
  let G := (SheafOfModules.free.generatingSections (R := S) PUnit.{u + 1}).ofEpi ef.hom
  let : G.IsFiniteType := { finite := inferInstanceAs (Finite PUnit.{u + 1}) }
  let p : SheafOfModules.free (R := S) PUnit.{u + 1} ⟶ A := G.π
  have hp : p = ef.hom :=
    (SheafOfModules.GeneratingSections.ofEpi_π
      (SheafOfModules.free.generatingSections (R := S) PUnit.{u + 1}) ef.hom).trans
      ((congrArg (fun g => g ≫ ef.hom)
        (SheafOfModules.free.generatingSections_π (R := S) PUnit.{u + 1})).trans
          (Category.id_comp ef.hom))
  let : IsIso G.π := by
    have hi : IsIso p := iso_of_hom_eq p ef hp
    exact hi
  obtain ⟨V, hVU, hxV, h, hh⟩ := @exists_local_section_of_finite_basis
    X Pₓ (L.val : X.Modules) π (by exact ‹Epi π›) U G inferInstance inferInstance x hxU
  exact ⟨V, hxV, restrictOverUnitIso X L.val (homOfLE hVU) e, h, hh⟩

private theorem crossDualRow_over_epi [Finite ι] (L : LineBundle X)
    (π : Pₓ ⟶ (L.val : X.Modules))
    (U : X.Opens) (e : L.val.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (h : L.val.over U ⟶ (SheafOfModules.free (R := X.ringCatSheaf) ι).over U)
    (hh : h ≫ π.over U = 𝟙 _) : Epi ((overRestriction U).map (crossDualRow L π)) := by
  classical
  let := Fintype.ofFinite ι
  let F := overRestriction U
  let : F.Additive := overRestriction_additive U
  let : F.IsRightAdjoint := overRestriction_isRightAdjoint U
  let e' : F.obj (L.val : X.Modules) ≅ F.obj Oₓ := e
  let d : F.obj ((dualLineBundle X L).val : X.Modules) ≅ F.obj Oₓ :=
    dualLocalIso X L.val U e
  let inc (i : ι) := F.map (generatingRowInclusion X i)
  let pr (i : ι) := F.map (freeProjection (X := X) i)
  have hη : ∑ i, pr i ≫ inc i = 𝟙 _ :=
    mapped_eta F (generatingRowInclusion X) (freeProjection (X := X))
      (free_eta (X := X) (ι := ι))
  let h₀ : F.obj (L.val : X.Modules) ⟶ F.obj Pₓ := h
  have hh₀ : h₀ ≫ F.map π = 𝟙 (F.obj (L.val : X.Modules)) := hh
  let q := F.map π ≫ e'.hom
  let h' := e'.inv ≫ h₀
  have hh' : h' ≫ q = 𝟙 _ := by
    calc
      h' ≫ q = e'.inv ≫ (h₀ ≫ F.map π) ≫ e'.hom := by
        simp only [h', q, Category.assoc]
      _ = 𝟙 _ := by rw [hh₀, Category.id_comp, e'.inv_hom_id]
  have hk : F.map (kernel.ι π) ≫ q = 0 := by
    have hmap : F.map (kernel.ι π) ≫ F.map π = 0 :=
      mapped_zero_comp F (kernel.ι π) π (kernel.condition π)
    calc
      F.map (kernel.ι π) ≫ q = (F.map (kernel.ι π) ≫ F.map π) ≫ e'.hom :=
        (Category.assoc _ _ _).symm
      _ = 0 := by rw [hmap, zero_comp]
  let t (ij : ι × ι) := d.inv ≫
    F.map (Sigma.ι (fun _ : ι × ι => ((dualLineBundle X L).val : X.Modules)) ij)
  have ht (i j : ι) : t (i, j) ≫ F.map (crossDualRow L π) ≫ F.map (kernel.ι π) =
      (inc j ≫ q) ≫ inc i - (inc i ≫ q) ≫ inc j :=
    mapped_cross_formula F (generatingRowInclusion X i) (generatingRowInclusion X j) π
      (dualSection X (generatingRowInclusion X i ≫ π))
      (dualSection X (generatingRowInclusion X j ≫ π))
      (generatingKernelDualRelation L π i j) (kernel.ι π)
      (Sigma.ι (fun _ : ι × ι => ((dualLineBundle X L).val : X.Modules)) (i, j))
      (crossDualRow L π) d e' (crossDualRow_component L π (i, j))
      (generatingKernelDualRelation_ι L π i j)
      (dualSection_frame L U e (generatingRowInclusion X i ≫ π))
      (dualSection_frame L U e (generatingRowInclusion X j ≫ π))
  let : Mono (F.map (kernel.ι π)) :=
    map_mono_with F (kernel.ι π)
      (Fork.IsLimit.mono (limit.isLimit (parallelPair π 0)))
  exact finite_cross_epi inc pr hη q h' hh' (F.map (kernel.ι π)) hk
    (F.map (crossDualRow L π)) t ht (unitEnd_commute U)

private theorem restrict_zero_of_over {M N : X.Modules} (f : M ⟶ N)
    (U : X.Opens) (h : (overRestriction U).map f = 0) :
    (restrictFunctor U.ι).map f = 0 := by
  let E := (overEquiv U).functor
  let : E.IsEquivalence := inferInstanceAs ((overEquiv U).functor.IsEquivalence)
  let η : overRestriction U ⋙ E ≅ restrictFunctor U.ι := overFunctorEquiv U
  let a : E.obj ((overRestriction U).obj M) ≅ (restrictFunctor U.ι).obj M := η.app M
  apply (cancel_epi a.hom).mp
  calc
    a.hom ≫ (restrictFunctor U.ι).map f =
        E.map ((overRestriction U).map f) ≫ η.hom.app N :=
      (η.hom.naturality f).symm
    _ = 0 := by rw [h, Functor.map_zero, zero_comp]
    _ = a.hom ≫ 0 := by simp

private theorem crossDualRow_epi [Finite ι] (L : LineBundle X)
    (π : Pₓ ⟶ (L.val : X.Modules)) [Epi π] :
    Epi (crossDualRow L π) := by
  apply Preadditive.epi_of_cancel_zero
  intro N g hg
  apply eq_zero_of_local_restrict X g
  intro x
  obtain ⟨U, hx, e, h, hh⟩ := exists_row_section_frame L π x
  let : Epi ((overRestriction U).map (crossDualRow L π)) :=
    crossDualRow_over_epi L π U e h hh
  refine ⟨U, hx, restrict_zero_of_over g U ?_⟩
  apply zero_of_epi_comp ((overRestriction U).map (crossDualRow L π))
  exact ((overRestriction U).map_comp _ _).symm.trans
    ((congrArg (overRestriction U).map hg).trans ((overRestriction U).map_zero _ _))

private theorem evaluation_tensor_section (L : LineBundle X) (U : X.Opens)
    (ell : (dualSheaf X L.val).val.obj (op U)) (m : Γ(L.val, U)) :
    (dualEvaluationIso X L).hom.val.app (op U)
        (moduleTensorSection X (dualLineBundle X L).val L.val U ell m) =
      ell.val.app (op (Over.mk (𝟙 U))) m := by
  let R : Sheaf (Opens.grothendieckTopology X) RingCat.{u} := X.ringCatSheaf
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)
  let P : _root_.PresheafOfModules.{u} R.obj :=
    PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf)
      (dualSheaf X L.val).val L.val.val
  let O : SheafOfModules.{u} R := SheafOfModules.unit R
  let f : P ⟶ (PresheafOfModules.restrictScalars (𝟙 R.obj)).obj
      ((SheafOfModules.forget R).obj O) := evaluationPresheaf X L.val O
  let ev : (PresheafOfModules.sheafification (𝟙 R.obj)).obj P ⟶ O :=
    evaluationSheaf X L.val O
  have he : adj.homEquiv P O ev = f :=
    (_root_.PresheafOfModules.sheafificationHomEquiv
      (𝟙 R.obj) (P := P) (F := O)).apply_symm_apply f
  have hu := (adj.homEquiv_unit P O ev).symm.trans he
  have hv : ev.val.app (op U)
      (moduleTensorSection X (dualLineBundle X L).val L.val U ell m) =
      ell.val.app (op (Over.mk (𝟙 U))) m :=
    congrArg (fun f => f.app (op U) (ell ⊗ₜ[Γ(X, U)] m)) hu
  exact (congrArg (fun f => f.val.app (op U)
    (moduleTensorSection X (dualLineBundle X L).val L.val U ell m))
      (dualEvaluationIso_hom X L)).trans hv

private theorem dualSection_tensor_contraction (L : LineBundle X)
    (s : Oₓ ⟶ (L.val : X.Modules)) :
    tensorSheafMap X (dualSection X s) (𝟙 (L.val : X.Modules)) ≫
        (tensorSheafLeftUnit X L.val).hom =
      (dualEvaluationIso X L).hom ≫ s := by
  apply moduleTensor_hom_ext
  intro U ell m
  let : Module Γ(X, U) (L.val.val.obj (op U)) :=
    (L.val.val.obj (op U)).isModule
  let a : Γ(X, U) := (dualSection X s).val.app (op U) ell
  have ha : a =
      (show Γ(X, U) from ell.val.app (op (Over.mk (𝟙 U))) (s.val.app (op U) (1 : Γ(X, U)))) :=
    dualSection_apply X s U ell
  have hmap : (tensorSheafMap X (dualSection X s) (𝟙 (L.val : X.Modules))).val.app
      (op U) (moduleTensorSection X (dualLineBundle X L).val L.val U ell m) =
      moduleTensorSection X Oₓ L.val U a m :=
    tensorSheafMap_tmul X (dualSection X s) (𝟙 (L.val : X.Modules)) (op U) ell m
  have hleft : (tensorSheafLeftUnit X L.val).hom.val.app (op U)
      (moduleTensorSection X Oₓ L.val U a m) = a • m :=
    tensorSheafLeftUnit_tmul X L.val (op U) a m
  let tau : Γ(X, U) →ₗ[Γ(X, U)] Γ(L.val, U) := (s.val.app (op U)).hom
  have hs (r : Γ(X, U)) : s.val.app (op U) r =
      r • s.val.app (op U) (1 : Γ(X, U)) := linear_from_ring tau r
  have hright : s.val.app (op U) ((dualEvaluationIso X L).hom.val.app (op U)
      (moduleTensorSection X (dualLineBundle X L).val L.val U ell m)) =
      (show Γ(X, U) from ell.val.app (op (Over.mk (𝟙 U))) m) • s.val.app (op U) (1 : Γ(X, U)) :=
    (congrArg (s.val.app (op U)) (evaluation_tensor_section L U ell m)).trans (hs _)
  have hfirst :=
    (congrArg ((tensorSheafLeftUnit X L.val).hom.val.app (op U)) hmap).trans hleft
  have hsecond : a • m = s.val.app (op U)
      ((dualEvaluationIso X L).hom.val.app (op U)
        (moduleTensorSection X (dualLineBundle X L).val L.val U ell m)) :=
    (congrArg (fun r : Γ(X, U) => r • m) ha).trans
      ((line_scalar_exchange L U ell (s.val.app (op U) (1 : Γ(X, U))) m).trans hright.symm)
  exact hfirst.trans hsecond

private theorem coevaluation_dualSection (L : LineBundle X)
    (s : Oₓ ⟶ (L.val : X.Modules)) :
    (dualEvaluationIso X L).inv ≫ tensorSheafMap X (dualSection X s) (𝟙 (L.val : X.Modules)) =
      (tensorSheafLeftUnit X Oₓ).inv ≫
        tensorSheafMap X (𝟙 Oₓ) s := by
  let M : X.Modules := L.val
  let D : X.Modules := (dualLineBundle X L).val
  let ev : tensorSheaf X D M ≅ Oₓ := dualEvaluationIso X L
  let leftUnitM : tensorSheaf X Oₓ M ≅ M := tensorSheafLeftUnit X M
  let leftUnitO : tensorSheaf X Oₓ Oₓ ≅ Oₓ := tensorSheafLeftUnit X Oₓ
  let unitor : moduleTensorLeftFunctor X Oₓ ≅ 𝟭 X.Modules :=
    SheafOfModulesOfCommRing.tensorLeftUnitIso X.sheaf
  have hc : tensorSheafMap X (dualSection X s) (𝟙 M) ≫ leftUnitM.hom = ev.hom ≫ s :=
    dualSection_tensor_contraction L s
  have hn : tensorSheafMap X (𝟙 Oₓ) s ≫ leftUnitM.hom = leftUnitO.hom ≫ s :=
    unitor.hom.naturality s
  exact evaluation_unit_cancel ev leftUnitM leftUnitO
    (tensorSheafMap X (dualSection X s) (𝟙 M))
    (tensorSheafMap X (𝟙 Oₓ) s) s hc hn

/-- The ordered pair of original generators gives a canonical section
of the tensor of the actual kernel with the original line bundle. -/
public def generatingKernelSection (L : LineBundle X)
    (π : Pₓ ⟶ (L.val : X.Modules)) (i j : ι) :
    Oₓ ⟶ (moduleTensorRightFunctor X L.val).obj (kernel π) :=
  (dualEvaluationIso X L).inv ≫
    (moduleTensorRightFunctor X L.val).map (generatingKernelDualRelation L π i j)

-- These factories fix one native right-tensor object presentation before
-- the free object, kernel, line bundle and dual are specialized together.
private def originalTensorUnit :
    (moduleTensorRightFunctor X Oₓ).obj Oₓ ≅ Oₓ :=
  tensorSheafLeftUnit X Oₓ

private def originalTensorSection (M : X.Modules) (s : Oₓ ⟶ M) :
    (moduleTensorRightFunctor X Oₓ).obj Oₓ ⟶
      (moduleTensorRightFunctor X M).obj Oₓ :=
  tensorSheafMap X (M := Oₓ) (M' := Oₓ) (N := Oₓ) (N' := M) (𝟙 Oₓ) s

private def originalTensorPair (M P : X.Modules) (a : Oₓ ⟶ P) (s : Oₓ ⟶ M) :
    (moduleTensorRightFunctor X Oₓ).obj Oₓ ⟶
      (moduleTensorRightFunctor X M).obj P :=
  tensorSheafMap X (M := Oₓ) (M' := P) (N := Oₓ) (N' := M) a s

private def originalTensorCross (M P : X.Modules)
    (a b : Oₓ ⟶ P) (si sj : Oₓ ⟶ M) : Oₓ ⟶ (moduleTensorRightFunctor X M).obj P :=
  (originalTensorUnit (X := X)).inv ≫
    (originalTensorPair M P a sj - originalTensorPair M P b si)

private theorem originalTensorCross_eq (M P : X.Modules)
    (a b : Oₓ ⟶ P) (si sj : Oₓ ⟶ M) :
    originalTensorCross M P a b si sj =
      (tensorSheafLeftUnit X Oₓ).inv ≫
        (tensorSheafMap X (M := Oₓ) (M' := P) (N := Oₓ) (N' := M) a sj -
          tensorSheafMap X (M := Oₓ) (M' := P) (N := Oₓ) (N' := M) b si) := rfl

private theorem originalTensorCross_post_eq (M P : X.Modules)
    (a b : Oₓ ⟶ P) (si sj : Oₓ ⟶ M) {N : X.Modules}
    (h : (moduleTensorRightFunctor X M).obj P ⟶ N) :
    originalTensorCross M P a b si sj ≫ h =
      (tensorSheafLeftUnit X Oₓ).inv ≫
        (tensorSheafMap X (M := Oₓ) (M' := P) (N := Oₓ) (N' := M) a sj -
          tensorSheafMap X (M := Oₓ) (M' := P) (N := Oₓ) (N' := M) b si) ≫ h :=
  (congrArg (fun f : Oₓ ⟶ (moduleTensorRightFunctor X M).obj P => f ≫ h)
    (originalTensorCross_eq M P a b si sj)).trans
      (Category.assoc (tensorSheafLeftUnit X Oₓ).inv
        (tensorSheafMap X (M := Oₓ) (M' := P) (N := Oₓ) (N' := M) a sj -
          tensorSheafMap X (M := Oₓ) (M' := P) (N := Oₓ) (N' := M) b si) h)

private theorem unit_tensor_pair_comp (M P : X.Modules)
    (a : Oₓ ⟶ P) (s : Oₓ ⟶ M) :
    originalTensorSection M s ≫ (moduleTensorRightFunctor X M).map a =
      originalTensorPair M P a s :=
  (tensorSheafMap_comp X (M := Oₓ) (M' := Oₓ) (M'' := P)
    (N := Oₓ) (N' := M) (N'' := M) (𝟙 Oₓ) s a (𝟙 M)).trans
      (congrArg₂ (fun (f : Oₓ ⟶ P) (g : Oₓ ⟶ M) =>
        tensorSheafMap X (M := Oₓ) (M' := P) (N := Oₓ) (N' := M) f g)
          (Category.id_comp a) (Category.comp_id s))

private theorem originalTensorContraction (L : LineBundle X)
    (s : Oₓ ⟶ (L.val : X.Modules)) :
    (dualEvaluationIso X L).inv ≫
        (moduleTensorRightFunctor X L.val).map (dualSection X s) =
      (originalTensorUnit (X := X)).inv ≫ originalTensorSection L.val s :=
  coevaluation_dualSection L s

-- The complete right-hand map has its native target fixed by the factory.
-- The expanded tensorSheafMap formula is recovered by originalTensorCross_eq.
private theorem generatingKernelSection_formula (L : LineBundle X)
    (π : Pₓ ⟶ (L.val : X.Modules)) (i j : ι) :
    generatingKernelSection L π i j ≫ (moduleTensorRightFunctor X L.val).map (kernel.ι π) =
      originalTensorCross L.val Pₓ (generatingRowInclusion X i) (generatingRowInclusion X j)
        (generatingRowInclusion X i ≫ π) (generatingRowInclusion X j ≫ π) := by
  let T := moduleTensorRightFunctor X L.val
  let : T.Additive := moduleTensorRightFunctor_additive X L.val
  let D : X.Modules := (dualLineBundle X L).val
  let M : X.Modules := L.val
  let ev : T.obj D ≅ Oₓ := dualEvaluationIso X L
  let u : (moduleTensorRightFunctor X Oₓ).obj Oₓ ≅ Oₓ := originalTensorUnit
  let si : Oₓ ⟶ M := generatingRowInclusion X i ≫ π
  let sj : Oₓ ⟶ M := generatingRowInclusion X j ≫ π
  have hx : (u.inv ≫ originalTensorSection M sj) ≫ T.map (generatingRowInclusion X i) =
      u.inv ≫ originalTensorPair M Pₓ (generatingRowInclusion X i) sj :=
    (Category.assoc _ _ _).trans
      (congrArg (fun f => u.inv ≫ f) (unit_tensor_pair_comp M Pₓ _ _))
  have hy : (u.inv ≫ originalTensorSection M si) ≫ T.map (generatingRowInclusion X j) =
      u.inv ≫ originalTensorPair M Pₓ (generatingRowInclusion X j) si :=
    (Category.assoc _ _ _).trans
      (congrArg (fun f => u.inv ≫ f) (unit_tensor_pair_comp M Pₓ _ _))
  have hf : OriginalCrossEquation (C := X.Modules) (generatingKernelSection L π i j)
      (T.map (kernel.ι π)) u.inv
      (originalTensorPair M Pₓ (generatingRowInclusion X i) sj)
      (originalTensorPair M Pₓ (generatingRowInclusion X j) si) :=
    tensor_cross_paste (C := X.Modules) T ev u (dualSection X si) (dualSection X sj)
      (generatingRowInclusion X i) (generatingRowInclusion X j)
      (generatingKernelDualRelation L π i j) (kernel.ι π)
      (generatingKernelDualRelation_ι L π i j)
      (u.inv ≫ originalTensorSection M si) (u.inv ≫ originalTensorSection M sj)
      (originalTensorContraction L si) (originalTensorContraction L sj)
      (originalTensorPair M Pₓ (generatingRowInclusion X i) sj)
      (originalTensorPair M Pₓ (generatingRowInclusion X j) si) hx hy
      (generatingKernelSection L π i j) rfl
  exact cross_equation_endpoints (C := X.Modules) (generatingKernelSection L π i j)
    (T.map (kernel.ι π)) u.inv
    (originalTensorPair M Pₓ (generatingRowInclusion X i) sj)
    (originalTensorPair M Pₓ (generatingRowInclusion X j) si)
    (generatingKernelSection L π i j ≫ T.map (kernel.ι π))
    (originalTensorCross M Pₓ (generatingRowInclusion X i) (generatingRowInclusion X j) si sj)
    rfl rfl hf

set_option maxHeartbeats 400000 in
-- Native runs 6007d9ca and be9e0b00 exhausted this concrete adapter.
-- Keep only its existing bounded allowance while the typed constructor
-- supplies the same original formula with every module object explicit.
/-- The inclusion equation is the literal cross relation in the original
free row, with the canonical unit normalization of the two tensor factors. -/
public theorem generatingKernelSection_ι (L : LineBundle X)
    (π : Pₓ ⟶ (L.val : X.Modules)) (i j : ι) :
    generatingKernelSection L π i j ≫ (moduleTensorRightFunctor X L.val).map (kernel.ι π) =
      (tensorSheafLeftUnit X Oₓ).inv ≫
        (tensorSheafMap X (M := Oₓ) (M' := Pₓ) (N := Oₓ) (N' := (L.val : X.Modules))
          (generatingRowInclusion X i) (generatingRowInclusion X j ≫ π) -
          tensorSheafMap X (M := Oₓ) (M' := Pₓ) (N := Oₓ) (N' := (L.val : X.Modules))
          (generatingRowInclusion X j) (generatingRowInclusion X i ≫ π)) := by
  exact (generatingKernelSection_formula L π i j).trans
    (originalTensorCross_eq L.val Pₓ (generatingRowInclusion X i) (generatingRowInclusion X j)
      (generatingRowInclusion X i ≫ π) (generatingRowInclusion X j ≫ π))

set_option maxHeartbeats 400000 in
-- The original postcomposition has the same concrete carrier conversion;
-- retain its existing bounded allowance, without changing the package default.
/-- Postcomposition of the same original inclusion equation. -/
public theorem generatingKernelSection_ι_assoc (L : LineBundle X)
    (π : Pₓ ⟶ (L.val : X.Modules)) (i j : ι) {N : X.Modules}
    (a : (moduleTensorRightFunctor X L.val).obj Pₓ ⟶ N) :
    generatingKernelSection L π i j ≫
        (moduleTensorRightFunctor X L.val).map (kernel.ι π) ≫ a =
      (tensorSheafLeftUnit X Oₓ).inv ≫
        (tensorSheafMap X (M := Oₓ) (M' := Pₓ) (N := Oₓ) (N' := (L.val : X.Modules))
          (generatingRowInclusion X i) (generatingRowInclusion X j ≫ π) -
          tensorSheafMap X (M := Oₓ) (M' := Pₓ) (N := Oₓ) (N' := (L.val : X.Modules))
          (generatingRowInclusion X j) (generatingRowInclusion X i ≫ π)) ≫ a :=
  (original_eq_post (C := X.Modules) (generatingKernelSection L π i j)
    ((moduleTensorRightFunctor X L.val).map (kernel.ι π))
    (originalTensorCross L.val Pₓ (generatingRowInclusion X i) (generatingRowInclusion X j)
      (generatingRowInclusion X i ≫ π) (generatingRowInclusion X j ≫ π))
    (generatingKernelSection_formula L π i j) a).trans
      (originalTensorCross_post_eq L.val Pₓ
        (generatingRowInclusion X i) (generatingRowInclusion X j)
        (generatingRowInclusion X i ≫ π) (generatingRowInclusion X j ≫ π) a)

/-- The original finite free row of ordered cross relations. -/
public def generatingKernelMap (L : LineBundle X)
    (π : Pₓ ⟶ (L.val : X.Modules)) :
    (SheafOfModules.free (R := X.ringCatSheaf) (ι × ι) : X.Modules) ⟶
      (moduleTensorRightFunctor X L.val).obj (kernel π) :=
  Sigma.desc (fun ij => generatingKernelSection L π ij.1 ij.2)

@[simp, reassoc]
public theorem ιFree_generatingKernelMap (L : LineBundle X)
    (π : Pₓ ⟶ (L.val : X.Modules)) (ij : ι × ι) :
    SheafOfModules.ιFree ij ≫ generatingKernelMap L π =
      generatingKernelSection L π ij.1 ij.2 :=
  show Sigma.ι (fun _ : ι × ι => Oₓ) ij ≫
    Sigma.desc (fun ab : ι × ι => generatingKernelSection L π ab.1 ab.2) = _ from
      Sigma.ι_comp_desc _ _

/-- The actual ordered cross relations generate the original tensor kernel
for every finite epimorphic row onto an actual line bundle. -/
public theorem generatingKernelMap_epi [Finite ι] (L : LineBundle X)
    (π : Pₓ ⟶ (L.val : X.Modules)) [Epi π] :
    Epi (generatingKernelMap L π) := by
  let T := moduleTensorRightFunctor X L.val
  let : IsFiniteLocallyFree X L.val := isFiniteLocallyFree_of_isLocallyRankOne L.property
  let : T.Additive := moduleTensorRightFunctor_additive X L.val
  let : T.PreservesHomology := moduleTensorRight_preservesHomology L.val
  let : PreservesFiniteColimits T := Functor.preservesFiniteColimits_of_preservesHomology T
  have hT : Epi (T.map (crossDualRow L π)) :=
    map_epi_with T (crossDualRow L π) (crossDualRow_epi L π)
  let D : X.Modules := (dualLineBundle X L).val
  let ev : T.obj D ≅ Oₓ := dualEvaluationIso X L
  let f : ι × ι → X.Modules := fun _ => D
  let e : (SheafOfModules.free (R := X.ringCatSheaf) (ι × ι) : X.Modules) ≅
      T.obj (∐ f) :=
    Sigma.mapIso (fun _ : ι × ι => ev.symm) ≪≫ (PreservesCoproduct.iso T f).symm
  have hei (ij : ι × ι) : Sigma.ι (fun _ : ι × ι => Oₓ) ij ≫ e.hom =
      ev.inv ≫ T.map (Sigma.ι f ij) :=
    mapped_coproduct_inclusion T f Oₓ (fun _ : ι × ι => ev.symm) ij
  have he : generatingKernelMap L π = e.hom ≫ T.map (crossDualRow L π) :=
    coproduct_desc_map T
      (fun ij : ι × ι => generatingKernelDualRelation L π ij.1 ij.2) e ev.inv hei
  exact he.symm ▸ epi_iso_comp e (T.map (crossDualRow L π)) hT

end AlgebraicGeometry.Scheme.Modules.Invertible
