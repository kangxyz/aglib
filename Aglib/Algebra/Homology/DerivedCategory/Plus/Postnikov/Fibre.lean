/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Plus.Postnikov.MultiplicationFibre
public import Aglib.Algebra.Homology.DerivedCategory.Plus.Postnikov.MixedEdge
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE

/-! The original fibre restricting the top homology of a two-layer object. -/

open CategoryTheory CategoryTheory.Limits

@[expose] public noncomputable section

namespace DerivedCategory.Plus

variable {C : Type*} [Category* C] [Abelian C]
  {B J P : C} (e : B ≅ P) (i : J ⟶ P)

/-- The original matrix `[(e),(-i)]` has the literal graph of `i` as kernel.
Its second projection is the identity on `J`. -/
private def graphKernelIsLimit :
    IsLimit (KernelFork.ofι (biprod.lift (i ≫ e.inv) (𝟙 J))
      (show biprod.lift (i ≫ e.inv) (𝟙 J) ≫ biprod.desc e.hom (-i) = 0 by
        simp [biprod.lift_desc, Category.assoc])) := by
  let g := biprod.desc e.hom (-i)
  let s := biprod.lift (i ≫ e.inv) (𝟙 J)
  have hs : s ≫ g = 0 := by simp [s, g, biprod.lift_desc, Category.assoc]
  refine KernelFork.IsLimit.ofι _ _
    (fun {W} f hf => f ≫ biprod.snd) ?_ ?_
  · intro W f hf
    apply biprod.hom_ext
    · have hfg : (f ≫ biprod.fst) ≫ e.hom = (f ≫ biprod.snd) ≫ i := by
        have := hf
        simp only [biprod.desc_eq, Preadditive.comp_add,
          Preadditive.comp_neg, add_neg_eq_zero] at this
        simpa only [Category.assoc] using this
      rw [Category.assoc, biprod.lift_fst]
      apply (cancel_mono e.hom).mp
      simpa only [Category.assoc, e.inv_hom_id, Category.comp_id] using hfg.symm
    · simp
  · intro W f hf m hm
    simpa using congrArg (fun t => t ≫ biprod.snd) hm

/-- In any original short exact realization of this one matrix kernel,
projection to `J` is an isomorphism. -/
private theorem graphShortExact_snd_isIso {K : C} (k : K ⟶ B ⊞ J)
    (hk : k ≫ biprod.desc e.hom (-i) = 0)
    (hS : (ShortComplex.mk k (biprod.desc e.hom (-i)) hk).ShortExact) :
    IsIso (k ≫ biprod.snd) := by
  let s := biprod.lift (i ≫ e.inv) (𝟙 J)
  have hs : s ≫ biprod.desc e.hom (-i) = 0 := by
    simp [s, biprod.lift_desc, Category.assoc]
  let hgraph : IsLimit (KernelFork.ofι s hs) := by
    exact graphKernelIsLimit e i
  let hkernel : IsLimit (KernelFork.ofι k hk) := hS.fIsKernel
  let E : J ≅ K := hgraph.conePointUniqueUpToIso hkernel
  have hE : E.hom ≫ k = s :=
    hgraph.conePointUniqueUpToIso_hom_comp hkernel WalkingParallelPair.zero
  have hproj : k ≫ biprod.snd = E.inv := by
    apply (cancel_epi E.hom).mp
    rw [← Category.assoc, hE]
    simp only [s, biprod.lift_snd]
    exact E.hom_inv_id.symm
  rw [hproj]
  infer_instance

/-- The first projection of that original kernel is the inclusion after
the same graph-coordinate isomorphism and the chosen `e`. -/
private theorem graphShortExact_fst_comp {K : C} (k : K ⟶ B ⊞ J)
    (hk : k ≫ biprod.desc e.hom (-i) = 0) :
    k ≫ biprod.fst ≫ e.hom = k ≫ biprod.snd ≫ i := by
  have h := hk
  simpa only [biprod.desc_eq, Preadditive.comp_add,
    Preadditive.comp_neg, add_neg_eq_zero] using h

/-- The same graph conclusion after only the ORIGINAL H¹ biproduct and target
isomorphisms; the source short complex itself is not replaced. -/
private theorem graphShortExact_transport {S : ShortComplex C} (hS : S.ShortExact)
    (m : S.X₂ ≅ B ⊞ J) (t : S.X₃ ≅ P)
    (hmatrix : m.inv ≫ S.g ≫ t.hom = biprod.desc e.hom (-i)) :
    IsIso (S.f ≫ m.hom ≫ biprod.snd) ∧
      S.f ≫ m.hom ≫ biprod.fst ≫ e.hom =
        S.f ≫ m.hom ≫ biprod.snd ≫ i := by
  let g := biprod.desc e.hom (-i)
  let k := S.f ≫ m.hom
  have hmg : m.hom ≫ g = S.g ≫ t.hom := by
    change m.hom ≫ biprod.desc e.hom (-i) = S.g ≫ t.hom
    rw [← hmatrix]
    rw [← Category.assoc m.hom m.inv (S.g ≫ t.hom), m.hom_inv_id,
      Category.id_comp]
  have hk : k ≫ g = 0 := by
    change (S.f ≫ m.hom) ≫ g = 0
    rw [Category.assoc, hmg, ← Category.assoc, S.zero, zero_comp]
  let S' := ShortComplex.mk k g hk
  let E : S ≅ S' := ShortComplex.isoMk (Iso.refl _) m t
    (by simp [S', k]) (by simpa only [S'] using hmg)
  have hS' : S'.ShortExact := ShortComplex.shortExact_of_iso E hS
  have hiso : IsIso (k ≫ biprod.snd) := graphShortExact_snd_isIso e i k hk hS'
  have hformula := graphShortExact_fst_comp e i k hk
  simpa only [k, Category.assoc] using (And.intro hiso hformula)

end DerivedCategory.Plus

open CategoryTheory CategoryTheory.Limits


namespace DerivedCategory.Plus

variable {C D : Type*} [Category* C] [Category* D]
  [Preadditive C] [Preadditive D]
  (F : C ⥤ D) [F.Additive]
  {B J P : C} {B₀ J₀ P₀ : D}
  [HasBinaryBiproduct B J]
  [PreservesBinaryBiproduct B J F]
  [HasBinaryBiproduct B₀ J₀]
  (eB : F.obj B ≅ B₀) (eJ : F.obj J ≅ J₀) (eP : F.obj P ≅ P₀)
  (r : B ⟶ P) (j : J ⟶ P) (r₀ : B₀ ⟶ P₀) (j₀ : J₀ ⟶ P₀)

/-- The native additive functor sends the exact original matrix to the
same matrix on its original compared coefficient objects. -/
private theorem map_biprod_desc_matrix
    (hr : F.map r ≫ eP.hom = eB.hom ≫ r₀)
    (hj : F.map j ≫ eP.hom = eJ.hom ≫ j₀) :
    let eM := F.mapBiprod B J ≪≫ biprod.mapIso eB eJ
    eM.inv ≫ F.map (biprod.desc r (-j)) ≫ eP.hom =
      biprod.desc r₀ (-j₀) := by
  intro eM
  have hleft : biprod.inl ≫ eM.inv =
      eB.inv ≫ F.map (biprod.inl : B ⟶ B ⊞ J) := by
    dsimp only [eM]
    simp only [Iso.trans_inv, biprod.mapIso_inv, Functor.mapBiprod_inv]
    rw [← Category.assoc, biprod.inl_map, Category.assoc, biprod.inl_desc]
  have hright : biprod.inr ≫ eM.inv =
      eJ.inv ≫ F.map (biprod.inr : J ⟶ B ⊞ J) := by
    dsimp only [eM]
    simp only [Iso.trans_inv, biprod.mapIso_inv, Functor.mapBiprod_inv]
    rw [← Category.assoc, biprod.inr_map, Category.assoc, biprod.inr_desc]
  apply biprod.hom_ext'
  · rw [biprod.inl_desc]
    rw [← Category.assoc biprod.inl eM.inv, hleft]
    calc
      _ = eB.inv ≫ F.map r ≫ eP.hom := by
        rw [← Category.assoc (eB.inv ≫ F.map (biprod.inl : B ⟶ B ⊞ J))
          (F.map (biprod.desc r (-j))) eP.hom,
          Category.assoc eB.inv (F.map (biprod.inl : B ⟶ B ⊞ J))
            (F.map (biprod.desc r (-j))), ← F.map_comp, biprod.inl_desc]
        simp only [Category.assoc]
      _ = eB.inv ≫ eB.hom ≫ r₀ := by rw [hr]
      _ = r₀ := by rw [← Category.assoc, eB.inv_hom_id, Category.id_comp]
  · rw [biprod.inr_desc]
    rw [← Category.assoc biprod.inr eM.inv, hright]
    calc
      _ = eJ.inv ≫ F.map (-j) ≫ eP.hom := by
        rw [← Category.assoc (eJ.inv ≫ F.map (biprod.inr : J ⟶ B ⊞ J))
          (F.map (biprod.desc r (-j))) eP.hom,
          Category.assoc eJ.inv (F.map (biprod.inr : J ⟶ B ⊞ J))
            (F.map (biprod.desc r (-j))), ← F.map_comp, biprod.inr_desc]
        simp only [Category.assoc]
      _ = -(eJ.inv ≫ F.map j ≫ eP.hom) := by
        rw [F.map_neg]
        simp only [Preadditive.comp_neg, Preadditive.neg_comp]
      _ = -j₀ := by
        have hbase : eJ.inv ≫ F.map j ≫ eP.hom = j₀ := by
          rw [hj, ← Category.assoc eJ.inv eJ.hom j₀,
            eJ.inv_hom_id, Category.id_comp]
        exact congrArg Neg.neg hbase

/-- When the normalized first component is an iso, the actual original
matrix map is epic, without a second target or quotient model. -/
private theorem map_biprod_desc_epi_of_iso [IsIso r₀]
    (hr : F.map r ≫ eP.hom = eB.hom ≫ r₀)
    (hj : F.map j ≫ eP.hom = eJ.hom ≫ j₀) :
    Epi (F.map (biprod.desc r (-j))) := by
  let eM := F.mapBiprod B J ≪≫ biprod.mapIso eB eJ
  have hsplit : IsSplitEpi (biprod.desc r₀ (-j₀)) :=
    IsSplitEpi.mk' ⟨inv r₀ ≫ biprod.inl, by simp⟩
  have hcomp : Epi (eM.inv ≫ F.map (biprod.desc r (-j)) ≫ eP.hom) := by
    rw [map_biprod_desc_matrix F eB eJ eP r j r₀ j₀ hr hj]
    infer_instance
  have hmid : Epi (eM.inv ≫ F.map (biprod.desc r (-j))) :=
    (epi_comp_iff_of_isIso _ eP.hom).mp (by simpa only [Category.assoc] using hcomp)
  exact (epi_comp_iff_of_epi eM.inv (F.map (biprod.desc r (-j)))).mp hmid

end DerivedCategory.Plus

open CategoryTheory CategoryTheory.Limits


namespace DerivedCategory.Plus

/-- The original binary first projection remains an isomorphism under an
additive functor when the second original summand has zero image. -/
private theorem map_biprod_fst_isIso_of_isZero
    {C D : Type*} [Category* C] [Category* D]
    [Preadditive C] [Preadditive D]
    (F : C ⥤ D) [F.Additive]
    (B J : C) [HasBinaryBiproduct B J] (hJ : IsZero (F.obj J)) :
    IsIso (F.map (biprod.fst : B ⊞ J ⟶ B)) := by
  let f := F.map (biprod.fst : B ⊞ J ⟶ B)
  let s := F.map (biprod.inl : B ⟶ B ⊞ J)
  have hs : s ≫ f = 𝟙 (F.obj B) := by
    change F.map biprod.inl ≫ F.map biprod.fst = 𝟙 _
    rw [← F.map_comp, biprod.inl_fst, F.map_id]
  have hz : F.map (biprod.snd : B ⊞ J ⟶ J) ≫
      F.map (biprod.inr : J ⟶ B ⊞ J) = 0 := by
    have h : F.map (biprod.snd : B ⊞ J ⟶ J) = 0 := hJ.eq_of_tgt _ _
    rw [h, zero_comp]
  have ht := congrArg F.map (biprod.total (X := B) (Y := J))
  have hf : f ≫ s = 𝟙 (F.obj (B ⊞ J)) := by
    change F.map biprod.fst ≫ F.map biprod.inl = 𝟙 _
    have hz' : F.map (biprod.snd ≫ biprod.inr : B ⊞ J ⟶ B ⊞ J) = 0 := by
      rw [F.map_comp]
      exact hz
    simp only [F.map_add, F.map_id, hz', add_zero] at ht
    rw [← F.map_comp]
    exact ht
  exact ⟨⟨s, hf, hs⟩⟩

end DerivedCategory.Plus

open CategoryTheory CategoryTheory.Limits


namespace DerivedCategory.Plus

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  (X Y : DerivedCategory.Plus C) (a : ℤ)

/-- Degree bounds are retained by the original binary biproduct. -/
private theorem biprod_isGE [X.IsGE a] [Y.IsGE a] : (X ⊞ Y).IsGE a := by
  rw [← DerivedCategory.Plus.isGE_ι_obj_iff]
  apply (DerivedCategory.isGE_iff _ a).2
  intro n hn
  let F := DerivedCategory.Plus.homologyFunctor C n
  change IsZero (F.obj (X ⊞ Y))
  have : PreservesBinaryBiproduct X Y F :=
    preservesBinaryBiproduct_of_preservesBiproduct _ _ _
  have hX : IsZero (F.obj X) :=
    DerivedCategory.Plus.isZero_homology_of_isGE X a n hn
  have hY : IsZero (F.obj Y) :=
    DerivedCategory.Plus.isZero_homology_of_isGE Y a n hn
  have hZ : IsZero (F.obj X ⊞ F.obj Y) :=
    (biprod_isZero_iff _ _).2 ⟨hX, hY⟩
  exact hZ.of_iso (F.mapBiprod X Y)

/-- The upper degree bound of the original binary biproduct. -/
private theorem biprod_isLE [X.IsLE a] [Y.IsLE a] : (X ⊞ Y).IsLE a := by
  rw [← DerivedCategory.Plus.isLE_ι_obj_iff]
  apply (DerivedCategory.isLE_iff _ a).2
  intro n hn
  let F := DerivedCategory.Plus.homologyFunctor C n
  change IsZero (F.obj (X ⊞ Y))
  have : PreservesBinaryBiproduct X Y F :=
    preservesBinaryBiproduct_of_preservesBiproduct _ _ _
  have hX : IsZero (F.obj X) :=
    DerivedCategory.Plus.isZero_homology_of_isLE X a n hn
  have hY : IsZero (F.obj Y) :=
    DerivedCategory.Plus.isZero_homology_of_isLE Y a n hn
  have hZ : IsZero (F.obj X ⊞ F.obj Y) :=
    (biprod_isZero_iff _ _).2 ⟨hX, hY⟩
  exact hZ.of_iso (F.mapBiprod X Y)

end DerivedCategory.Plus

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated


namespace DerivedCategory.Plus

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  (T : Triangle (DerivedCategory.Plus C))

/-- The fibre of a map from a nonnegative object to a degree-at-least-one
object is nonnegative. This uses the same distinguished fibre triangle. -/
private theorem fiber_isGE_zero (hT : T ∈ distTriang _) [T.obj₂.IsGE 0] [T.obj₃.IsGE 1] :
    T.obj₁.IsGE 0 := by
  let U := T.invRotate
  have hU : U ∈ distTriang _ := inv_rot_of_distTriang T hT
  have h1 : U.obj₁.IsGE 0 := by
    have h2 : (T.obj₃⟦(-1 : ℤ)⟧).IsGE 2 :=
      DerivedCategory.Plus.TStructure.t.isGE_shift T.obj₃ 1 (-1) 2 (by omega)
    have : U.obj₁.IsGE 2 := h2
    exact DerivedCategory.Plus.TStructure.t.isGE_of_ge _ 0 2 (by omega)
  have h3 : U.obj₃.IsGE 0 := by
    change T.obj₂.IsGE 0
    infer_instance
  exact DerivedCategory.Plus.TStructure.t.isGE₂ U hU 0 h1 h3

/-- Below the target's lower bound, the original fibre arrow is an iso
on homology; any further original projection which is an H⁰ iso stays so. -/
private theorem fiber_homologyZero_projection_isIso (hT : T ∈ distTriang _) [T.obj₃.IsGE 1]
    {B : DerivedCategory.Plus C} (p : T.obj₂ ⟶ B)
    [IsIso ((DerivedCategory.Plus.homologyFunctor C 0).map p)] :
    IsIso ((DerivedCategory.Plus.homologyFunctor C 0).map (T.mor₁ ≫ p)) := by
  have : IsIso ((DerivedCategory.Plus.homologyFunctor C 0).map T.mor₁) :=
    DerivedCategory.Plus.isIso_homology_mor₁_of_isGE T hT 1 0 (by omega)
  rw [Functor.map_comp]
  infer_instance

end DerivedCategory.Plus

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated


namespace DerivedCategory.Plus

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  (T : Triangle (DerivedCategory.Plus C)) (hT : T ∈ distTriang _)

/-- The one fibre triangle gives an original H¹ short exact row when the
target has zero H⁰ and the original H¹ matrix is epic. -/
private theorem fiber_homologyOne_shortExact
    (hzero : IsZero ((DerivedCategory.Plus.homologyFunctor C 0).obj T.obj₃))
    [Epi ((DerivedCategory.Plus.homologyFunctor C 1).map T.mor₂)] :
    (ShortComplex.mk
      ((DerivedCategory.Plus.homologyFunctor C 1).map T.mor₁)
      ((DerivedCategory.Plus.homologyFunctor C 1).map T.mor₂)
      (by rw [← Functor.map_comp, comp_distTriang_mor_zero₁₂ T hT,
        Functor.map_zero])).ShortExact := by
  have hExact :
      (ShortComplex.mk ((DerivedCategory.Plus.homologyFunctor C 1).map T.mor₁)
        ((DerivedCategory.Plus.homologyFunctor C 1).map T.mor₂)
        (by rw [← Functor.map_comp, comp_distTriang_mor_zero₁₂ T hT,
          Functor.map_zero])).Exact := by
    change (ShortComplex.mk _ _
      ((DerivedCategory.Plus.homologyFunctor C 0).homologySequence_comp T hT 1)).Exact
    exact (DerivedCategory.Plus.homologyFunctor C 0).homologySequence_exact₂ T hT 1
  have hMono : Mono ((DerivedCategory.Plus.homologyFunctor C 1).map T.mor₁) := by
    change Mono (((DerivedCategory.Plus.homologyFunctor C 0).shift (1 : ℤ)).map T.mor₁)
    apply ((DerivedCategory.Plus.homologyFunctor C 0).homologySequence_mono_shift_map_mor₁_iff
      T hT 0 1 (by omega)).mpr
    exact hzero.eq_of_src _ _
  exact { exact := hExact, mono_f := hMono, epi_g := inferInstance }

end DerivedCategory.Plus

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated


namespace DerivedCategory.Plus

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  (T : Triangle (DerivedCategory.Plus C))
  [T.obj₂.IsLE 1] [T.obj₃.IsLE 1]
  [Epi ((DerivedCategory.Plus.homologyFunctor C 1).map T.mor₂)]

/-- The original fibre has no homology above one when its target is at most
one and the original degree-one map is epic. -/
private theorem fiber_homology_high_isZero (hT : T ∈ distTriang _) (n : ℤ) (hn : 1 < n) :
    IsZero ((DerivedCategory.Plus.homologyFunctor C n).obj T.obj₁) := by
  let H := DerivedCategory.Plus.homologyFunctor C 0
  have hM : IsZero ((H.shift n).obj T.obj₂) :=
    DerivedCategory.Plus.isZero_homology_of_isLE T.obj₂ 1 n hn
  have hδ : H.homologySequenceδ T (n - 1) n (by omega) = 0 := by
    by_cases h2 : n = 2
    · subst n
      exact (H.homologySequence_epi_shift_map_mor₂_iff T hT 1 2 (by omega)).mp
        (inferInstanceAs (Epi ((DerivedCategory.Plus.homologyFunctor C 1).map T.mor₂)))
    · have hp : IsZero ((H.shift (n - 1)).obj T.obj₃) :=
        DerivedCategory.Plus.isZero_homology_of_isLE T.obj₃ 1 (n - 1) (by omega)
      exact hp.eq_of_src _ _
  have hEx := H.homologySequence_exact₁ T hT (n - 1) n (by omega)
  have hK : IsZero ((H.shift n).obj T.obj₁) :=
    hEx.isZero_X₂ hδ (hM.eq_of_tgt _ _)
  exact hK

/-- The same original fibre is bounded above by degree one. -/
private theorem fiber_isLE_one (hT : T ∈ distTriang _) : T.obj₁.IsLE 1 := by
  rw [← DerivedCategory.Plus.isLE_ι_obj_iff]
  apply (DerivedCategory.isLE_iff
    ((DerivedCategory.Plus.ι (C := C)).obj T.obj₁) 1).2
  intro n hn
  exact fiber_homology_high_isZero T hT n hn

end DerivedCategory.Plus

/- B0Matrix -/
open CategoryTheory CategoryTheory.Limits


namespace DerivedCategory.Plus

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  (B : DerivedCategory.Plus C) (J : C)
  (i : J ⟶ (DerivedCategory.Plus.homologyFunctor C 1).obj B)
  (r : B ⟶ (DerivedCategory.Plus.singleFunctor C 1).obj
    ((DerivedCategory.Plus.homologyFunctor C 1).obj B))

local instance (B : DerivedCategory.Plus C) (J : C) :
    PreservesBinaryBiproduct B ((DerivedCategory.Plus.singleFunctor C 1).obj J)
      (DerivedCategory.Plus.homologyFunctor C 1) :=
  preservesBinaryBiproduct_of_preservesBiproduct _ _ _

/-- The actual top projection and original single map give the heart matrix
`[id,-i]` under only the chosen H¹ normalization. -/
private theorem B0_homologyOne_matrix
    (hr : (DerivedCategory.Plus.homologyFunctor C 1).map r ≫
      (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso (C := C) 1).hom.app
        ((DerivedCategory.Plus.homologyFunctor C 1).obj B) = 𝟙 _) :
    let H1 := DerivedCategory.Plus.homologyFunctor C 1
    let S := DerivedCategory.Plus.singleFunctor C 1
    let J1 := S.obj J
    let eP := (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso (C := C) 1).app (H1.obj B)
    let eJ := (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso (C := C) 1).app J
    let eM := H1.mapBiprod B J1 ≪≫ biprod.mapIso (Iso.refl (H1.obj B)) eJ
    eM.inv ≫ H1.map (biprod.desc r (-(S.map i))) ≫ eP.hom =
      biprod.desc (𝟙 (H1.obj B)) (-i) := by
  intro H1 S J1 eP eJ eM
  have hj := (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso (C := C) 1).hom.naturality i
  change H1.map (S.map i) ≫ eP.hom = eJ.hom ≫ i at hj
  have hr0 := hr
  change H1.map r ≫ eP.hom = 𝟙 (H1.obj B) at hr0
  have hr' : H1.map r ≫ eP.hom = (Iso.refl (H1.obj B)).hom ≫ 𝟙 _ := by
    simpa using hr0
  exact map_biprod_desc_matrix H1 (Iso.refl (H1.obj B)) eJ eP
    r (S.map i) (𝟙 (H1.obj B)) i hr' hj

/-- The original degree-one matrix is epic because its normalized first
component is the identity. -/
private theorem B0_homologyOne_map_epi
    (hr : (DerivedCategory.Plus.homologyFunctor C 1).map r ≫
      (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso (C := C) 1).hom.app
        ((DerivedCategory.Plus.homologyFunctor C 1).obj B) = 𝟙 _) :
    Epi ((DerivedCategory.Plus.homologyFunctor C 1).map
      (biprod.desc r
        (-((DerivedCategory.Plus.singleFunctor C 1).map i)))) := by
  let H1 := DerivedCategory.Plus.homologyFunctor C 1
  let S := DerivedCategory.Plus.singleFunctor C 1
  let eP := (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso (C := C) 1).app (H1.obj B)
  let eJ := (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso (C := C) 1).app J
  have hj := (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso (C := C) 1).hom.naturality i
  change H1.map (S.map i) ≫ eP.hom = eJ.hom ≫ i at hj
  have hr0 := hr
  change H1.map r ≫ eP.hom = 𝟙 (H1.obj B) at hr0
  have hr' : H1.map r ≫ eP.hom = (Iso.refl (H1.obj B)).hom ≫ 𝟙 _ := by
    simpa using hr0
  exact map_biprod_desc_epi_of_iso H1 (Iso.refl (H1.obj B)) eJ eP
    r (S.map i) (𝟙 (H1.obj B)) i hr' hj

end DerivedCategory.Plus

/- B0Fiber -/
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated


namespace DerivedCategory.Plus

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  (B : DerivedCategory.Plus C) (J : C)
  (i : J ⟶ (DerivedCategory.Plus.homologyFunctor C 1).obj B)
  (r : B ⟶ (DerivedCategory.Plus.singleFunctor C 1).obj
    ((DerivedCategory.Plus.homologyFunctor C 1).obj B))

local instance (B : DerivedCategory.Plus C) (J : C) :
    PreservesBinaryBiproduct B ((DerivedCategory.Plus.singleFunctor C 1).obj J)
      (DerivedCategory.Plus.homologyFunctor C 1) :=
  preservesBinaryBiproduct_of_preservesBiproduct _ _ _

/-- The actual H¹ map in the supplied original fibre triangle is epic. -/
private theorem B0_fibre_homologyOne_epi
    (hr : (DerivedCategory.Plus.homologyFunctor C 1).map r ≫
      (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso (C := C) 1).hom.app
        ((DerivedCategory.Plus.homologyFunctor C 1).obj B) = 𝟙 _)
    (T : Triangle (DerivedCategory.Plus C))
    (u₂ : T.obj₂ ≅ B ⊞ (DerivedCategory.Plus.singleFunctor C 1).obj J)
    (u₃ : T.obj₃ ≅ (DerivedCategory.Plus.singleFunctor C 1).obj
      ((DerivedCategory.Plus.homologyFunctor C 1).obj B))
    (hmap : u₂.inv ≫ T.mor₂ ≫ u₃.hom =
      biprod.desc r (-((DerivedCategory.Plus.singleFunctor C 1).map i))) :
    Epi ((DerivedCategory.Plus.homologyFunctor C 1).map T.mor₂) := by
  let H1 := DerivedCategory.Plus.homologyFunctor C 1
  let g := biprod.desc r (-((DerivedCategory.Plus.singleFunctor C 1).map i))
  have hbase : Epi (H1.map g) := B0_homologyOne_map_epi B J i r hr
  have hmapH := congrArg H1.map hmap
  simp only [Functor.map_comp] at hmapH
  have hEpiComp : Epi (H1.map u₂.inv ≫ H1.map T.mor₂ ≫ H1.map u₃.hom) := by
    rw [hmapH]
    exact hbase
  have hEpiLeft : Epi (H1.map u₂.inv ≫ H1.map T.mor₂) :=
    (epi_comp_iff_of_isIso _ (H1.map u₃.hom)).mp
      (by simpa only [Category.assoc] using hEpiComp)
  exact (epi_comp_iff_of_epi (H1.map u₂.inv) (H1.map T.mor₂)).mp hEpiLeft

/-- A single chosen fibre triangle of the original map has its actual H¹
graph projection identified with `J`, and the B projection composes with
the original inclusion `i`. -/
private theorem B0_fibre_homologyOne_graph
    (hr : (DerivedCategory.Plus.homologyFunctor C 1).map r ≫
      (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso (C := C) 1).hom.app
        ((DerivedCategory.Plus.homologyFunctor C 1).obj B) = 𝟙 _)
    (T : Triangle (DerivedCategory.Plus C)) (hT : T ∈ distTriang _)
    (u₂ : T.obj₂ ≅ B ⊞ (DerivedCategory.Plus.singleFunctor C 1).obj J)
    (u₃ : T.obj₃ ≅ (DerivedCategory.Plus.singleFunctor C 1).obj
      ((DerivedCategory.Plus.homologyFunctor C 1).obj B))
    (hmap : u₂.inv ≫ T.mor₂ ≫ u₃.hom =
      biprod.desc r (-((DerivedCategory.Plus.singleFunctor C 1).map i))) :
    let H1 := DerivedCategory.Plus.homologyFunctor C 1
    let eJ := (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso (C := C) 1).app J
    let m := H1.mapIso u₂ ≪≫
      H1.mapBiprod B ((DerivedCategory.Plus.singleFunctor C 1).obj J) ≪≫
      biprod.mapIso (Iso.refl (H1.obj B)) eJ
    IsIso (H1.map T.mor₁ ≫ m.hom ≫ biprod.snd) ∧
      H1.map T.mor₁ ≫ m.hom ≫ biprod.fst =
        H1.map T.mor₁ ≫ m.hom ≫ biprod.snd ≫ i := by
  intro H1 eJ m
  let S := DerivedCategory.Plus.singleFunctor C 1
  let P := S.obj (H1.obj B)
  let J1 := S.obj J
  let eP := (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso (C := C) 1).app (H1.obj B)
  let eM := H1.mapBiprod B J1 ≪≫ biprod.mapIso (Iso.refl (H1.obj B)) eJ
  let t := H1.mapIso u₃ ≪≫ eP
  let g := biprod.desc r (-(S.map i))
  have hEpi : Epi (H1.map T.mor₂) :=
    B0_fibre_homologyOne_epi B J i r hr T u₂ u₃ hmap
  have : Epi (H1.map T.mor₂) := hEpi
  have hzeroP : IsZero ((DerivedCategory.Plus.homologyFunctor C 0).obj P) :=
    DerivedCategory.Plus.isZero_homology_of_isGE P 1 0 (by omega)
  have hzero : IsZero ((DerivedCategory.Plus.homologyFunctor C 0).obj T.obj₃) :=
    hzeroP.of_iso ((DerivedCategory.Plus.homologyFunctor C 0).mapIso u₃)
  let Q := ShortComplex.mk (H1.map T.mor₁) (H1.map T.mor₂)
    (by rw [← Functor.map_comp, comp_distTriang_mor_zero₁₂ T hT, Functor.map_zero])
  have hQ : Q.ShortExact := fiber_homologyOne_shortExact T hT hzero
  have hmatrix : m.inv ≫ Q.g ≫ t.hom =
      biprod.desc (𝟙 (H1.obj B)) (-i) := by
    change (H1.mapIso u₂ ≪≫ eM).inv ≫ H1.map T.mor₂ ≫
      (H1.mapIso u₃ ≪≫ eP).hom = _
    simp only [Iso.trans_inv, Iso.trans_hom, Functor.mapIso_inv, Functor.mapIso_hom]
    simp only [Category.assoc]
    calc
      eM.inv ≫ H1.map u₂.inv ≫ H1.map T.mor₂ ≫ H1.map u₃.hom ≫ eP.hom =
          eM.inv ≫ H1.map (u₂.inv ≫ T.mor₂ ≫ u₃.hom) ≫ eP.hom := by
            simp only [Functor.map_comp, Category.assoc]
      _ = eM.inv ≫ H1.map g ≫ eP.hom := by rw [hmap]
      _ = biprod.desc (𝟙 (H1.obj B)) (-i) := B0_homologyOne_matrix B J i r hr
  have hgraph := graphShortExact_transport (Iso.refl (H1.obj B)) i hQ m t hmatrix
  refine ⟨hgraph.1, ?_⟩
  convert hgraph.2 using 1 <;> simp only [Q, Iso.refl_hom, Category.comp_id] <;> rfl

/-- The graph coordinates above are the literal original H¹ maps on the
two biproduct projections, with only the original single/homology iso on J. -/
private theorem B0_fibre_homologyOne_projections
    (hr : (DerivedCategory.Plus.homologyFunctor C 1).map r ≫
      (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso (C := C) 1).hom.app
        ((DerivedCategory.Plus.homologyFunctor C 1).obj B) = 𝟙 _)
    (T : Triangle (DerivedCategory.Plus C)) (hT : T ∈ distTriang _)
    (u₂ : T.obj₂ ≅ B ⊞ (DerivedCategory.Plus.singleFunctor C 1).obj J)
    (u₃ : T.obj₃ ≅ (DerivedCategory.Plus.singleFunctor C 1).obj
      ((DerivedCategory.Plus.homologyFunctor C 1).obj B))
    (hmap : u₂.inv ≫ T.mor₂ ≫ u₃.hom =
      biprod.desc r (-((DerivedCategory.Plus.singleFunctor C 1).map i))) :
    let H1 := DerivedCategory.Plus.homologyFunctor C 1
    let J1 := (DerivedCategory.Plus.singleFunctor C 1).obj J
    let eJ := (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso (C := C) 1).app J
    IsIso (H1.map (T.mor₁ ≫ u₂.hom ≫ (biprod.snd : B ⊞ J1 ⟶ J1)) ≫ eJ.hom) ∧
      H1.map (T.mor₁ ≫ u₂.hom ≫ (biprod.fst : B ⊞ J1 ⟶ B)) =
        H1.map (T.mor₁ ≫ u₂.hom ≫ (biprod.snd : B ⊞ J1 ⟶ J1)) ≫ eJ.hom ≫ i := by
  intro H1 J1 eJ
  have hgraph := B0_fibre_homologyOne_graph B J i r hr T hT u₂ u₃ hmap
  let eM := H1.mapBiprod B J1 ≪≫ biprod.mapIso (Iso.refl (H1.obj B)) eJ
  have hfst : eM.hom ≫ biprod.fst = H1.map (biprod.fst : B ⊞ J1 ⟶ B) := by
    simp only [eM, Iso.trans_hom, biprod.mapIso_hom, Category.assoc,
      biprod.map_fst, Iso.refl_hom, Category.comp_id,
      Functor.mapBiprod_hom, biprod.lift_fst]
  have hsnd : eM.hom ≫ biprod.snd = H1.map (biprod.snd : B ⊞ J1 ⟶ J1) ≫ eJ.hom := by
    simp only [eM, Iso.trans_hom, biprod.mapIso_hom, Category.assoc,
      biprod.map_snd, Functor.mapBiprod_hom]
    rw [← Category.assoc, biprod.lift_snd]
  change IsIso (H1.map T.mor₁ ≫ (H1.mapIso u₂ ≪≫ eM).hom ≫ biprod.snd) ∧
    H1.map T.mor₁ ≫ (H1.mapIso u₂ ≪≫ eM).hom ≫ biprod.fst =
      H1.map T.mor₁ ≫ (H1.mapIso u₂ ≪≫ eM).hom ≫ biprod.snd ≫ i at hgraph
  simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc, hfst, hsnd] at hgraph
  simp only [← Category.assoc, hsnd] at hgraph
  simpa only [Functor.map_comp, Category.assoc] using hgraph

/-- The same supplied fibre has the original degree-zero homology and is
bounded in degrees zero and one. Its only degree-one premise is the already
verified original top-projection normalization. -/
private theorem B0_fibre_bounds_and_homologyZero [B.IsGE 0] [B.IsLE 1]
    (hr : (DerivedCategory.Plus.homologyFunctor C 1).map r ≫
      (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso (C := C) 1).hom.app
        ((DerivedCategory.Plus.homologyFunctor C 1).obj B) = 𝟙 _)
    (T : Triangle (DerivedCategory.Plus C)) (hT : T ∈ distTriang _)
    (u₂ : T.obj₂ ≅ B ⊞ (DerivedCategory.Plus.singleFunctor C 1).obj J)
    (u₃ : T.obj₃ ≅ (DerivedCategory.Plus.singleFunctor C 1).obj
      ((DerivedCategory.Plus.homologyFunctor C 1).obj B))
    (hmap : u₂.inv ≫ T.mor₂ ≫ u₃.hom =
      biprod.desc r (-((DerivedCategory.Plus.singleFunctor C 1).map i))) :
    T.obj₁.IsGE 0 ∧ T.obj₁.IsLE 1 ∧
      IsIso ((DerivedCategory.Plus.homologyFunctor C 0).map
        (T.mor₁ ≫ u₂.hom ≫ (biprod.fst :
          B ⊞ (DerivedCategory.Plus.singleFunctor C 1).obj J ⟶ B))) := by
  let S := DerivedCategory.Plus.singleFunctor C 1
  let J1 := S.obj J
  let P := S.obj ((DerivedCategory.Plus.homologyFunctor C 1).obj B)
  let H0 := DerivedCategory.Plus.homologyFunctor C 0
  have hJge0 : J1.IsGE 0 :=
    DerivedCategory.Plus.TStructure.t.isGE_of_ge J1 0 1 (by omega)
  have : J1.IsGE 0 := hJge0
  have hbipGE : (B ⊞ J1).IsGE 0 := biprod_isGE B J1 0
  have : T.obj₂.IsGE 0 :=
    DerivedCategory.Plus.TStructure.t.isGE_of_iso u₂.symm 0
  have hPge1 : P.IsGE 1 := inferInstance
  have : T.obj₃.IsGE 1 :=
    DerivedCategory.Plus.TStructure.t.isGE_of_iso u₃.symm 1
  have hGE : T.obj₁.IsGE 0 := fiber_isGE_zero T hT
  have hbipLE : (B ⊞ J1).IsLE 1 := biprod_isLE B J1 1
  have : T.obj₂.IsLE 1 :=
    DerivedCategory.Plus.TStructure.t.isLE_of_iso u₂.symm 1
  have : T.obj₃.IsLE 1 :=
    DerivedCategory.Plus.TStructure.t.isLE_of_iso u₃.symm 1
  have hEpi : Epi ((DerivedCategory.Plus.homologyFunctor C 1).map T.mor₂) :=
    B0_fibre_homologyOne_epi B J i r hr T u₂ u₃ hmap
  have : Epi ((DerivedCategory.Plus.homologyFunctor C 1).map T.mor₂) := hEpi
  have hLE : T.obj₁.IsLE 1 := fiber_isLE_one T hT
  have hJ0 : IsZero (H0.obj J1) :=
    DerivedCategory.Plus.isZero_homology_of_isGE J1 1 0 (by omega)
  have hfst : IsIso (H0.map (biprod.fst : B ⊞ J1 ⟶ B)) :=
    map_biprod_fst_isIso_of_isZero H0 B J1 hJ0
  have hp : IsIso (H0.map (u₂.hom ≫ (biprod.fst : B ⊞ J1 ⟶ B))) := by
    rw [Functor.map_comp]
    infer_instance
  have : IsIso (H0.map (u₂.hom ≫ (biprod.fst : B ⊞ J1 ⟶ B))) := hp
  exact ⟨hGE, hLE, fiber_homologyZero_projection_isIso T hT _⟩

/-- One original distinguished triangle for the top-homology restriction.
All three maps in the conclusions are the maps of this same triangle. -/
theorem postnikovFibreHomology [B.IsGE 0] [B.IsLE 1]
    (hr : (DerivedCategory.Plus.homologyFunctor C 1).map r ≫
      (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso (C := C) 1).hom.app
        ((DerivedCategory.Plus.homologyFunctor C 1).obj B) = 𝟙 _)
    {K : DerivedCategory.Plus C}
    (a : K ⟶ B ⊞ (DerivedCategory.Plus.singleFunctor C 1).obj J)
    (δ : (DerivedCategory.Plus.singleFunctor C 1).obj
      ((DerivedCategory.Plus.homologyFunctor C 1).obj B) ⟶ K⟦(1 : ℤ)⟧)
    (hT : Triangle.mk a
      (biprod.desc r (-((DerivedCategory.Plus.singleFunctor C 1).map i))) δ ∈ distTriang _) :
    let H0 := DerivedCategory.Plus.homologyFunctor C 0
    let H1 := DerivedCategory.Plus.homologyFunctor C 1
    let J1 := (DerivedCategory.Plus.singleFunctor C 1).obj J
    let eJ := (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso (C := C) 1).app J
    K.IsGE 0 ∧ K.IsLE 1 ∧
      IsIso (H0.map (a ≫ (biprod.fst : B ⊞ J1 ⟶ B))) ∧
      IsIso (H1.map (a ≫ (biprod.snd : B ⊞ J1 ⟶ J1)) ≫ eJ.hom) ∧
      H1.map (a ≫ (biprod.fst : B ⊞ J1 ⟶ B)) =
        H1.map (a ≫ (biprod.snd : B ⊞ J1 ⟶ J1)) ≫ eJ.hom ≫ i := by
  intro H0 H1 J1 eJ
  let T : Triangle (DerivedCategory.Plus C) :=
    Triangle.mk a (biprod.desc r (-((DerivedCategory.Plus.singleFunctor C 1).map i))) δ
  have hmap : (Iso.refl _).inv ≫ T.mor₂ ≫ (Iso.refl _).hom =
      biprod.desc r (-((DerivedCategory.Plus.singleFunctor C 1).map i)) := by
    simp [T]
  have hbounds := B0_fibre_bounds_and_homologyZero B J i r hr T hT
    (Iso.refl _) (Iso.refl _) hmap
  have hproj := B0_fibre_homologyOne_projections B J i r hr T hT
    (Iso.refl _) (Iso.refl _) hmap
  rcases hbounds with ⟨hGE, hLE, hH0⟩
  rcases hproj with ⟨hH1, hformula⟩
  have hH0' : IsIso (H0.map (a ≫ (biprod.fst : B ⊞ J1 ⟶ B))) := by
    simpa only [T, Triangle.mk_mor₁, Iso.refl_hom, ← Category.assoc, Category.comp_id] using hH0
  have hH1' : IsIso (H1.map (a ≫ (biprod.snd : B ⊞ J1 ⟶ J1)) ≫ eJ.hom) := by
    simpa only [T, Triangle.mk_mor₁, Iso.refl_hom, ← Category.assoc, Category.comp_id] using hH1
  have hf' : H1.map (a ≫ (biprod.fst : B ⊞ J1 ⟶ B)) =
      H1.map (a ≫ (biprod.snd : B ⊞ J1 ⟶ J1)) ≫ eJ.hom ≫ i := by
    simpa only [T, Triangle.mk_mor₁, Iso.refl_hom, ← Category.assoc,
      Category.comp_id] using hformula
  exact ⟨hGE, hLE, hH0', hH1', hf'⟩

end DerivedCategory.Plus

namespace DerivedCategory.Plus

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- Restrict degree one of the original nonnegative object to the specified
map, using one fibre of the actual upper truncation. -/
theorem exists_postnikovRestriction (K : Plus C) [K.IsGE 0]
    {J : C} (i : J ⟶ (homologyFunctor C 1).obj K) :
    ∃ (B₀ : Plus C) (b : B₀ ⟶ K) (e : (homologyFunctor C 1).obj B₀ ≅ J),
      B₀.IsGE 0 ∧ B₀.IsLE 1 ∧ IsIso ((homologyFunctor C 0).map b) ∧
        (homologyFunctor C 1).map b = e.hom ≫ i ∧
        ∀ {W : C} (x : (singleFunctor C 1).obj W ⟶ K) (j : W ⟶ J),
          (homologyFunctor C 1).map x =
            (singleFunctorCompHomologyFunctorIso (C := C) 1).hom.app W ≫ j ≫ i →
          ∃ x₀ : (singleFunctor C 1).obj W ⟶ B₀,
            x₀ ≫ b = x ∧ (homologyFunctor C 1).map x₀ ≫ e.hom =
              (singleFunctorCompHomologyFunctorIso (C := C) 1).hom.app W ≫ j := by
  let t := TStructure.t (C := C)
  let B := (t.truncLT 2).obj K
  let k := (t.truncLTι 2).app K
  let T := (t.triangleLTGE 2).obj K
  let H₀ := homologyFunctor C 0
  let H₁ := homologyFunctor C 1
  let eB := homologyTruncLTIso K 2 1 (by omega)
  let a := i ≫ eB.inv
  let : B.IsLE 1 := t.isLE_truncLT_obj K 2 1
  let : T.obj₂.IsGE 0 := by change K.IsGE 0; infer_instance
  let : T.obj₃.IsGE 1 := t.isGE_truncGE_obj K 2 1
  let : B.IsGE 0 := fiber_isGE_zero T (t.triangleLTGE_distinguished 2 K)
  let r := upperHomologyProjection B 1
  let F := singleFunctor C 1
  let J1 := F.obj J
  let s := biprod.desc r (-(F.map a))
  obtain ⟨B₀, u, δ, hT⟩ := distinguished_cocone_triangle₁ s
  have hr := upperHomologyProjection_homology B 1
  obtain ⟨hge, hle, h0, h1, he⟩ := postnikovFibreHomology B J a r hr u δ hT
  let x : B₀ ⟶ B := u ≫ (biprod.fst : B ⊞ J1 ⟶ B)
  let y : B₀ ⟶ J1 := u ≫ (biprod.snd : B ⊞ J1 ⟶ J1)
  let E := (singleFunctorCompHomologyFunctorIso (C := C) 1).app J
  let e := @asIso _ _ _ _ (H₁.map y ≫ E.hom) h1
  have : IsIso (H₀.map x) := h0
  have : IsIso (H₀.map k) := isIso_homology_truncLTι K 2 0 (by omega)
  have h₀ : IsIso (H₀.map (x ≫ k)) := by rw [H₀.map_comp]; infer_instance
  have hk : H₁.map k = eB.hom := (homologyTruncLTIso_hom K 2 1 (by omega)).symm
  have hx : H₁.map x = e.hom ≫ a := by
    change H₁.map x = (H₁.map y ≫ E.hom) ≫ a
    rw [Category.assoc]
    exact he
  have hproj : H₁.map (x ≫ k) = e.hom ≫ i := by
    rw [H₁.map_comp, hx, hk, Category.assoc]
    dsimp only [a]
    rw [Category.assoc, eB.inv_hom_id, Category.comp_id]
  refine ⟨B₀, x ≫ k, e, hge, hle, h₀, hproj, ?_⟩
  intro W x₀ j₀ hx₀
  let WX := F.obj W
  let EW := (singleFunctorCompHomologyFunctorIso (C := C) 1).app W
  let EH := (singleFunctorCompHomologyFunctorIso (C := C) 1).app (H₁.obj B)
  let TR := (t.triangleLTGE 2).obj K
  have hWX : WX.IsLE 1 := inferInstance
  have hGE : TR.obj₃.IsGE 2 := t.isGE_truncGE_obj K 2 2
  have hvan : x₀ ≫ TR.mor₂ = 0 :=
    t.zero_of_isLE_of_isGE _ 1 2 (by omega) hWX hGE
  obtain ⟨x₁', hx₁⟩ := TR.coyoneda_exact₂ (t.triangleLTGE_distinguished 2 K) x₀ hvan
  let x₁ : F.obj W ⟶ B := x₁'
  have hx₁' : x₁ ≫ k = x₀ := hx₁.symm
  have hH : H₁.map x₁ = EW.hom ≫ j₀ ≫ a := by
    apply (cancel_mono eB.hom).mp
    calc
      H₁.map x₁ ≫ eB.hom = H₁.map (x₁ ≫ k) :=
        (congrArg (fun f => H₁.map x₁ ≫ f) hk.symm).trans (H₁.map_comp x₁ k).symm
      _ = H₁.map x₀ := congrArg H₁.map hx₁'
      _ = EW.hom ≫ j₀ ≫ i := hx₀
      _ = (EW.hom ≫ j₀ ≫ a) ≫ eB.hom := by
        dsimp only [a]
        simp only [Category.assoc, eB.inv_hom_id, Category.comp_id]
  have hρ : x₁ ≫ r = F.map j₀ ≫ F.map a := by
    apply (ι : Plus C ⥤ DerivedCategory C).map_injective
    apply DerivedCategory.homology_map_injective_of_isGE_of_isLE _ _ 1
    change H₁.map (x₁ ≫ r) = H₁.map (F.map j₀ ≫ F.map a)
    apply (cancel_mono EH.hom).mp
    have hr' : H₁.map r ≫ EH.hom = 𝟙 (H₁.obj B) := hr
    have hη : H₁.map (F.map (j₀ ≫ a)) ≫ EH.hom = EW.hom ≫ j₀ ≫ a :=
      (singleFunctorCompHomologyFunctorIso (C := C) 1).hom.naturality (j₀ ≫ a)
    rw [H₁.map_comp, Category.assoc, hr', Category.comp_id, hH,
      ← F.map_comp, hη]
  let TT := Triangle.mk u s δ
  let v := biprod.lift x₁ (F.map j₀)
  have hvs : v ≫ TT.mor₂ = 0 := by
    change biprod.lift x₁ (F.map j₀) ≫ biprod.desc r (-(F.map a)) = 0
    rw [biprod.lift_desc, Preadditive.comp_neg, hρ, add_neg_cancel]
  obtain ⟨w₀', hw₀⟩ := TT.coyoneda_exact₂ hT v hvs
  let w₀ : F.obj W ⟶ B₀ := w₀'
  have hw₀' : v = w₀ ≫ u := hw₀
  have hwfst : w₀ ≫ x = x₁ := by
    dsimp only [x]
    rw [← Category.assoc, ← hw₀']
    exact biprod.lift_fst x₁ (F.map j₀)
  have hwsnd : w₀ ≫ y = F.map j₀ := by
    dsimp only [y]
    rw [← Category.assoc, ← hw₀']
    exact biprod.lift_snd x₁ (F.map j₀)
  refine ⟨w₀, ?_, ?_⟩
  · rw [← Category.assoc, hwfst]
    exact hx₁'
  · change H₁.map w₀ ≫ H₁.map y ≫ E.hom = EW.hom ≫ j₀
    rw [← Category.assoc, ← H₁.map_comp, hwsnd]
    exact (singleFunctorCompHomologyFunctorIso (C := C) 1).hom.naturality j₀

end DerivedCategory.Plus

namespace DerivedCategory.Plus

universe uScalar vScalar wScalar

private theorem epi_nsmul_id_of_iso
    {D : Type*} [Category* D] [Preadditive D] {X Y : D} (e : X ≅ Y) (n : ℕ)
    [Epi (n • 𝟙 Y)] : Epi (n • 𝟙 X) := by
  have h : n • 𝟙 X = e.hom ≫ (n • 𝟙 Y) ≫ e.inv := by
    simp only [Preadditive.nsmul_comp, Preadditive.comp_nsmul, Category.id_comp,
      Iso.hom_inv_id]
  rw [h]
  infer_instance

variable {C : Type uScalar} [Category.{vScalar} C] [Abelian C] [HasDerivedCategory.{wScalar} C]

/-- The original scalar fibre of the given two-layer restriction compares
to the original scalar fibre, retaining the original inclusion and boundary. -/
theorem exists_postnikovMultiplicationFibre_comparison
    {K B₀ F : Plus C} [B₀.IsLE 1] {J : C}
    (b : B₀ ⟶ K) (e : (homologyFunctor C 1).obj B₀ ≅ J)
    (h₀ : IsIso ((homologyFunctor C 0).map b)) (n : ℕ)
    [Epi (n • 𝟙 ((homologyFunctor C 0).obj K))] [Epi (n • 𝟙 J)]
    (i : F ⟶ K) (δ : K ⟶ F⟦(1 : ℤ)⟧)
    (hT : Triangle.mk i (n • 𝟙 K) δ ∈ distTriang (Plus C)) :
    ∃ (F₀ : Plus C) (i₀ : F₀ ⟶ B₀) (δ₀ : B₀ ⟶ F₀⟦(1 : ℤ)⟧)
      (a : F₀ ⟶ F) (e₀ : (homologyFunctor C 1).obj F₀ ≅ kernel (n • 𝟙 J)),
      F₀.IsLE 1 ∧ Triangle.mk i₀ (n • 𝟙 B₀) δ₀ ∈ distTriang (Plus C) ∧
      i₀ ≫ b = a ≫ i ∧ δ₀ ≫ a⟦(1 : ℤ)⟧' = b ≫ δ ∧
      e₀.hom ≫ kernel.ι (n • 𝟙 J) = (homologyFunctor C 1).map i₀ ≫ e.hom := by
  let H₀ := homologyFunctor C 0
  let H₁ := homologyFunctor C 1
  let eH₀ := @asIso _ _ _ _ (H₀.map b) h₀
  let : Epi (H₀.map (n • 𝟙 B₀)) := by
    rw [H₀.map_nsmul, H₀.map_id]
    exact epi_nsmul_id_of_iso eH₀ n
  have hH₁ : Epi (H₁.map (n • 𝟙 B₀)) := by
    rw [H₁.map_nsmul, H₁.map_id]
    exact epi_nsmul_id_of_iso e n
  obtain ⟨F₀, i₀, δ₀, hT₀⟩ := distinguished_cocone_triangle₁ (n • 𝟙 B₀)
  let T₀ := Triangle.mk i₀ (n • 𝟙 B₀) δ₀
  let T := Triangle.mk i (n • 𝟙 K) δ
  have hmid : T₀.mor₂ ≫ b = b ≫ T.mor₂ := by
    change (n • 𝟙 B₀) ≫ b = b ≫ (n • 𝟙 K)
    simp only [Preadditive.nsmul_comp, Preadditive.comp_nsmul, Category.id_comp, Category.comp_id]
  obtain ⟨a, ha, hδ⟩ := complete_distinguished_triangle_morphism₁ T₀ T hT₀ hT b b hmid
  let : T₀.obj₂.IsLE 1 := by change B₀.IsLE 1; infer_instance
  let : T₀.obj₃.IsLE 1 := by change B₀.IsLE 1; infer_instance
  let : Epi (H₁.map T₀.mor₂) := hH₁
  let e₀ := homologyOneMultiplicationKernelIso n i₀ δ₀ hT₀ e
  refine ⟨F₀, i₀, δ₀, a, e₀, fiber_isLE_one T₀ hT₀, hT₀, ha, hδ, ?_⟩
  exact homologyOneMultiplicationKernelIso_hom_ι n i₀ δ₀ hT₀ e

end DerivedCategory.Plus
