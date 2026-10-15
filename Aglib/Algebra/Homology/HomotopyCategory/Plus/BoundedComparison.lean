/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Triangulated.NatTransIso
public import Aglib.Algebra.Homology.Embedding.StupidTrunc.Layer
public import Mathlib.Algebra.Homology.HomotopyCategory.Plus
public import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
/-! # Original brutal-layer triangles in bounded-below homotopy categories -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CochainComplex
universe v u v' u'
namespace CochainComplex
variable {A : Type u} [Category.{v} A] [Abelian A]
attribute [local instance] Abelian.hasFiniteBiproducts

/-- The actual brutal truncation as a bounded-below complex. -/
def brutalPlus (K : CochainComplex A ℤ) (n : ℤ) : _root_.CochainComplex.Plus A :=
  ⟨stupidTruncGE K n, n, inferInstance⟩

/-- An original single term in its own degree as a bounded-below complex. -/
def singlePlus (M : A) (n : ℤ) : _root_.CochainComplex.Plus A :=
  ⟨(HomologicalComplex.single A (.up ℤ) n).obj M, n, inferInstance⟩

/-- The original degreewise split layer triangle, lifted to the bounded-below homotopy category. -/
def brutalLayerTriangle (K : CochainComplex A ℤ) (n : ℤ) :
    Triangle (HomotopyCategory.Plus A) where
  obj₁ := (HomotopyCategory.Plus.quotient A).obj (brutalPlus K (n + 1))
  obj₂ := (HomotopyCategory.Plus.quotient A).obj (brutalPlus K n)
  obj₃ := (HomotopyCategory.Plus.quotient A).obj (singlePlus (K.X n) n)
  mor₁ := (HomotopyCategory.Plus.quotient A).map
    (ObjectProperty.homMk (stupidTruncGETransition K (by omega : n ≤ n + 1)))
  mor₂ := (HomotopyCategory.Plus.quotient A).map
    (ObjectProperty.homMk (stupidTruncGELayerProjection K n))
  mor₃ := ObjectProperty.homMk
    ((_root_.CochainComplex.trianglehOfDegreewiseSplit (stupidTruncGELayerSequence K n)
      (stupidTruncGELayerSequenceSplitting K n)).mor₃ ≫
      ((HomotopyCategory.Plus.ι A).commShiftIso (1 : ℤ)).inv.app
        ((HomotopyCategory.Plus.quotient A).obj (brutalPlus K (n + 1))))

/-- The original brutal layer is distinguished in the actual bounded-below homotopy category. -/
theorem brutalLayerTriangle_distinguished (K : CochainComplex A ℤ) (n : ℤ) :
    brutalLayerTriangle K n ∈ distTriang (HomotopyCategory.Plus A) := by
  change (HomotopyCategory.Plus.ι A).mapTriangle.obj (brutalLayerTriangle K n) ∈
    distTriang (HomotopyCategory A (.up ℤ))
  convert _root_.CochainComplex.trianglehOfDegreewiseSplit_distinguished
    (stupidTruncGELayerSequence K n) (stupidTruncGELayerSequenceSplitting K n) using 1
  simp [brutalLayerTriangle, _root_.CochainComplex.trianglehOfDegreewiseSplit,
    _root_.CochainComplex.triangleOfDegreewiseSplit, Functor.mapTriangle,
    stupidTruncGELayerSequence, brutalPlus]
  congr 1
  dsimp [HomotopyCategory.Plus.quotient, ObjectProperty.lift]
  simp

/-- Above an upper term bound, the original brutal truncation is zero. -/
theorem brutalPlus_isZero (K : CochainComplex A ℤ) (b n : ℤ)
    (hK : ∀ i, b < i → IsZero (K.X i)) (hn : b < n) : IsZero (brutalPlus K n) := by
  rw [IsZero.iff_id_eq_zero]
  apply ObjectProperty.hom_ext
  ext i
  by_cases hi : n ≤ i
  · let : IsSplitMono ((stupidTruncGEInclusion K n).f i) :=
      stupidTruncGEInclusion_degreewiseSplitMono K n i
    exact (IsZero.of_mono ((stupidTruncGEInclusion K n).f i)
      (hK i (by omega))).eq_of_src _ _
  · exact (stupidTruncGE_isZero_X K n i (by omega)).eq_of_src _ _

variable {D : Type u'} [Category.{v'} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive] [Pretriangulated D]
  {F G : HomotopyCategory.Plus A ⥤ D} [F.CommShift ℤ] [G.CommShift ℤ]
  [F.IsTriangulated] [G.IsTriangulated]
  (τ : F ⟶ G) [τ.CommShift ℤ]

/-- The original adjacent brutal layer propagates invertibility of the given transformation. -/
theorem isIso_app_brutal_step (K : CochainComplex A ℤ) (n : ℤ)
    (hn : IsIso (τ.app ((HomotopyCategory.Plus.quotient A).obj (brutalPlus K (n + 1)))))
    (hs : IsIso (τ.app ((HomotopyCategory.Plus.quotient A).obj (singlePlus (K.X n) n)))) :
    IsIso (τ.app ((HomotopyCategory.Plus.quotient A).obj (brutalPlus K n))) :=
  τ.isIso_app_middle_of_distinguished (brutalLayerTriangle K n)
    (brutalLayerTriangle_distinguished K n) hn hs

/-- Finite downward induction through the original brutal layers. -/
theorem isIso_app_brutal_of_upper_bound (K : CochainComplex A ℤ) (b : ℤ)
    (hK : ∀ i, b < i → IsZero (K.X i))
    (hs : ∀ n, IsIso (τ.app ((HomotopyCategory.Plus.quotient A).obj
      (singlePlus (K.X n) n)))) (k : ℕ) :
    IsIso (τ.app ((HomotopyCategory.Plus.quotient A).obj
      (brutalPlus K (b + 1 - k)))) := by
  induction k with
  | zero =>
    have hz := (HomotopyCategory.Plus.quotient A).map_isZero
      (brutalPlus_isZero K b (b + 1) hK (by omega))
    convert (F.map_isZero hz).isIso (G.map_isZero hz) (τ.app _) using 1 <;>
      congr 3 <;> omega
  | succ k ih =>
    apply isIso_app_brutal_step τ K (b + 1 - (k + 1))
    · convert ih using 1 <;> congr 3 <;> omega
    · exact hs _

/-- The original natural transformation is invertible on a genuinely bounded complex if it is
invertible on each of its original single terms. -/
theorem isIso_app_of_term_bounds (K : _root_.CochainComplex.Plus A) (a b : ℤ)
    (hl : ∀ i, i < a → IsZero (K.obj.X i))
    (hu : ∀ i, b < i → IsZero (K.obj.X i))
    (hs : ∀ n, IsIso (τ.app ((HomotopyCategory.Plus.quotient A).obj
      (singlePlus (K.obj.X n) n)))) :
    IsIso (τ.app ((HomotopyCategory.Plus.quotient A).obj K)) := by
  let m := min a (b + 1)
  have hi : IsIso (stupidTruncGEInclusion K.obj m) := by
    have (i : ℤ) : IsIso ((stupidTruncGEInclusion K.obj m).f i) := by
      by_cases hmi : m ≤ i
      · rw [stupidTruncGEInclusion_f_of_le K.obj m i hmi]
        infer_instance
      · exact (stupidTruncGE_isZero_X K.obj m i (by omega)).isIso
          (hl i (by dsimp [m] at *; omega)) _
    exact HomologicalComplex.Hom.isIso_of_components _
  let e : brutalPlus K.obj m ≅ K :=
    (_root_.CochainComplex.plus A).isoMk (asIso (stupidTruncGEInclusion K.obj m))
  rw [← NatTrans.isIso_app_iff_of_iso τ ((HomotopyCategory.Plus.quotient A).mapIso e)]
  have hm : b + 1 - ((b + 1 - m).toNat : ℤ) = m := by
    rw [Int.toNat_of_nonneg (by dsimp [m]; omega)]
    omega
  have h := isIso_app_brutal_of_upper_bound τ K.obj b hu hs (b + 1 - m).toNat
  rwa [hm] at h

omit [Preadditive D] [HasZeroObject D] [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive]
  [Pretriangulated D] [F.IsTriangulated] [G.IsTriangulated] in
/-- Shift compatibility transports invertibility on a sheaf in degree zero to its original
single complex in every degree. -/
theorem isIso_app_single_of_zero (M : A)
    (h : IsIso (τ.app ((HomotopyCategory.Plus.quotient A).obj (singlePlus M 0))))
    (n : ℤ) : IsIso (τ.app ((HomotopyCategory.Plus.quotient A).obj (singlePlus M n))) := by
  let e := ((HomotopyCategory.Plus.singleFunctors A).shiftIso (-n) n 0 (by omega)).app M
  change IsIso (τ.app ((HomotopyCategory.Plus.singleFunctor A n).obj M))
  rw [← NatTrans.isIso_app_iff_of_iso τ e]
  dsimp only [Functor.comp_obj]
  rw [τ.app_shift]
  have : IsIso (τ.app ((HomotopyCategory.Plus.singleFunctor A 0).obj M)) := h
  infer_instance

end CochainComplex
