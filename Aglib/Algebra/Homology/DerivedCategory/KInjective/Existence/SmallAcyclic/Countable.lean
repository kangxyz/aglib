/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.KInjective.Existence.SmallAcyclic.AdjacentPair

/-!
# A small acyclic subcomplex by countable downward recursion

For an actual natural-number chain complex exact in positive degrees, a map
from a separator to degree one lies in an actual small acyclic subcomplex.
The initial degree-zero term is the image of the restricted differential,
and every successor is the compatible exactness step from `AdjacentPair`.
All terms have the single bound constructed in `CardinalLadder`.
-/

@[expose] public noncomputable section

universe w v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.IsGrothendieckAbelian

namespace ChainComplex.SmallAcyclicPair

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  {G : C} (hG : IsSeparator G) (K : ChainComplex C ℕ) (ψ : G ⟶ K.X 1)

/-- Start with the image of the given map and the image of its restricted differential. -/
def initial : SmallAcyclicPair K (smallAcyclicCardinalLadder hG 0) 0 where
  X₀ := image (image.ι ψ ≫ K.d 1 0)
  X₁ := image ψ
  d := factorThruImage (image.ι ψ ≫ K.d 1 0)
  f₀ := image.ι (image.ι ψ ≫ K.d 1 0)
  f₁ := image.ι ψ
  mono_f₀ := inferInstance
  mono_f₁ := inferInstance
  comm := image.fac _
  size := Subobject.hasCardinalLT_of_epi (hasCardinalLT_separator_ladder_zero hG)
    (factorThruImage ψ)

lemma initial_epi_d : Epi (initial hG K ψ).d :=
  inferInstanceAs (Epi (factorThruImage (image.ι ψ ≫ K.d 1 0)))

lemma initial_size_X₀ :
    HasCardinalLT (Subobject (initial hG K ψ).X₀) (smallAcyclicCardinalLadder hG 0) := by
  have := initial_epi_d hG K ψ
  exact Subobject.hasCardinalLT_of_epi (initial hG K ψ).size (initial hG K ψ).d

variable (hK : ∀ n : ℕ, K.ExactAt (n + 1))

/-- The actual compatible sequence of adjacent pairs, with its degreewise bounds. -/
def sequence : ∀ n : ℕ, SmallAcyclicPair K (smallAcyclicCardinalLadder hG n) n
  | 0 => initial hG K ψ
  | n + 1 => next hG (sequence n) (hK n)

/-- The small natural-number chain complex assembled from the compatible pairs. -/
def complex : ChainComplex C ℕ :=
  ChainComplex.of (fun n ↦ (sequence hG K ψ hK n).X₀)
    (fun n ↦ (sequence hG K ψ hK n).d)
    (fun n ↦ next_d_comp hG (sequence hG K ψ hK n) (hK n))

@[simp]
lemma complex_d (n : ℕ) :
    (complex hG K ψ hK).d (n + 1) n = (sequence hG K ψ hK n).d :=
  ChainComplex.of_d (fun j ↦ (sequence hG K ψ hK j).X₀)
    (fun j ↦ (sequence hG K ψ hK j).d) n

/-- The actual monic chain map into the ambient complex. -/
def inclusion : complex hG K ψ hK ⟶ K :=
  ChainComplex.ofHom (fun n ↦ (sequence hG K ψ hK n).f₀)
    (fun n ↦ by
      rw [complex_d]
      exact (sequence hG K ψ hK n).comm.symm)

instance inclusion_f_mono (n : ℕ) : Mono ((inclusion hG K ψ hK).f n) :=
  (sequence hG K ψ hK n).mono_f₀

lemma complex_acyclic : (complex hG K ψ hK).Acyclic := by
  intro n
  cases n with
  | zero =>
    apply ((complex hG K ψ hK).exactAt_iff' 1 0 0 (by simp) (by simp)).2
    have hz : (complex hG K ψ hK).d 0 0 = 0 :=
      (complex hG K ψ hK).shape 0 0 (by simp)
    apply (ShortComplex.exact_iff_epi _ hz).2
    change Epi ((complex hG K ψ hK).d 1 0)
    rw [complex_d]
    exact initial_epi_d hG K ψ
  | succ n =>
    apply ((complex hG K ψ hK).exactAt_iff' (n + 2) (n + 1) n
      (by simp) (by simp)).2
    let S : ShortComplex C :=
      ShortComplex.mk (next hG (sequence hG K ψ hK n) (hK n)).d
        (sequence hG K ψ hK n).d (next_d_comp hG _ _)
    let T : ShortComplex C := (complex hG K ψ hK).sc' (n + 2) (n + 1) n
    have e : S ≅ T := ShortComplex.isoMk (S₁ := S) (S₂ := T)
      (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by
        change 𝟙 _ ≫ (complex hG K ψ hK).d (n + 2) (n + 1) =
          (next hG (sequence hG K ψ hK n) (hK n)).d ≫ 𝟙 _
        simp only [Category.id_comp, Category.comp_id]
        change (complex hG K ψ hK).d (n + 1 + 1) (n + 1) =
          (sequence hG K ψ hK (n + 1)).d
        exact complex_d hG K ψ hK (n + 1))
      (by
        change 𝟙 _ ≫ (complex hG K ψ hK).d (n + 1) n =
          (sequence hG K ψ hK n).d ≫ 𝟙 _
        simpa only [Category.id_comp, Category.comp_id] using complex_d hG K ψ hK n)
    exact ShortComplex.exact_of_iso e (next_exact hG (sequence hG K ψ hK n) (hK n))

lemma complex_size (n : ℕ) :
    HasCardinalLT (Subobject ((complex hG K ψ hK).X n)) (smallAcyclicCardinal hG) := by
  cases n with
  | zero => exact (initial_size_X₀ hG K ψ).of_le (smallAcyclicCardinalLadder_lt hG 0).le
  | succ n =>
    exact (sequence hG K ψ hK n).size.of_le (smallAcyclicCardinalLadder_lt hG n).le

/-- The original separator map factors through degree one of the constructed complex. -/
def factor : G ⟶ (complex hG K ψ hK).X 1 := factorThruImage ψ

@[reassoc (attr := simp)]
lemma factor_inclusion : factor hG K ψ hK ≫ (inclusion hG K ψ hK).f 1 = ψ :=
  image.fac ψ

end ChainComplex.SmallAcyclicPair
