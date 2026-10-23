/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.DerivedExt
public import Mathlib.Algebra.Homology.ConcreteCategory

/-!
# Original cocycle representatives for derived sections

These lemmas compute native homology comparisons on the original cocycles.
-/

@[expose] public noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open CochainComplex CochainComplex.HomComplex

namespace CategoryTheory.Sheaf.ModuleCoefficients

/-- The identity forgetful functor on additive commutative groups. -/
local instance derivedCocyclesHasForget₂ : HasForget₂ AddCommGrpCat.{v} AddCommGrpCat.{v} where
  forget₂ := 𝟭 _

local instance : (forget₂ AddCommGrpCat.{v} AddCommGrpCat.{v}).Additive :=
  inferInstanceAs (Functor.Additive (𝟭 AddCommGrpCat.{v}))

local instance : (forget₂ AddCommGrpCat.{v} AddCommGrpCat.{v}).PreservesHomology :=
  inferInstanceAs (Functor.PreservesHomology (𝟭 AddCommGrpCat.{v}))

section Complex

variable {ι : Type*} {c : ComplexShape ι}
  {K L : HomologicalComplex AddCommGrpCat.{v} c} {i j : ι}

/-- Naturality of native cycles constructors. -/
lemma cyclesMk_map (f : K ⟶ L) (x : K.X i) (hj : c.next i = j)
    (hx : K.d i j x = 0) :
    HomologicalComplex.cyclesMap f i (K.cyclesMk x j hj hx) =
      L.cyclesMk (f.f i x) j hj (by
        change L.d i j (f.f i x) = 0
        calc
          L.d i j (f.f i x) = f.f j (K.d i j x) :=
            ConcreteCategory.congr_hom (f.comm i j) x
          _ = 0 := by rw [hx]; exact map_zero _) := by
  apply (AddCommGrpCat.mono_iff_injective (L.iCycles i)).mp inferInstance
  have h := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i f i) (K.cyclesMk x j hj hx)
  change L.iCycles i (HomologicalComplex.cyclesMap f i (K.cyclesMk x j hj hx)) =
    f.f i (K.iCycles i (K.cyclesMk x j hj hx)) at h
  have hK : K.iCycles i (K.cyclesMk x j hj hx) = x := K.i_cyclesMk _ _ _ _
  rw [hK] at h
  exact h.trans (L.i_cyclesMk _ _ _ _).symm

/-- A native homology map sends the class of a cycle to the class of its actual image. -/
lemma homologyMap_cyclesMk (f : K ⟶ L) (x : K.X i) (hj : c.next i = j)
    (hx : K.d i j x = 0) :
    HomologicalComplex.homologyMap f i (K.homologyπ i (K.cyclesMk x j hj hx)) =
      L.homologyπ i (L.cyclesMk (f.f i x) j hj (by
        change L.d i j (f.f i x) = 0
        calc
          L.d i j (f.f i x) = f.f j (K.d i j x) :=
            ConcreteCategory.congr_hom (f.comm i j) x
          _ = 0 := by rw [hx]; exact map_zero _)) := by
  have h := ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality f i)
    (K.cyclesMk x j hj hx)
  change HomologicalComplex.homologyMap f i (K.homologyπ i (K.cyclesMk x j hj hx)) =
    L.homologyπ i (HomologicalComplex.cyclesMap f i (K.cyclesMk x j hj hx)) at h
  rw [cyclesMk_map] at h
  exact h

end Complex

section HomComplex

variable {C : Type u} [Category.{v} C] [Abelian C]
  (K L : CochainComplex C ℤ) (n : ℤ)

/-- The original Hom-complex comparison sends the class of a cocycle to that cocycle class. -/
lemma homologyAddEquiv_cyclesMk (z : Cocycle K L n) :
    HomComplex.homologyAddEquiv K L n
      ((HomComplex K L).homologyπ n
        ((HomComplex K L).cyclesMk z.val (n + 1) (by simp) (by exact z.property))) =
      CohomologyClass.mk z := by
  let h := HomComplex.leftHomologyData K L n
  have hz : h.cyclesIso.hom
      ((HomComplex K L).cyclesMk z.val (n + 1) (by simp) (by exact z.property)) = z := by
    apply Subtype.ext
    have he := ConcreteCategory.congr_hom h.cyclesIso_hom_comp_i
      ((HomComplex K L).cyclesMk z.val (n + 1) (by simp) (by exact z.property))
    change (h.cyclesIso.hom
      ((HomComplex K L).cyclesMk z.val (n + 1) (by simp) z.property)).val =
      (HomComplex K L).iCycles n
        ((HomComplex K L).cyclesMk z.val (n + 1) (by simp) z.property) at he
    exact he.trans ((HomComplex K L).i_cyclesMk _ _ _ _)
  have he := ConcreteCategory.congr_hom h.homologyπ_comp_homologyIso_hom
    ((HomComplex K L).cyclesMk z.val (n + 1) (by simp) (by exact z.property))
  change h.homologyIso.hom _ = _
  change h.homologyIso.hom ((HomComplex K L).homologyπ n
    ((HomComplex K L).cyclesMk z.val (n + 1) (by simp) z.property)) =
      h.π (h.cyclesIso.hom
        ((HomComplex K L).cyclesMk z.val (n + 1) (by simp) z.property)) at he
  rw [hz] at he
  exact he

end HomComplex

end CategoryTheory.Sheaf.ModuleCoefficients
