/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Limits.Types.FiniteSubset
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.RingTheory.FiniteType

/-!
# Finite-type generators captured at one filtered-colimit stage

A finitely generated algebra which is also a specified filtered colimit of
rings is generated, over its original coefficient ring, by one stage image.
The transition maps need not be surjective, and the coefficient-ring map need
not factor through a stage. A separate range criterion turns native
factorizations of both sets of generators into a surjectivity statement.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CommRingCat

universe u v

/-- One original stage image generates a finite-type colimit algebra over the
specified coefficient ring, without assumptions on transition maps. -/
theorem exists_adjoin_range_eq_top_of_isColimit
    {I : Type u} [Category.{u} I] [IsFiltered I]
    (D : I ⥤ CommRingCat.{u}) (c : Cocone D) (hc : IsColimit c)
    (R : Type v) [CommSemiring R] [Algebra R c.pt] [Algebra.FiniteType R c.pt] :
    ∃ i, Algebra.adjoin (A := c.pt) R (Set.range (c.ι.app i : D.obj i → c.pt)) = ⊤ := by
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := R) (A := c.pt)
  obtain ⟨i, hi⟩ := Types.exists_finset_subset_range_of_isColimit
    (D ⋙ forget CommRingCat) ((forget CommRingCat).mapCocone c)
    (isColimitOfPreserves (forget CommRingCat) hc) s
  refine ⟨i, top_unique ?_⟩
  rw [← hs]
  exact Algebra.adjoin_mono hi

end CommRingCat

namespace RingHom

universe uR uA uB uC

/-- If a map's range contains the coefficient ring and an algebra-generating
ring image, the original map is surjective. Both inclusions are specified by
literal factorization equations. -/
theorem surjective_of_adjoin_range_eq_top
    {R : Type uR} {A : Type uA} {B : Type uB} {C : Type uC}
    [CommSemiring R] [Semiring A] [Semiring B] [Semiring C] [Algebra R A]
    (q : C →+* A) (r : R →+* C) (s : B →+* C) (t : B →+* A)
    (hR : q.comp r = algebraMap R A) (hB : q.comp s = t)
    (hgen : Algebra.adjoin R (Set.range t) = ⊤) : Function.Surjective q := by
  let V : Subalgebra R A :=
    { q.rangeS with
      algebraMap_mem' := fun x ↦ ⟨r x, congrArg (fun f : R →+* A ↦ f x) hR⟩ }
  have htop : (⊤ : Subalgebra R A) ≤ V := by
    rw [← hgen]
    apply Algebra.adjoin_le
    rintro _ ⟨b, rfl⟩
    exact ⟨s b, congrArg (fun f : B →+* A ↦ f b) hB⟩
  intro a
  exact htop (Algebra.mem_top : a ∈ (⊤ : Subalgebra R A))

end RingHom
