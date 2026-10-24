/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.KInjective.Existence.Filtration.Successor

/-! # Strict acyclic growth in the native subobject lattice -/

@[expose] public noncomputable section

universe w v u

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  {G : C} (hG : IsSeparator G)

/-- A proper acyclic subobject admits a strictly larger acyclic subobject.
The quotient by the canonical native `Subobject.ofLE` map is isomorphic to
one member of the fixed small acyclic family. -/
lemma exists_small_acyclic_subobject_step (M : CochainComplex C ℤ) (hM : M.Acyclic)
    (A : Subobject M) (hA : (A : CochainComplex C ℤ).Acyclic) (hne : A ≠ ⊤) :
    ∃ (B : Subobject M) (hAB : A < B) (i : smallAcyclicFamilyIndex hG),
      (B : CochainComplex C ℤ).Acyclic ∧
      Nonempty (cokernel (Subobject.ofLE A B hAB.le) ≅ smallAcyclicFamily hG i) := by
  have ha : ¬ IsIso A.arrow := fun h ↦ hne ((Subobject.isIso_arrow_iff_eq_top A).1 h)
  obtain ⟨i, B, u, b, hu, hb, hub, hB, hnu, ⟨e⟩⟩ :=
    exists_small_acyclic_extension hG A.arrow hA hM ha
  have := hu
  have := hb
  have hAB : A < Subobject.mk b := by
    simpa only [Subobject.mk_arrow] using Subobject.mk_lt_mk_of_comm u hub hnu
  refine ⟨Subobject.mk b, hAB, i, ?_, ?_⟩
  · intro n
    exact (hB n).of_iso (Subobject.underlyingIso b).symm
  · refine ⟨(cokernel.mapIso (Subobject.ofLE A (Subobject.mk b) hAB.le) u
      (Iso.refl _) (Subobject.underlyingIso b) ?_) ≪≫ e⟩
    apply (cancel_mono b).1
    simp only [Category.assoc, Subobject.underlyingIso_hom_comp_eq_mk,
      Subobject.ofLE_arrow, Iso.refl_hom, Category.id_comp, hub]

end CochainComplex
