/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.Epimorphisms
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Local boundaries detect exactness of the original module sheaves

The criterion applies to the actual differential maps. Every closed section
must become an actual boundary on a covering sieve. The proof makes the original
map to cycles locally surjective, hence epic. It does not identify evaluation
of sheaf homology with homology of sections, or assume sectionwise surjectivity
of arbitrary epimorphisms.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe c h r m

namespace SheafOfModules

variable {C : Type c} [Category.{h} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{r}} [HasSheafify J AddCommGrpCat.{m}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
  [J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{m})]

-- Use the original native module/underlying-abelian section dictionaries.
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Local lifting of every closed section detects exactness of a module-sheaf short complex. -/
theorem exact_of_local_boundaries (S : ShortComplex (SheafOfModules.{m} R))
    (hS : ∀ (U : C) (x : S.X₂.val.obj (op U)), S.g.val.app (op U) x = 0 →
      ∃ T : Sieve U, T ∈ J U ∧ ∀ ⦃V : C⦄ (f : V ⟶ U), T f →
        ∃ y : S.X₁.val.obj (op V), S.f.val.app (op V) y = S.X₂.val.map f.op x) :
    S.Exact := by
  rw [ShortComplex.exact_iff_epi_toCycles]
  let : CategoryTheory.Sheaf.IsLocallySurjective ((toSheaf R).map S.toCycles) := by
    constructor
    intro U s
    have hs : S.g.val.app (op U) (S.iCycles.val.app (op U) s) = 0 := by
      exact congrArg (fun a : S.cycles ⟶ S.X₃ => a.val.app (op U) s) S.iCycles_g
    obtain ⟨T, hT, h⟩ := hS U (S.iCycles.val.app (op U) s) hs
    apply J.superset_covering _ hT
    intro V f hf
    obtain ⟨y, hy⟩ := h f hf
    refine ⟨y, ?_⟩
    let : Mono S.iCycles.val :=
      inferInstanceAs (Mono ((SheafOfModules.forget R).map S.iCycles))
    have hi : Function.Injective (S.iCycles.val.app (op V)) :=
      PresheafOfModules.injective_of_mono S.iCycles.val (op V)
    apply hi
    have hy' := congrArg (fun a : S.X₁ ⟶ S.X₂ => a.val.app (op V) y) S.toCycles_i
    have hn := PresheafOfModules.naturality_apply S.iCycles.val f.op s
    exact hy'.trans (hy.trans hn.symm)
  have h : Epi ((toSheaf R).map S.toCycles) := inferInstance
  exact (toSheaf R).epi_of_epi_map h

/-- Local boundaries for the original predecessor/current/successor maps detect exactness. -/
theorem exactAt_of_local_boundaries {ι : Type*} {s : ComplexShape ι}
    (K : HomologicalComplex (SheafOfModules.{m} R) s) (i : ι)
    (hK : ∀ (U : C) (x : (K.X i).val.obj (op U)),
      (K.d i (s.next i)).val.app (op U) x = 0 →
      ∃ T : Sieve U, T ∈ J U ∧ ∀ ⦃V : C⦄ (f : V ⟶ U), T f →
        ∃ y : (K.X (s.prev i)).val.obj (op V),
          (K.d (s.prev i) i).val.app (op V) y = (K.X i).val.map f.op x) :
    K.ExactAt i :=
  exact_of_local_boundaries (K.sc i) hK

end SheafOfModules
