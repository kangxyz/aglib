/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-! # Sectionwise exactness on a covering object basis

A covering object basis detects exactness of actual abelian sheaves. Cover
indices, category size and coefficient values have independent universes.
The proof uses local surjectivity of the original map to cycles; no assertion
that evaluation preserves arbitrary epimorphisms is made.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits Opposite

universe c h v k

namespace CategoryTheory.Sheaf.BasisAcyclicity

variable {C : Type c} [Category.{h} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{v}]
  [J.HasSheafCompose (forget AddCommGrpCat.{v})]
  (B : C → Prop)
  (hB : ∀ W : C, ∃ (ι : Type k) (U : ι → Over W),
    Sieve.ofArrows (fun i => (U i).left) (fun i => (U i).hom) ∈ J W ∧
      ∀ i, B (U i).left)

include hB

omit [HasSheafify J AddCommGrpCat.{v}] in
/-- Surjectivity of original sections on a covering object basis implies that
an actual sheaf morphism is epi. -/
theorem epi_of_sections_surjective_on_basis
    {F G : Sheaf J AddCommGrpCat.{v}} (f : F ⟶ G)
    (hf : ∀ W, B W → Function.Surjective (f.hom.app (op W))) : Epi f := by
  let : Sheaf.IsLocallySurjective f := by
    constructor
    intro W s
    obtain ⟨ι, U, hU, hBU⟩ := hB W
    apply J.superset_covering _ hU
    rw [Sieve.ofArrows, Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
    intro i
    exact hf (U i).left (hBU i) (G.obj.map (U i).hom.op s)
  infer_instance

/-- Exactness of original section short complexes on a covering object basis
detects exactness of the sheaf short complex. -/
theorem exact_of_sections_on_basis
    (S : ShortComplex (Sheaf J AddCommGrpCat.{v}))
    (hS : ∀ W, B W →
      (S.map (sheafToPresheaf J AddCommGrpCat ⋙
        (evaluation Cᵒᵖ AddCommGrpCat).obj (op W))).Exact) : S.Exact := by
  rw [ShortComplex.exact_iff_epi_toCycles]
  apply epi_of_sections_surjective_on_basis B hB
  intro W hW s
  have hs : S.g.hom.app (op W) (S.iCycles.hom.app (op W) s) = 0 := by
    have H := congrArg
      (fun f : S.cycles ⟶ S.X₃ => f.hom.app (op W) s) S.iCycles_g
    change S.g.hom.app (op W) (S.iCycles.hom.app (op W) s) = 0 at H
    exact H
  obtain ⟨a, ha⟩ := (ShortComplex.ab_exact_iff _).mp (hS W hW)
    (S.iCycles.hom.app (op W) s) hs
  refine ⟨a, ?_⟩
  let E := sheafToPresheaf J AddCommGrpCat.{v} ⋙
    (evaluation Cᵒᵖ AddCommGrpCat.{v}).obj (op W)
  have : Mono (S.iCycles.hom.app (op W)) :=
    inferInstanceAs (Mono (E.map S.iCycles))
  apply (AddCommGrpCat.mono_iff_injective (S.iCycles.hom.app (op W))).mp this
  have H := congrArg (fun f => f.hom.app (op W) a) S.toCycles_i
  exact H.trans ha

/-- Arbitrary-shape complex exactness is detected by original sections on the basis. -/
theorem exactAt_of_sections_on_basis {ι : Type*} {s : ComplexShape ι}
    (K : HomologicalComplex (Sheaf J AddCommGrpCat.{v}) s) (n : ι)
    (hK : ∀ W, B W →
      (((sheafToPresheaf J AddCommGrpCat ⋙
        (evaluation Cᵒᵖ AddCommGrpCat).obj (op W)).mapHomologicalComplex s).obj K).ExactAt n) :
    K.ExactAt n := by
  apply exact_of_sections_on_basis B hB (K.sc n)
  exact hK

end CategoryTheory.Sheaf.BasisAcyclicity
