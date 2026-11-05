/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Torsion.FinitePresentation.FiniteCover
public import Mathlib.CategoryTheory.Sites.MayerVietorisSquare
public import Mathlib.CategoryTheory.Abelian.CommSq

/-! # Actual Mayer–Vietoris section sequences on injective sheaves

Restriction along a monomorphism of site objects is surjective on an injective
abelian sheaf: the free represented sheaf map is monic, and genuine injectivity
extends the original section. Consequently a native Mayer–Vietoris square
has a short exact section sequence on each injective. No topological space,
open-immersion acyclicity, or derived-composition theorem is assumed.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w a b

namespace CategoryTheory.Sheaf

open Hypercohomology

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max v w}]

/-- A genuine injective abelian sheaf extends sections along every site monomorphism. -/
theorem restriction_epi_of_injective (I : Sheaf J AddCommGrpCat.{max v w}) [Injective I]
    {U V : C} (f : U ⟶ V) [Mono f] : Epi (I.obj.map f.op) := by
  let a := (freeAbelianSheafFunctor.{w} J).map f
  have : Mono a := by
    dsimp [a, freeAbelianSheafFunctor]
    infer_instance
  apply (AddCommGrpCat.epi_iff_surjective _).mpr
  intro x
  obtain ⟨s, hs⟩ := Injective.factors ((sectionsEquiv.{w} J U I).symm x) a
  refine ⟨sectionsEquiv.{w} J V I s, ?_⟩
  rw [← TorsionFinitePresentation.FiniteCover.freeAbelian_sections_naturality_left J f I s]
  exact (congrArg (sectionsEquiv.{w} J U I) hs).trans (Equiv.apply_symm_apply _ x)

end CategoryTheory.Sheaf

namespace CategoryTheory.Square

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (S : Square C) [Mono S.f₂₄] [Mono S.f₃₄]
  (hS : S.IsPullback) (hcover : Sieve.ofTwoArrows S.f₂₄ S.f₃₄ ∈ J S.X₄)

variable [HasSheafify J AddCommGrpCat.{max v w}]
  (F : Sheaf J AddCommGrpCat.{max v w})

/-- The original restriction sum and difference on the four site objects. -/
def sectionsShortComplex : ShortComplex AddCommGrpCat.{max v w} :=
  (S.op.map F.obj).commSq.shortComplex'

include hS hcover

omit [HasSheafify J AddCommGrpCat.{max v w}] in
/-- The sheaf axiom gives exactness, independently of injectivity. -/
theorem sectionsShortComplex_exact : (S.sectionsShortComplex F).Exact :=
  (Sheaf.TorsionFinitePresentation.FiniteCover.sheaf_isPullback J S hS hcover F).exact_shortComplex'

/-- Injectivity supplies only surjectivity of the original difference map. -/
theorem sectionsShortComplex_shortExact [Injective F] :
    (S.sectionsShortComplex F).ShortExact := by
  have : Mono S.f₁₃ := hS.mono_f₁₃
  have : Epi (F.obj.map S.f₁₃.op) := Sheaf.restriction_epi_of_injective J F S.f₁₃
  have : Epi (-(F.obj.map S.f₁₃.op)) := inferInstance
  have : Epi (S.sectionsShortComplex F).g :=
    epi_of_epi_fac (biprod.inr_desc (F.obj.map S.f₁₂.op) (-(F.obj.map S.f₁₃.op)))
  have : Mono (S.sectionsShortComplex F).f :=
    (Sheaf.TorsionFinitePresentation.FiniteCover.sheaf_isPullback
      J S hS hcover F).mono_shortComplex'_f
  exact { exact := S.sectionsShortComplex_exact hS hcover F }

end CategoryTheory.Square
