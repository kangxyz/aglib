/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.FreeRepresentableCover
public import Mathlib.Algebra.Category.ModuleCat.EpiMono

/-! # Actual restrictions of genuine injective module sheaves

A monomorphism of site objects gives a monomorphism of the original free
module generators. Genuine module-sheaf injectivity therefore makes the
original restriction of sections surjective. No injectivity of the underlying
abelian sheaf is asserted or used, and the coefficient ring is unchanged.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

namespace ModuleCat

universe r w

/-- The original free-module map sends each basis element to its original image. -/
theorem freeWideFunctor_map_eq_lmapDomain (R : Type r) [Ring R]
    {X Y : Type w} (f : X ⟶ Y) :
    (freeWideFunctor R).map f = ModuleCat.ofHom (Finsupp.lmapDomain R R f) := by
  apply freeWide_hom_ext
  intro x
  change freeWideDesc (R := R) (M := freeWide R Y)
      (fun x => Finsupp.single (f x) (1 : R)) (Finsupp.single x (1 : R)) =
    Finsupp.mapDomain f (Finsupp.single x (1 : R))
  simp only [freeWideDesc_single, Finsupp.mapDomain_single]

/-- Free modules with independent scalar and basis universes preserve monomorphisms. -/
instance freeWideFunctor_preservesMonomorphisms (R : Type r) [Ring R] :
    (freeWideFunctor.{r, w} R).PreservesMonomorphisms where
  preserves f _ := by
    rw [freeWideFunctor_map_eq_lmapDomain]
    apply (ModuleCat.mono_iff_injective _).mpr
    exact Finsupp.mapDomain_injective ((CategoryTheory.mono_iff_injective f).mp inferInstance)

namespace Sheaf

universe c h t

variable {C : Type c} [Category.{h} C] (J : GrothendieckTopology C)
  (R : Type r) [Ring R] [HasSheafify J (ModuleCat.{max c h r t} R)]

/-- The native large-valued free representable retains monic site maps. -/
instance freeRepresentableFunctor_preservesMonomorphisms :
    (freeRepresentableFunctor.{r, c, h, t} J R).PreservesMonomorphisms := by
  unfold freeRepresentableFunctor
  infer_instance

/-- A genuine injective module sheaf extends original sections along a monic site map. -/
theorem restriction_epi_of_injective
    (I : Sheaf J (ModuleCat.{max c h r t} R)) [Injective I]
    {U V : C} (f : U ⟶ V) [Mono f] : Epi (I.obj.map f.op) := by
  apply (ModuleCat.epi_iff_surjective _).mpr
  intro x
  obtain ⟨s, hs⟩ := Injective.factors
    ((freeRepresentableSectionsEquiv J R U I).symm x)
    ((freeRepresentableFunctor J R).map f)
  refine ⟨freeRepresentableSectionsEquiv J R V I s, ?_⟩
  rw [← freeRepresentableSectionsEquiv_naturality_left J R f I s]
  exact (congrArg (freeRepresentableSectionsEquiv J R U I) hs).trans
    (Equiv.apply_symm_apply _ x)

end Sheaf
end ModuleCat
