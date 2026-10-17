/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Descent
public import Aglib.Algebra.Category.ModuleCat.Descent.Coalgebra

/-!
# Effective faithfully flat descent of modules

For a faithfully flat ring map `f : A ⟶ B` in `CommRingCat`, Mathlib's extension-of-scalars
pseudofunctor, reindexed to the site `CommRingCatᵒᵖ`
(`CommRingCat.moduleCatExtendScalarsPseudofunctorOpOp`), satisfies
`Pseudofunctor.IsStackFor` for the singleton presieve of `f.op : op B ⟶ op A`: the functor
from `A`-modules to descent data along `f.op` is an equivalence of categories.

The proof composes Mathlib's comonadicity of extension of scalars along a faithfully flat map
(`ModuleCat.comonadicExtendScalars`, whose effectivity consequence Mathlib leaves as a TODO)
with the fully faithful functor from descent data to coalgebras of
`CommRingCat.ExtendScalarsDescent.coalgebraFunctor`, whose composite with `toDescentData` is
`Comonad.comparison`. This is faithfully flat descent for modules (Vistoli, *Notes on
Grothendieck topologies, fibered categories and descent theory*, arXiv:math/0412512v4,
Theorem 4.21; Stacks Project, Tag 023N (1)–(2)). The descent data are Mathlib's
`Pseudofunctor.DescentData`, which replace the cocycle category of Stacks 023G and Vistoli's
`Mod_{A→B}`; the description of the inverse by `H⁰` in Stacks 023N (3) is not encoded. Modules
are `ModuleCat.{u}` over rings in `CommRingCat.{u}`, and the site is `CommRingCatᵒᵖ`.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Opposite Limits ModuleCat

namespace CommRingCat

namespace ExtendScalarsDescent

variable {A B : CommRingCat.{u}} (f : A ⟶ B)

/-- For a faithfully flat `f`, descent data along `f.op` are equivalent to coalgebras over the
comonad of `extendScalars f ⊣ restrictScalars f`. -/
theorem isEquivalence_coalgebraFunctor (hf : f.hom.FaithfullyFlat) :
    (coalgebraFunctor f).IsEquivalence := by
  have hc : (Comonad.comparison (extendRestrictScalarsAdj f.hom)).IsEquivalence :=
    (comonadicExtendScalars hf).eqv
  have : ((moduleCatExtendScalarsPseudofunctorOpOp.{u}).toDescentData
      (fun (_ : PUnit.{1}) ↦ f.op) ⋙ coalgebraFunctor f).IsEquivalence :=
    @Functor.isEquivalence_of_iso _ _ _ _ _ _ (toDescentDataCompCoalgebraFunctorIso f).symm hc
  have : (coalgebraFunctor f).Full := (fullyFaithfulCoalgebraFunctor f).full
  have : (coalgebraFunctor f).Faithful := (fullyFaithfulCoalgebraFunctor f).faithful
  have : (coalgebraFunctor f).EssSurj :=
    ⟨fun Y ↦ ⟨_, ⟨((moduleCatExtendScalarsPseudofunctorOpOp.{u}).toDescentData
      (fun (_ : PUnit.{1}) ↦ f.op) ⋙ coalgebraFunctor f).objObjPreimageIso Y⟩⟩⟩
  exact { }

/-- Faithfully flat descent of modules: for a faithfully flat `f : A ⟶ B`, the functor from
`A`-modules to descent data along `f.op` is an equivalence. -/
theorem isEquivalence_toDescentData (hf : f.hom.FaithfullyFlat) :
    ((moduleCatExtendScalarsPseudofunctorOpOp.{u}).toDescentData
      (fun (_ : PUnit.{1}) ↦ f.op)).IsEquivalence := by
  have := isEquivalence_coalgebraFunctor f hf
  have hc : (Comonad.comparison (extendRestrictScalarsAdj f.hom)).IsEquivalence :=
    (comonadicExtendScalars hf).eqv
  have : ((moduleCatExtendScalarsPseudofunctorOpOp.{u}).toDescentData
      (fun (_ : PUnit.{1}) ↦ f.op) ⋙ coalgebraFunctor f).IsEquivalence :=
    @Functor.isEquivalence_of_iso _ _ _ _ _ _ (toDescentDataCompCoalgebraFunctorIso f).symm hc
  exact Functor.isEquivalence_of_comp_right _ (coalgebraFunctor f)

end ExtendScalarsDescent

/-- **Effective faithfully flat descent of modules.** For a faithfully flat ring map
`f : A ⟶ B`, Mathlib's extension-of-scalars pseudofunctor on the site `CommRingCatᵒᵖ` is a
stack for the singleton presieve of `f.op : op B ⟶ op A`, for modules in `ModuleCat.{u}` over
rings in `CommRingCat.{u}`. This encodes Stacks Project, Tag 023N (1)–(2), and Vistoli,
arXiv:math/0412512v4, Theorem 4.21, with Mathlib's `Pseudofunctor.DescentData` in place of the
cocycle category of Stacks 023G or Vistoli's `Mod_{A→B}`; Stacks 023N (3), the inverse given by
`H⁰`, is not encoded. -/
theorem isStackFor_moduleCatExtendScalarsPseudofunctorOpOp_singleton {A B : CommRingCat.{u}}
    (f : A ⟶ B) (hf : f.hom.FaithfullyFlat) :
    (moduleCatExtendScalarsPseudofunctorOpOp.{u}).IsStackFor (Presieve.singleton f.op) := by
  rw [← Presieve.ofArrows_pUnit.{0}, Pseudofunctor.isStackFor_ofArrows_iff]
  exact ExtendScalarsDescent.isEquivalence_toDescentData f hf

end CommRingCat
