/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-! # Exact universe lifting of abelian sheaves

The functor is the native sheaf composition with the native additive ULift.
Exactness is proved by preservation of kernels and local surjectivity. No
preservation of injective objects is asserted.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Sheaf.BasisAcyclicity

universe c h v t

variable {C : Type c} [Category.{h} C] (J : GrothendieckTopology C)

/-- The actual value-universe lift, without changing the site or topology. -/
abbrev valueLift : Sheaf J AddCommGrpCat.{v} ⥤ Sheaf J AddCommGrpCat.{max v t} :=
  sheafCompose J AddCommGrpCat.uliftFunctor.{t, v}

instance valueLift_additive : (valueLift.{c, h, v, t} J).Additive where
  map_add := by
    intro F G f g
    ext X x
    rfl

instance valueLift_preservesFiniteLimits : PreservesFiniteLimits (valueLift.{c, h, v, t} J) := by
  let : PreservesFiniteLimits
      (valueLift.{c, h, v, t} J ⋙ sheafToPresheaf J AddCommGrpCat) :=
    inferInstanceAs (PreservesFiniteLimits (sheafToPresheaf J AddCommGrpCat ⋙
      (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.uliftFunctor.{t, v}))
  exact preservesFiniteLimits_of_reflects_of_preserves _ (sheafToPresheaf J AddCommGrpCat)

variable [HasSheafify J AddCommGrpCat.{v}]
  [HasSheafify J AddCommGrpCat.{max v t}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max v t}]
  [J.HasSheafCompose (forget AddCommGrpCat.{v})]
  [J.HasSheafCompose (forget AddCommGrpCat.{max v t})]

/-- Local lifts transport by `ULift.up`, so a sheaf epimorphism stays epi. -/
instance valueLift_preservesEpimorphisms : (valueLift.{c, h, v, t} J).PreservesEpimorphisms where
  preserves {F G} f hf := by
    let : Sheaf.IsLocallySurjective f :=
      (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat f).mpr inferInstance
    apply (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat _).mp
    change Presheaf.IsLocallySurjective J
      (Functor.whiskerRight f.hom AddCommGrpCat.uliftFunctor.{t, v})
    constructor
    intro W s
    apply J.superset_covering _ (Presheaf.imageSieve_mem J f.hom s.down)
    intro V g hg
    obtain ⟨a, ha⟩ := hg
    refine ⟨ULift.up a, ?_⟩
    exact congrArg ULift.up ha

/-- Exactness at the original coefficient universe is preserved by value lift. -/
theorem valueLift_map_shortExact
    (S : ShortComplex (Sheaf J AddCommGrpCat.{v})) (hS : S.ShortExact) :
    (S.map (valueLift.{c, h, v, t} J)).ShortExact := by
  let : Mono S.f := hS.mono_f
  let : Epi S.g := hS.epi_g
  exact {
    exact := hS.exact.map_of_mono_of_preservesKernel _ inferInstance inferInstance
    mono_f := by change Mono ((valueLift J).map S.f); infer_instance
    epi_g := by change Epi ((valueLift J).map S.g); infer_instance }

instance valueLift_preservesFiniteColimits :
    PreservesFiniteColimits (valueLift.{c, h, v, t} J) := by
  have h : ∀ S : ShortComplex (Sheaf J AddCommGrpCat.{v}),
      S.ShortExact → (S.map (valueLift.{c, h, v, t} J)).ShortExact :=
    fun S hS => valueLift_map_shortExact.{c, h, v, t} J S hS
  exact (((Functor.exact_tfae (valueLift.{c, h, v, t} J)).out 1 4 rfl rfl).mp h).2

end CategoryTheory.Sheaf.BasisAcyclicity
