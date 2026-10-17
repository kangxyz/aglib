/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!
# Pullback of ideal sheaves: affine formula, flat surjections and open base change

This file collects the properties of Mathlib's pullback `Scheme.IdealSheafData.comap` and
pushforward `Scheme.IdealSheafData.map` of ideal sheaves used by faithfully flat descent of closed
subschemes.

* `Scheme.Hom.app_injective_of_flat_of_surjective`: every section map of a flat surjective
  morphism is injective; no quasi-compactness is needed, since the stalk maps are flat local and
  hence faithfully flat.
* `IsSchemeTheoreticallyDominant.of_flat_of_surjective`: flat surjective morphisms have trivial
  kernel.
* `Scheme.IdealSheafData.map_comap_of_flat_of_surjective`: along a flat surjective morphism `f`,
  `(I.comap f).map f = I`; hence `comap · f` is injective.
* `Scheme.IdealSheafData.ideal_comap_top_of_isAffine`, `ideal_map_top_of_isAffine`: between affine
  schemes the pullback and pushforward are extension and contraction of ideals of global sections
  along `f.appTop`.
* `Scheme.Hom.ker_eq_comap_of_isPullback_of_isOpenImmersion`: the kernel of a quasi-compact
  morphism commutes with base change along an open immersion.
* `Scheme.IdealSheafData.ext_of_comap_eq`: ideal sheaves agreeing after pullback along a jointly
  surjective family of open immersions are equal.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- Every section map `Γ(Y, U) → Γ(X, f⁻¹ U)` of a flat surjective morphism is injective: a
section killed by `f` has zero germs, because each stalk map of `f` is a flat local ring map,
hence faithfully flat and injective. -/
lemma Scheme.Hom.app_injective_of_flat_of_surjective (f : X ⟶ Y) [Flat f] [Surjective f]
    (U : Y.Opens) : Function.Injective (f.app U) := by
  rw [injective_iff_map_eq_zero]
  intro s hs
  refine TopCat.Presheaf.section_ext Y.sheaf U s 0 fun y hy ↦ ?_
  obtain ⟨x, rfl⟩ := f.surjective y
  have hinj : Function.Injective (f.stalkMap x) := by
    algebraize [(f.stalkMap x).hom]
    have : Module.FaithfullyFlat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
      @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
        (Flat.stalkMap f x) (f.toLRSHom.prop x)
    exact ‹RingHom.FaithfullyFlat _›.injective
  change Y.presheaf.germ U (f x) hy s = Y.presheaf.germ U (f x) hy 0
  rw [map_zero]
  apply hinj
  rw [Scheme.Hom.germ_stalkMap_apply, hs, map_zero, map_zero]

/-- A flat surjective morphism is scheme-theoretically dominant: its kernel is trivial. -/
instance IsSchemeTheoreticallyDominant.of_flat_of_surjective (f : X ⟶ Y) [Flat f]
    [Surjective f] : IsSchemeTheoreticallyDominant f := by
  constructor
  apply le_bot_iff.mp
  intro U s hs
  have hs' := f.ideal_ker_le U hs
  rw [RingHom.mem_ker] at hs'
  exact Ideal.mem_bot.mpr (f.app_injective_of_flat_of_surjective U.1 (by rw [hs', map_zero]))

namespace Scheme.IdealSheafData

/-- Pushing forward the pullback of an ideal sheaf along a flat surjective morphism recovers the
ideal sheaf: the pulled-back subscheme maps to the original one by a flat surjective base change of
`f`, whose kernel is trivial. -/
lemma map_comap_of_flat_of_surjective (I : Y.IdealSheafData) (f : X ⟶ Y) [Flat f]
    [Surjective f] : (I.comap f).map f = I := by
  rw [map, ← comapIso_hom_fst, Category.assoc, pullback.condition,
    Scheme.Hom.ker_comp_of_isIso, Scheme.Hom.ker_comp, (pullback.snd f I.subschemeι).ker_eq_bot,
    map_bot, ker_subschemeι]

/-- Pullback of ideal sheaves along a flat surjective morphism is injective. -/
lemma comap_injective_of_flat_of_surjective (f : X ⟶ Y) [Flat f] [Surjective f] :
    Function.Injective (comap · f : Y.IdealSheafData → X.IdealSheafData) := fun I J h ↦ by
  rw [← map_comap_of_flat_of_surjective I f, ← map_comap_of_flat_of_surjective J f]
  exact congrArg (map · f) h

/-- Between affine schemes, the pushforward of an ideal sheaf is the contraction of its ideal of
global sections along `f.appTop`. -/
lemma ideal_map_top_of_isAffine [IsAffine X] [IsAffine Y] (I : X.IdealSheafData) (f : X ⟶ Y) :
    (I.map f).ideal ⟨⊤, isAffineOpen_top Y⟩ =
      (I.ideal ⟨⊤, isAffineOpen_top X⟩).comap f.appTop.hom :=
  ideal_map_of_isAffineHom I f _

/-- Between affine schemes, the pullback of an ideal sheaf is the extension of its ideal of global
sections along `f.appTop`. Both sides are left adjoint to the same contraction. -/
lemma ideal_comap_top_of_isAffine [IsAffine X] [IsAffine Y] (I : Y.IdealSheafData) (f : X ⟶ Y) :
    (I.comap f).ideal ⟨⊤, isAffineOpen_top X⟩ =
      (I.ideal ⟨⊤, isAffineOpen_top Y⟩).map f.appTop.hom := by
  have hmap : ∀ K : X.IdealSheafData, (K.map f).ideal ⟨⊤, isAffineOpen_top Y⟩ =
      (K.ideal ⟨⊤, isAffineOpen_top X⟩).comap f.appTop.hom := fun K ↦
    ideal_map_top_of_isAffine K f
  apply le_antisymm
  · let K : X.IdealSheafData :=
      equivOfIsAffine.symm ((I.ideal ⟨⊤, isAffineOpen_top Y⟩).map f.appTop.hom)
    have hK : K.ideal ⟨⊤, isAffineOpen_top X⟩ =
        (I.ideal ⟨⊤, isAffineOpen_top Y⟩).map f.appTop.hom :=
      equivOfIsAffine.apply_symm_apply _
    have hle : I.comap f ≤ K := by
      rw [← le_map_iff_comap_le]
      apply le_of_isAffine
      rw [hmap, hK]
      exact Ideal.le_comap_map
    rw [← hK]
    exact hle _
  · rw [Ideal.map_le_iff_le_comap, ← hmap]
    exact le_map_comap I f _

/-- Ideal sheaves that agree after pullback along a jointly surjective family of open immersions
are equal. -/
lemma ext_of_comap_eq {ι : Type*} {U : ι → Scheme.{u}} (c : ∀ i, U i ⟶ X)
    [∀ i, IsOpenImmersion (c i)] (hc : ⋃ i, Set.range (c i) = Set.univ)
    {I J : X.IdealSheafData} (h : ∀ i, I.comap (c i) = J.comap (c i)) : I = J := by
  refine ext_of_iSup_eq_top (ι := Σ i, (U i).affineOpens)
    (fun W ↦ ⟨c W.1 ''ᵁ W.2, W.2.2.image_of_isOpenImmersion _⟩) ?_ fun W ↦ ?_
  · refine top_le_iff.mp fun x _ ↦ ?_
    obtain ⟨i, y, rfl⟩ : ∃ i y, c i y = x := by
      simpa using (Set.ext_iff.mp hc x).mpr (Set.mem_univ x)
    obtain ⟨_, ⟨V, hV, rfl⟩, hyV, -⟩ :=
      (U i).isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨i, ⟨V, hV⟩⟩, ⟨y, hyV, rfl⟩⟩
  · have := congr($(h W.1).ideal W.2)
    rw [ideal_comap_of_isOpenImmersion, ideal_comap_of_isOpenImmersion] at this
    exact Ideal.comap_injective_of_surjective _
      (ConcreteCategory.bijective_of_isIso ((c W.1).appIso W.2).inv).2 this

end Scheme.IdealSheafData

/-- The kernel of a quasi-compact morphism commutes with base change along an open immersion: for
a cartesian square with `iV` an open immersion, the kernel of the base change `f'` is the pullback
of the kernel of `f`. -/
lemma Scheme.Hom.ker_eq_comap_of_isPullback_of_isOpenImmersion {U V : Scheme.{u}}
    {f : X ⟶ Y} {f' : U ⟶ V} {iU : U ⟶ X} {iV : V ⟶ Y} [IsOpenImmersion iV] [QuasiCompact f]
    (H : IsPullback f' iU iV f) : f'.ker = f.ker.comap iV := by
  refine IdealSheafData.ext (funext fun W ↦ ?_)
  rw [Scheme.ker_ideal_of_isPullback_of_isOpenImmersion f f' iU iV H W,
    IdealSheafData.ideal_comap_of_isOpenImmersion]

end AlgebraicGeometry
