/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Locality
public import Aglib.AlgebraicGeometry.Modules.Invertible.Pullback
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# The locus where a module is locally rank one

`Scheme.Modules.Invertible.IsLocallyRankOneAt M x` says that the module `M` on `X` pulls back
to a locally rank-one module along some open immersion whose image contains `x`. The set of such
points is open (`isOpen_setOf_isLocallyRankOneAt`), and `M` is locally rank one exactly when
every point lies in it (`isLocallyRankOne_iff_forall_isLocallyRankOneAt`). The condition pulls
back along every morphism and descends along open immersions. A pullback of `M` is locally rank
one as soon as the image of the morphism lies in the locus
(`isLocallyRankOne_pullback_of_forall`). No finiteness, Noetherian or quasicoherence hypothesis
is used. The openness argument for relative effective Cartier divisors (Kleiman, *The Picard
scheme*, arXiv:math/0504020v1, proof of Thm 3.7, p. 24) in
`EffectiveCartierDivisor/Relative/Open` uses this locus for the actual ideal of a closed
subscheme.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules.Invertible

variable {X Y : Scheme.{u}}

/-- `M` is locally rank one at `x`: it pulls back to a locally rank-one module along an open
immersion whose image contains `x`. -/
def IsLocallyRankOneAt (M : X.Modules) (x : X) : Prop :=
  ∃ (W : Scheme.{u}) (f : W ⟶ X) (_ : IsOpenImmersion f), x ∈ Set.range f ∧
    IsLocallyRankOne W ((Scheme.Modules.pullback f).obj M)

theorem IsLocallyRankOneAt.of_iso {M N : X.Modules} {x : X} (h : IsLocallyRankOneAt M x)
    (e : M ≅ N) : IsLocallyRankOneAt N x := by
  obtain ⟨W, f, hf, hx, hW⟩ := h
  exact ⟨W, f, hf, hx, isLocallyRankOne_of_iso _ ((Scheme.Modules.pullback f).mapIso e) hW⟩

/-- The condition descends along an open immersion. -/
theorem IsLocallyRankOneAt.of_pullback (f : Y ⟶ X) [IsOpenImmersion f] {M : X.Modules}
    {y : Y} (h : IsLocallyRankOneAt ((Scheme.Modules.pullback f).obj M) y) :
    IsLocallyRankOneAt M (f y) := by
  obtain ⟨W, g, hg, ⟨w, rfl⟩, hW⟩ := h
  have := hg
  exact ⟨W, g ≫ f, inferInstance, ⟨w, Scheme.Hom.comp_apply g f w⟩,
    isLocallyRankOne_of_iso _ ((Scheme.Modules.pullbackComp g f).app M) hW⟩

/-- The condition pulls back along every morphism. -/
theorem IsLocallyRankOneAt.pullback (f : Y ⟶ X) {M : X.Modules} {y : Y}
    (h : IsLocallyRankOneAt M (f y)) :
    IsLocallyRankOneAt ((Scheme.Modules.pullback f).obj M) y := by
  obtain ⟨W, g, hg, hy, hW⟩ := h
  have := hg
  refine ⟨Limits.pullback f g, Limits.pullback.fst f g, inferInstance, ?_, ?_⟩
  · rw [Scheme.Pullback.range_fst]
    exact hy
  · let e : (Scheme.Modules.pullback (Limits.pullback.fst f g)).obj
        ((Scheme.Modules.pullback f).obj M) ≅
        (Scheme.Modules.pullback (Limits.pullback.snd f g)).obj
          ((Scheme.Modules.pullback g).obj M) :=
      (Scheme.Modules.pullbackComp _ _).app M ≪≫
        (Scheme.Modules.pullbackCongr Limits.pullback.condition).app M ≪≫
          ((Scheme.Modules.pullbackComp _ _).app M).symm
    exact isLocallyRankOne_of_iso _ e.symm (pullback_locallyRankOne _ _ hW)

/-- The locus where a module is locally rank one is open. -/
theorem isOpen_setOf_isLocallyRankOneAt (M : X.Modules) :
    IsOpen {x | IsLocallyRankOneAt M x} := by
  rw [isOpen_iff_forall_mem_open]
  rintro x ⟨W, f, hf, hx, hW⟩
  have := hf
  exact ⟨Set.range f, fun y hy ↦ ⟨W, f, hf, hy, hW⟩, IsOpenImmersion.isOpen_range f, hx⟩

/-- A module that is locally rank one at every point is locally rank one. -/
theorem isLocallyRankOne_of_forall_isLocallyRankOneAt (M : X.Modules)
    (h : ∀ x, IsLocallyRankOneAt M x) : IsLocallyRankOne X M := by
  choose W f hf hx hW using h
  let U : X → X.Opens := fun x ↦ (f x).opensRange
  have hcov : IsOpenCover U := .mk (by
    apply top_le_iff.mp
    intro x _
    exact Opens.mem_iSup.mpr ⟨x, hx x⟩)
  apply isLocallyRankOne_of_cover_restrict M U hcov
  intro x
  have := hf x
  let e : M.restrict (U x).ι ≅ (Scheme.Modules.pullback (f x).isoOpensRange.inv).obj
      ((Scheme.Modules.pullback (f x)).obj M) :=
    (Scheme.Modules.restrictFunctorIsoPullback (U x).ι).app M ≪≫
      (Scheme.Modules.pullbackCongr (Scheme.Hom.isoOpensRange_inv_comp (f x)).symm).app M ≪≫
        ((Scheme.Modules.pullbackComp _ _).app M).symm
  exact isLocallyRankOne_of_iso _ e.symm (pullback_locallyRankOne _ _ (hW x))

/-- A locally rank-one module is locally rank one at every point. -/
theorem IsLocallyRankOne.isLocallyRankOneAt {M : X.Modules} (h : IsLocallyRankOne X M)
    (x : X) : IsLocallyRankOneAt M x :=
  ⟨X, 𝟙 X, inferInstance, ⟨x, rfl⟩,
    isLocallyRankOne_of_iso _ ((Scheme.Modules.pullbackId (X := X)).app M).symm h⟩

theorem isLocallyRankOne_iff_forall_isLocallyRankOneAt (M : X.Modules) :
    IsLocallyRankOne X M ↔ ∀ x, IsLocallyRankOneAt M x :=
  ⟨fun h x ↦ h.isLocallyRankOneAt x, isLocallyRankOne_of_forall_isLocallyRankOneAt M⟩

/-- A pullback is locally rank one when the image of the morphism lies in the locus. -/
theorem isLocallyRankOne_pullback_of_forall (g : Y ⟶ X) (M : X.Modules)
    (h : ∀ y, IsLocallyRankOneAt M (g y)) :
    IsLocallyRankOne Y ((Scheme.Modules.pullback g).obj M) :=
  isLocallyRankOne_of_forall_isLocallyRankOneAt _ fun y ↦ (h y).pullback g

end AlgebraicGeometry.Scheme.Modules.Invertible
