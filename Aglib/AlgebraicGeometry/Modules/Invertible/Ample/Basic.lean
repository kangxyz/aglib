/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Nonvanishing.Pullback
public import Aglib.AlgebraicGeometry.Modules.Invertible.Nonvanishing.GlobalFrame
public import Aglib.AlgebraicGeometry.Modules.Invertible.PullbackTensor.Local
public import Mathlib.AlgebraicGeometry.QuasiAffine

/-!
# Ampleness of original line bundles

An invertible sheaf is ample when the scheme is quasi-compact and its affine
nonvanishing opens, from global sections of positive tensor powers, cover the
scheme. This is Stacks, Definition 28.27.1, in Section 01PR. The definition uses
the existing line bundle, tensor powers and nonvanishing opens.

The first operations are invariance under isomorphism and pullback by affine
morphisms. In particular closed restrictions and automorphism pullbacks preserve
ampleness. Ampleness of a trivial bundle gives quasi-affineness, not affineness.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules.Invertible

open PullbackTensor.Local

universe u

variable {X Y : Scheme.{u}}

/-- The affine-nonvanishing-open definition of an ample invertible sheaf.
No choice of projective embedding or line-bundle representative is included. -/
def LineBundle.IsAmple (L : LineBundle X) : Prop :=
  CompactSpace X ∧ ∀ x : X, ∃ (n : ℕ), 0 < n ∧
    ∃ s : Γ((tensorPowerLineBundle X L n).val, ⊤),
      IsAffineOpen (nonvanishingOpen (tensorPowerLineBundle X L n) s) ∧
        x ∈ nonvanishingOpen (tensorPowerLineBundle X L n) s

/-- Equal original Picard classes preserve ampleness. The proof transports
sections between the existing tensor powers, without changing the powers. -/
theorem LineBundle.IsAmple.of_classOf_eq {L M : LineBundle X}
    (hL : L.IsAmple) (h : classOf X L = classOf X M) : M.IsAmple := by
  refine ⟨hL.1, ?_⟩
  intro x
  obtain ⟨n, hn, s, hs, hx⟩ := hL.2 x
  have hp : classOf X (tensorPowerLineBundle X L n) =
      classOf X (tensorPowerLineBundle X M n) := by
    simp only [classOf_tensorPower, h]
  obtain ⟨e⟩ := (class_eq_iff X _ _).mp hp
  refine ⟨n, hn, e.hom.val.app (op ⊤) s, ?_, ?_⟩
  · rwa [nonvanishingOpen_iso]
  · rwa [nonvanishingOpen_iso]

/-- Isomorphism of the original sheaves preserves ampleness. -/
theorem LineBundle.IsAmple.of_iso {L M : LineBundle X}
    (hL : L.IsAmple) (e : L.val ≅ M.val) : M.IsAmple :=
  hL.of_classOf_eq ((class_eq_iff X L M).mpr ⟨e⟩)

/-- Pullback of an actual tensor power has the class of the same power of
the original pulled-back bundle. -/
theorem classOf_pullback_tensorPower (f : X ⟶ Y) (L : LineBundle Y) (n : ℕ) :
    classOf X (pullbackLineBundle f (tensorPowerLineBundle Y L n)) =
      classOf X (tensorPowerLineBundle X (pullbackLineBundle f L) n) := by
  rw [← pullbackClass_classOf, classOf_tensorPower, classOf_tensorPower,
    ← pullbackClass_classOf]
  exact map_nsmul (pullbackHom f) n (classOf Y L)

-- Pullback module sheaves and their LineBundle coercions use the same
-- native carrier, but unfold at different transparency levels.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- An affine morphism pulls an ample invertible sheaf back to an ample
invertible sheaf. All section and nonvanishing maps are the original ones. -/
theorem LineBundle.IsAmple.pullback_of_isAffineHom {L : LineBundle Y}
    (hL : L.IsAmple) (f : X ⟶ Y) [IsAffineHom f] : (pullbackLineBundle f L).IsAmple := by
  let : CompactSpace Y := hL.1
  refine ⟨QuasiCompact.compactSpace_of_compactSpace f, ?_⟩
  intro x
  obtain ⟨n, hn, s, hs, hx⟩ := hL.2 (f x)
  let N := pullbackLineBundle f (tensorPowerLineBundle Y L n)
  obtain ⟨e⟩ := (class_eq_iff X N
    (tensorPowerLineBundle X (pullbackLineBundle f L) n)).mp
      (classOf_pullback_tensorPower f L n)
  let s' := Nonvanishing.pullbackSection f (tensorPowerLineBundle Y L n).val s
  refine ⟨n, hn, e.hom.val.app (op ⊤) s', ?_, ?_⟩
  · rw [nonvanishingOpen_iso]
    rw [Nonvanishing.nonvanishingOpen_pullback]
    exact hs.preimage f
  · rw [nonvanishingOpen_iso]
    rw [Nonvanishing.nonvanishingOpen_pullback]
    exact hx

/-- An ample line bundle whose original Picard class vanishes makes the
scheme quasi-affine. No implication of affineness is asserted. -/
theorem LineBundle.IsAmple.isQuasiAffine_of_classOf_eq_zero {L : LineBundle X}
    (hL : L.IsAmple) (h : classOf X L = 0) : X.IsQuasiAffine := by
  let : CompactSpace X := hL.1
  apply IsQuasiAffine.of_forall_exists_mem_basicOpen X
  intro x
  obtain ⟨n, hn, s, hs, hx⟩ := hL.2 x
  have hp : classOf X (tensorPowerLineBundle X L n) =
      classOf X (trivialLineBundle X) := by
    rw [classOf_tensorPower, h, smul_zero, classOf_trivial]
  obtain ⟨e⟩ := (class_eq_iff X _ _).mp hp
  let e' : (tensorPowerLineBundle X L n).val ≅ SheafOfModules.unit X.ringCatSheaf :=
    e ≪≫ coproductUniqueIso (fun _ : PUnit.{u + 1} => SheafOfModules.unit X.ringCatSheaf)
  refine ⟨e'.hom.val.app (op ⊤) s, ?_, ?_⟩
  · rwa [← Nonvanishing.nonvanishingOpen_eq_basicOpen_of_unitIso _ e' s]
  · rwa [← Nonvanishing.nonvanishingOpen_eq_basicOpen_of_unitIso _ e' s]

end AlgebraicGeometry.Scheme.Modules.Invertible
