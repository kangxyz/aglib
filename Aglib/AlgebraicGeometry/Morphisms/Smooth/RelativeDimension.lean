/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Smooth.Dimension
public import Mathlib.Topology.LocallyConstant.Basic

/-!
# The relative dimension of a smooth scheme over a field

Standard smooth presentations give neighborhoods of fixed relative dimension.
Over a field those dimensions agree on a nonempty overlap, by the dimension
of a nonempty smooth scheme. Thus a connected smooth scheme has one relative
dimension, without quasi-compactness or an algebraically closed base field.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- A smooth morphism locally has a fixed relative dimension. -/
theorem exists_smoothOfRelativeDimension_open {X Y : Scheme.{u}}
    (f : X ⟶ Y) [Smooth f] (x : X) :
    ∃ (U : X.Opens) (n : ℕ), x ∈ U ∧ SmoothOfRelativeDimension n (U.ι ≫ f) := by
  obtain ⟨V, hV, U, hU, hx, e, hf⟩ := Smooth.exists_isStandardSmooth f x
  have hn : ∃ n, (f.appLE V U e).hom.IsStandardSmoothOfRelativeDimension n := by
    let := (f.appLE V U e).hom.toAlgebra
    change Algebra.IsStandardSmooth Γ(Y, V) Γ(X, U) at hf
    obtain ⟨ι, σ, hσ, hι, ⟨Q⟩⟩ := hf.out
    exact ⟨Q.dimension, ⟨ι, σ, hσ, hι, Q, rfl⟩⟩
  obtain ⟨n, hn⟩ := hn
  let : IsAffine V.toScheme := hV
  let : IsAffine U.toScheme := hU
  have hs : SmoothOfRelativeDimension n (f.resLE V U e) := by
    rw [HasRingHomProperty.iff_of_isAffine (P := @SmoothOfRelativeDimension n)]
    have : (RingHom.toMorphismProperty
        (RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n))).RespectsIso :=
      RingHom.toMorphismProperty_respectsIso_iff.mp
        (HasRingHomProperty.isLocal_ringHomProperty
          (@SmoothOfRelativeDimension n)).respectsIso
    exact (MorphismProperty.arrow_mk_iso_iff
      (RingHom.toMorphismProperty
        (RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n)))
      (arrowResLEAppIso f V U e)).mpr
        (RingHom.locally_of
          (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := n)) _ hn)
  refine ⟨U, n, hx, ?_⟩
  rw [← Hom.resLE_comp_ι f e]
  simpa only [Nat.add_zero] using
    (smoothOfRelativeDimension_comp n 0 (f.resLE V U e) V.ι)

/-- A nonempty scheme smooth over a field cannot have two different relative
dimensions. -/
theorem smoothOfRelativeDimension_eq {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (n m : ℕ) [Nonempty X]
    [hn : SmoothOfRelativeDimension n f] [hm : SmoothOfRelativeDimension m f] : n = m := by
  have h := (smoothFieldDimension k X f n hn inferInstance).symm.trans
    (smoothFieldDimension k X f m hm inferInstance)
  exact_mod_cast h

-- Morphism-property locality uses the definitionally equal field-scheme presentation.
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The relative dimensions on two smooth open neighborhoods agree wherever
the neighborhoods intersect. -/
theorem smoothOfRelativeDimension_eq_of_mem_inter
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (U V : X.Opens) (n m : ℕ)
    [hn : SmoothOfRelativeDimension n (U.ι ≫ f)]
    [hm : SmoothOfRelativeDimension m (V.ι ≫ f)]
    (x : X) (hxU : x ∈ U) (hxV : x ∈ V) : n = m := by
  let W := U ⊓ V
  let : Nonempty W.toScheme := ⟨⟨x, hxU, hxV⟩⟩
  have hWn : SmoothOfRelativeDimension n (W.ι ≫ f) := by
    rw [← X.homOfLE_ι (show W ≤ U from inf_le_left), Category.assoc]
    exact IsZariskiLocalAtSource.comp (P := @SmoothOfRelativeDimension.{u} n) hn _
  have hWm : SmoothOfRelativeDimension m (W.ι ≫ f) := by
    rw [← X.homOfLE_ι (show W ≤ V from inf_le_right), Category.assoc]
    exact IsZariskiLocalAtSource.comp (P := @SmoothOfRelativeDimension.{u} m) hm _
  exact smoothOfRelativeDimension_eq (W.ι ≫ f) n m

-- Morphism-property locality uses the definitionally equal field-scheme presentation.
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A nonempty connected smooth scheme over a field has a fixed relative
dimension. The point supplies only nonemptiness. -/
theorem exists_smoothOfRelativeDimension_of_preconnected
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [Smooth f] [PreconnectedSpace X] (x : X) :
    ∃ n, SmoothOfRelativeDimension n f := by
  choose U n hx hn using exists_smoothOfRelativeDimension_open f
  have hlc : IsLocallyConstant n := by
    rw [IsLocallyConstant.iff_exists_open]
    intro y
    refine ⟨U y, (U y).isOpen, hx y, ?_⟩
    intro z hz
    let := hn z
    let := hn y
    exact smoothOfRelativeDimension_eq_of_mem_inter f (U z) (U y)
      (n z) (n y) z (hx z) hz
  refine ⟨n x, IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension.{u} (n x))
    U ?_ ?_⟩
  · apply top_le_iff.mp
    intro y _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hx y⟩
  · intro y
    simpa only [hlc.apply_eq_of_preconnectedSpace y x] using hn y

end AlgebraicGeometry.Scheme
