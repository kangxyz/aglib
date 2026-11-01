/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Dimension.ProperImage
public import Aglib.AlgebraicGeometry.Dimension.QuasiFiniteSurjective
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.Dimension
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-!
# A finite fibre determines the dimension of a proper image

Locally quasi-finite maps preserve strict specialization chains, so source
dimension is at most target dimension. For a proper map from a nonempty
scheme smooth of relative dimension n over a field, one finite actual point
fibre gives a nonempty finite neighborhood in its original schematic image.
The source open still has dimension n. Combining the two inequalities makes
the actual schematic image n-dimensional, without any separability premise.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Hom

attribute [local instance] specializationOrder

/-- A locally quasi-finite morphism cannot collapse a strict specialization
chain, giving this one-sided dimension inequality for the actual schemes. -/
theorem topologicalKrullDim_source_le_of_locallyQuasiFinite
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f] :
    topologicalKrullDim X ≤ topologicalKrullDim Y := by
  rw [topologicalKrullDim, topologicalKrullDim,
    Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X)),
    Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := Y))]
  exact Order.krullDim_le_of_strictMono f f.strictMono_of_locallyQuasiFinite

/-- A proper map from a scheme smooth of relative dimension n over a field
has n-dimensional schematic image if one actual point fibre through a
source point is finite. No reduced-fibre or birationality assertion is made. -/
theorem topologicalKrullDim_image_eq_of_smooth_of_finite_fibre
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n p]
    (f : X ⟶ Y) [IsProper f] (x : X) (hx : (f ⁻¹' {f x}).Finite) :
    topologicalKrullDim f.image = n := by
  have : Nonempty X := ⟨x⟩
  have hX : topologicalKrullDim X = n :=
    smoothFieldDimension k X p n inferInstance inferInstance
  have hupper : topologicalKrullDim f.image ≤ n := f.topologicalKrullDim_image_le.trans hX.le
  have : IsProper f.toImage := isProper_toImage f
  have hfinite : (f.toImage ⁻¹' {f.toImage x}).Finite := hx.subset (by
    intro z hz
    change f z = f x
    change f.toImage z = f.toImage x at hz
    have h := congrArg f.imageι hz
    simpa only [← Scheme.Hom.comp_apply, f.toImage_imageι] using h)
  obtain ⟨U, hxU, hU⟩ :=
    exists_isFinite_morphismRestrict_of_finite_preimage_singleton f.toImage (f.toImage x) hfinite
  let V := f.toImage ⁻¹ᵁ U
  have : Nonempty V.toScheme := ⟨⟨x, hxU⟩⟩
  have hVsmooth : SmoothOfRelativeDimension n (V.ι ≫ p) := by
    simpa only [Nat.zero_add] using smoothOfRelativeDimension_comp 0 n V.ι p
  have hV : topologicalKrullDim V.toScheme = n :=
    smoothFieldDimension k V.toScheme (V.ι ≫ p) n hVsmooth inferInstance
  have : IsFinite (f.toImage ∣_ U) := hU
  have hlower : (n : WithBot ℕ∞) ≤ topologicalKrullDim U.toScheme := by
    rw [← hV]
    exact topologicalKrullDim_source_le_of_locallyQuasiFinite (f.toImage ∣_ U)
  exact le_antisymm hupper (hlower.trans (topologicalKrullDim_subspace_le f.image U))

end AlgebraicGeometry.Scheme.Hom
