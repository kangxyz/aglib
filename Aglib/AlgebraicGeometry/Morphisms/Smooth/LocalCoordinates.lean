/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.RingHom.StandardSmooth

/-!
# Actual local polynomial coordinates for smooth morphisms

The native standard-smooth theorem supplies an etale polynomial coordinate
map near every point over an arbitrary base. The affine source and target,
the relative dimension of each chart, and the exact structural triangle are
retained. These source charts form an actual open cover. No uniform relative
dimension, field, Noetherianity, or cohomological hypothesis is imposed.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.SmoothLocalCoordinates

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Actual affine coordinates near a point, including the original ring-map
triangle. The coordinate dimension may vary with the point. -/
structure Chart (x : X) where
  /-- The affine open subset of the target. -/
  targetOpen : Y.Opens
  isAffine_target : IsAffineOpen targetOpen
  /-- The affine open subset of the source containing the point. -/
  sourceOpen : X.Opens
  isAffine_source : IsAffineOpen sourceOpen
  mem_source : x ∈ sourceOpen
  mapsTo : sourceOpen ≤ f ⁻¹ᵁ targetOpen
  /-- The number of polynomial coordinates in this chart. -/
  dimension : ℕ
  /-- The original etale polynomial-coordinate ring map. -/
  coordinate : MvPolynomial (Fin dimension) Γ(Y, targetOpen) →+* Γ(X, sourceOpen)
  coordinate_comp_C : coordinate.comp MvPolynomial.C =
    (f.appLE targetOpen sourceOpen mapsTo).hom
  coordinate_etale : coordinate.Etale

variable {f}

/-- Smoothness supplies the actual affine coordinate data at every point. -/
theorem nonempty_chart [Smooth f] (x : X) : Nonempty (Chart f x) := by
  obtain ⟨U, hU, V, hV, hx, e, hf⟩ := Smooth.exists_isStandardSmooth f x
  obtain ⟨n, g, hg, hge⟩ := hf.exists_etale_mvPolynomial
  exact ⟨⟨U, hU, V, hV, hx, e, n, g, hg, hge⟩⟩

/-- A fixed relative dimension can be retained in the same actual chart data. -/
theorem exists_chart_of_smoothOfRelativeDimension (n : ℕ)
    [SmoothOfRelativeDimension n f] (x : X) :
    ∃ c : Chart f x, c.dimension = n := by
  obtain ⟨U, hU, V, hV, hx, e, hf⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (f := f) (n := n) x
  obtain ⟨g, hg, hge⟩ := hf.exists_etale_mvPolynomial
  exact ⟨⟨U, hU, V, hV, hx, e, n, g, hg, hge⟩, rfl⟩

namespace Chart

variable {x : X} (c : Chart f x)

/-- The actual affine source chart inclusion. -/
def sourceMap : Spec Γ(X, c.sourceOpen) ⟶ X := c.isAffine_source.fromSpec

/-- The actual affine base chart inclusion. -/
def targetMap : Spec Γ(Y, c.targetOpen) ⟶ Y := c.isAffine_target.fromSpec

/-- The etale coordinate map is exactly the spectrum of the displayed ring map. -/
def coordinateMap : Spec Γ(X, c.sourceOpen) ⟶
    Spec (.of (MvPolynomial (Fin c.dimension) Γ(Y, c.targetOpen))) :=
  Spec.map (CommRingCat.ofHom c.coordinate)

/-- The polynomial structural map over the actual affine base chart. -/
def projection : Spec (.of (MvPolynomial (Fin c.dimension) Γ(Y, c.targetOpen))) ⟶
    Spec Γ(Y, c.targetOpen) :=
  Spec.map (CommRingCat.ofHom MvPolynomial.C)

instance sourceMap_isOpenImmersion : IsOpenImmersion c.sourceMap := by
  dsimp [sourceMap]
  infer_instance

instance targetMap_isOpenImmersion : IsOpenImmersion c.targetMap := by
  dsimp [targetMap]
  infer_instance

instance coordinateMap_etale : Etale c.coordinateMap :=
  HasRingHomProperty.Spec_iff.mpr c.coordinate_etale

/-- The chosen source inclusion contains the point it charts. -/
theorem mem_range_sourceMap : x ∈ Set.range c.sourceMap := by
  rw [sourceMap, c.isAffine_source.range_fromSpec]
  exact c.mem_source

/-- The original coordinate factorization over the whole base, with no
replacement of either structural map. -/
@[reassoc]
theorem factorization :
    c.coordinateMap ≫ c.projection ≫ c.targetMap = c.sourceMap ≫ f := by
  have hcomp :
      CommRingCat.ofHom (MvPolynomial.C : Γ(Y, c.targetOpen) →+*
        MvPolynomial (Fin c.dimension) Γ(Y, c.targetOpen)) ≫
          CommRingCat.ofHom c.coordinate = f.appLE c.targetOpen c.sourceOpen c.mapsTo := by
    ext a
    exact DFunLike.congr_fun c.coordinate_comp_C a
  dsimp only [coordinateMap, projection, targetMap, sourceMap]
  rw [← Spec.map_comp_assoc, hcomp]
  exact IsAffineOpen.SpecMap_appLE_fromSpec f c.isAffine_target c.isAffine_source c.mapsTo

end Chart

variable (f) [Smooth f]

/-- A choice of actual coordinates at each source point of a smooth morphism. -/
def chart (x : X) : Chart f x := Classical.choice (nonempty_chart (f := f) x)

/-- The spectra of the actual smooth coordinate rings form an open cover. -/
def openCover : X.OpenCover where
  I₀ := X
  X x := Spec Γ(X, (chart f x).sourceOpen)
  f x := (chart f x).sourceMap
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    exact ⟨fun x => ⟨x, (chart f x).mem_range_sourceMap⟩, inferInstance⟩

instance openCover_isAffine (x : X) : IsAffine ((openCover f).X x) := by
  change IsAffine (Spec Γ(X, (chart f x).sourceOpen))
  infer_instance

/-- Every member of the actual source cover has its exact etale-polynomial
factorization over the original base. -/
@[reassoc]
theorem openCover_structure (x : X) :
    (chart f x).coordinateMap ≫ (chart f x).projection ≫ (chart f x).targetMap =
      (openCover f).f x ≫ f :=
  (chart f x).factorization

end AlgebraicGeometry.Scheme.SmoothLocalCoordinates
