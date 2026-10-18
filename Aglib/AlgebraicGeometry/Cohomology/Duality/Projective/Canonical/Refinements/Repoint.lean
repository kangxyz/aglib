/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.LocalCharts.Quotient

/-!
# Retaining a chart at any original source point in its range

Only the point and its image equation change. The original rings, regular
list, maps, Cartesian square and smooth presentations stay the same. This
allows two independently centered charts to use common-point refinements.
-/

@[expose] public section
noncomputable section

open CategoryTheory AlgebraicGeometry

universe u
namespace AlgebraicGeometry.Scheme.Modules.Differentials
namespace SmoothClosedImmersionLocalChart

variable {X P Y : Scheme.{u}} {i : X ⟶ P} {p : P ⟶ Y} {n d : ℕ} {x : X}

/-- The identical actual chart retained at another original point in its source. -/
def repoint (C : SmoothClosedImmersionLocalChart i p n d x)
    (y : X) (q : PrimeSpectrum C.B) (hq : C.jX q = y) :
    SmoothClosedImmersionLocalChart i p n d y where
  R := C.R
  A := C.A
  B := C.B
  α := C.α
  σ := C.σ
  surjective := C.surjective
  jY := C.jY
  jP := C.jP
  jX := C.jX
  openY := C.openY
  openP := C.openP
  openX := C.openX
  ambientSquare := C.ambientSquare
  closedSquare := C.closedSquare
  cartesian := C.cartesian
  point := q
  point_eq := hq
  regularList := C.regularList
  weaklyRegular := C.weaklyRegular
  kernel := C.kernel
  ambientSmooth := C.ambientSmooth
  sourceSmooth := C.sourceSmooth

end SmoothClosedImmersionLocalChart
end AlgebraicGeometry.Scheme.Modules.Differentials
