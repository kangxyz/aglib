/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Properties.Noetherian.LocallyNoetherianOver
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Disjoint unions of locally Noetherian schemes

* `AlgebraicGeometry.isLocallyNoetherian_sigma`: a disjoint union `∐ g` of locally Noetherian
  schemes, over a small index type in any universe, is locally Noetherian. It is covered by the
  open subschemes `g j` (Mathlib's `sigmaOpenCover`), and local Noetherianity is local on open
  covers (Mathlib's `isLocallyNoetherian_iff_openCover`).
* `AlgebraicGeometry.Scheme.LocallyNoetherianOver.sigma`: hence the disjoint union of a family
  `H` of locally Noetherian test schemes over `S` is a locally Noetherian test scheme over `S`, with
  structure morphism `Sigma.desc fun j => (H j).obj.hom`; `LocallyNoetherianOver.sigmaι` is the
  inclusion of `H j`.

Present consumer: the scheme `∐_{Φ ∈ F} Hilb^Φ_Y` representing the Hilbert functor of an immersed
scheme with Hilbert polynomials in a set `F` (`HilbertScheme/Coproduct/Representability`).
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace AlgebraicGeometry

/-- **A disjoint union of locally Noetherian schemes is locally Noetherian**: `∐ g` is covered by
the open subschemes `g j` (`sigmaOpenCover`). -/
instance isLocallyNoetherian_sigma {σ : Type v} [Small.{u} σ] (g : σ → Scheme.{u})
    [∀ j, IsLocallyNoetherian (g j)] : IsLocallyNoetherian (∐ g) :=
  (isLocallyNoetherian_iff_openCover (sigmaOpenCover g)).mpr fun (j : σ) => by
    have h : IsLocallyNoetherian (g j) := inferInstance
    exact h

namespace Scheme.LocallyNoetherianOver

variable {S : Scheme.{u}} {σ : Type v} [Small.{u} σ] (H : σ → LocallyNoetherianOver S)

/-- **The disjoint union of locally Noetherian test schemes over `S`**: `∐ j, H j` with structure
morphism `Sigma.desc fun j => (H j).obj.hom`, locally Noetherian by `isLocallyNoetherian_sigma`. -/
def sigma : LocallyNoetherianOver S :=
  ⟨Over.mk (Sigma.desc fun j => (H j).obj.hom),
    isLocallyNoetherian_sigma fun j => (H j).obj.left⟩

/-- The inclusion `H j ⟶ ∐ H` of locally Noetherian test schemes over `S`. -/
def sigmaι (j : σ) : H j ⟶ sigma H :=
  ObjectProperty.homMk (Over.homMk (Sigma.ι (fun j => (H j).obj.left) j) (Sigma.ι_comp_desc _ _))

@[simp]
theorem sigmaι_hom_left (j : σ) :
    (sigmaι H j).hom.left = Sigma.ι (fun j => (H j).obj.left) j :=
  rfl

end Scheme.LocallyNoetherianOver

end AlgebraicGeometry
