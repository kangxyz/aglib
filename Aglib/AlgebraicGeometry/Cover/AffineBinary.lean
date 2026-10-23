/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Two affine opens with affine intersection

The actual opens, their affine intersection and their covering equation
are retained. Inverse image along an affine morphism preserves these data.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme

universe u

/-- An actual cover by two affine opens whose intersection is affine. -/
structure AffineBinaryCover (X : Scheme.{u}) where
  /-- The first original open. -/
  first : X.Opens
  /-- The second original open. -/
  second : X.Opens
  /-- The first chart is affine. -/
  affineFirst : IsAffineOpen first
  /-- The second chart is affine. -/
  affineSecond : IsAffineOpen second
  /-- The actual open intersection is affine. -/
  affineIntersection : IsAffineOpen (first ⊓ second)
  /-- The two original opens cover the scheme. -/
  covers : first ⊔ second = ⊤

namespace AffineBinaryCover

variable {X Y : Scheme.{u}} (A : AffineBinaryCover X)

/-- The original two-open family, indexed by `Bool`. -/
def opens : Bool → X.Opens
  | false => A.first
  | true => A.second

/-- Each original member of the binary family is affine. -/
theorem affine (b : Bool) : IsAffineOpen (A.opens b) := by
  cases b
  · exact A.affineFirst
  · exact A.affineSecond

/-- The original binary family covers the scheme. -/
theorem isOpenCover : IsOpenCover A.opens := by
  apply IsOpenCover.mk
  apply top_le_iff.mp
  intro x _
  have hx : x ∈ A.first ⊔ A.second := by rw [A.covers]; trivial
  rcases hx with h | h
  · exact Opens.mem_iSup.mpr ⟨false, h⟩
  · exact Opens.mem_iSup.mpr ⟨true, h⟩

/-- Pull the actual opens and covering equation back along an affine map. -/
def pullback (g : Y ⟶ X) [IsAffineHom g] : AffineBinaryCover Y where
  first := g ⁻¹ᵁ A.first
  second := g ⁻¹ᵁ A.second
  affineFirst := A.affineFirst.preimage g
  affineSecond := A.affineSecond.preimage g
  affineIntersection := A.affineIntersection.preimage g
  covers := by rw [← Hom.preimage_sup, A.covers, Hom.preimage_top]

/-- The actual categorical intersection of the two chart immersions is affine. -/
theorem affinePullback : IsAffine (Limits.pullback A.first.ι A.second.ι) := by
  let : IsAffine (A.first ⊓ A.second).toScheme := A.affineIntersection
  exact IsAffine.of_isIso (isPullback_opens_inf A.first A.second).isoPullback.inv

end AffineBinaryCover

end AlgebraicGeometry.Scheme
