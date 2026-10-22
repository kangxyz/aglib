/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Approximation.FinitePresentationEnvelope.PreparedAffine

/-!
# Extending an arithmetic approximation by one affine open

An actual arithmetic system on a compact open extends across one affine chart
covering the original scheme together with that open. The overlap, finite
denominators, filtered pullback rings, eligible finite subalgebras, and native
glued limiting cone are all constructed internally.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.FinitePresentationEnvelope

universe u

/-- The single-affine extension step of absolute arithmetic approximation,
with the original union as the literal limiting scheme. -/
theorem nonempty_system_of_affine_open_union
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsCompact (V : Set X))
    (hcover : U ⊔ V = ⊤) (M : System V.toScheme) : Nonempty (System X) := by
  let : IsAffine U.toScheme := hU
  obtain ⟨P⟩ := nonempty_overlapPreparation U V M hV
  exact ⟨P.originalSystem hcover⟩

end AlgebraicGeometry.Scheme.FinitePresentationEnvelope
