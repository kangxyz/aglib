/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Limits.Clopen

/-!
# Clopen descent along affine inverse limits

Compatibility interface for the general scheme-limit clopen supplier.
Finite étale limit descent uses the same canonical inverse images.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open TopologicalSpace

namespace AlgebraicGeometry.Scheme.FiniteEtale.LimitDescent

universe u

variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
  [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
  [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]

include hc in
/-- Every clopen subset of a qcqs affine-transition limit descends to a clopen
subset of one stage. No surjectivity of the transition maps is assumed. -/
theorem exists_clopen_preimage_eq (U : c.pt.Opens)
    (hU : IsClosed (U : Set c.pt)) :
    ∃ (i : I) (V : (D.obj i).Opens),
      IsClosed (V : Set (D.obj i)) ∧ c.π.app i ⁻¹ᵁ V = U :=
  Scheme.exists_clopen_preimage_eq_of_isLimit D c hc U hU

end AlgebraicGeometry.Scheme.FiniteEtale.LimitDescent

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 755d4dd49c9b43fc0ca7330d7a9dc99cda88256f85801a0abcf4b06dfb7dd334.
Definitions, hypotheses and universes are retained modulo native names. -/
