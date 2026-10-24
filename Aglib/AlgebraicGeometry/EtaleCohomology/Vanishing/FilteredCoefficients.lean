/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Torsion.QcqsComparison
public import Aglib.AlgebraicGeometry.EtaleCohomology.Torsion.Colimit

/-! # Passing vanishing from bounded coefficients to internal torsion

On a qcqs scheme, original cohomology commutes with the actual factorial
annihilator colimit. Thus vanishing proved for all positive uniform moduli
implies vanishing for arbitrary internally torsion abelian sheaves, without
assuming a global common annihilator. These are reduction theorems; the
fixed-modulus vanishing remains an explicit application obligation.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Vanishing

universe u e

attribute [local instance] hasSheafifyLarge

variable {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
  [HasExt.{e} (AbelianSheaf.{u, u + 1} X)]

/-- Vanishing on every actual factorial annihilator kernel implies vanishing
on the original internally torsion sheaf. The Ext universe remains arbitrary. -/
theorem subsingleton_H_of_factorialAnnihilators
    (F : AbelianSheaf.{u, u + 1} X) (hF : IsTorsion X F) (q : ℕ)
    (hstage : ∀ n, Subsingleton
      (Sheaf.H.{e} ((Sheaf.factorialAnnihilatorDiagram F).obj n) q)) :
    Subsingleton (Sheaf.H.{e} F q) := by
  let G := Sheaf.factorialAnnihilatorDiagram F
  let H := cohomologyFunctor.{u, e} X q
  let : PreservesColimitsOfShape ℕ H :=
    qcqsCohomologyFunctor_preservesSequentialColimits X q
  have hzero : IsZero (G ⋙ H) := by
    apply Functor.isZero
    intro n
    exact AddCommGrpCat.isZero_iff_subsingleton.mpr (hstage n)
  have hc : IsZero (colimit (G ⋙ H)) := (colimit.isColimit (G ⋙ H)).isZero_pt hzero
  have hcol : IsZero (H.obj (colimit G)) := hc.of_iso (preservesColimitIso H G)
  exact AddCommGrpCat.isZero_iff_subsingleton.mp
    (hcol.of_iso (H.mapIso (torsionFilteredColimitIso F hF)).symm)

/-- A vanishing theorem for every positive uniform modulus extends to arbitrary
internally torsion coefficients on a qcqs scheme through original cohomology. -/
theorem subsingleton_H_of_isTorsion_of_bounded
    (q : ℕ)
    (hbounded : ∀ (n : ℕ), 0 < n → ∀ G : AbelianSheaf.{u, u + 1} X,
      n • 𝟙 G = 0 → Subsingleton (Sheaf.H.{e} G q))
    (F : AbelianSheaf.{u, u + 1} X) (hF : IsTorsion X F) :
    Subsingleton (Sheaf.H.{e} F q) := by
  apply subsingleton_H_of_factorialAnnihilators F hF q
  intro n
  exact hbounded (n + 1).factorial (Nat.factorial_pos _)
    ((Sheaf.factorialAnnihilatorDiagram F).obj n)
    (Sheaf.factorialAnnihilatorDiagram_annihilated F n)

end AlgebraicGeometry.Scheme.EtaleCohomology.Vanishing
