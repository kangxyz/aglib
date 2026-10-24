/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.LocalSplitting
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.SplitProjection

/-!
# Geometric fiber cardinality and the original finite-flat rank

The original finite etale cover splits locally with labels given by its
geometric fiber over an algebraic closure of the residue field. Comparing
that actual splitting with the actual coproduct projection identifies its
cardinality with the original scheme morphism's native `finrank`.
No connectedness hypothesis or coefficient-valued comparison is required.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.FiniteEtale

universe u

/-- The cardinality of the original geometric fiber at a base point equals
the original finite-flat rank at that point, even on a disconnected base. -/
theorem natCard_geometricFiber_eq_finrank {X : Scheme.{u}} (Y : Scheme.FiniteEtale X) (x : X) :
    Nat.card (Fiber (algebraicClosureResiduePoint X x) Y) = Y.obj.hom.finrank x := by
  obtain ⟨U, y, hy, ⟨e⟩, _⟩ := exists_etale_trivialization_at_point Y x
  let A := Fiber (algebraicClosureResiduePoint X x) Y
  have hprojection : (trivialCover U.left A).obj.hom =
      (trivialCoverSigmaIso U.left A).hom ≫ Scheme.SplitProjection.projection A U.left := by
    apply (isColimitOfHasCoproductOfPreservesColimit (forgetToScheme U.left)
      (fun _ : A => terminalCover U.left)).hom_ext
    intro a
    change (trivialCoverι U.left A a.as).hom.left ≫ (trivialCover U.left A).obj.hom =
      (trivialCoverι U.left A a.as).hom.left ≫
        (trivialCoverSigmaIso U.left A).hom ≫ Scheme.SplitProjection.projection A U.left
    rw [trivialCoverι_struct, ← Category.assoc, trivialCoverSigmaIso_ι]
    exact (Sigma.ι_comp_desc (fun _ : A => 𝟙 U.left) a.as).symm
  have he : IsIso e.hom.hom.left := inferInstance
  have h := congrArg (fun g : (trivialCover U.left A).obj.left ⟶ U.left => g.finrank y)
    (Over.w e.hom.hom)
  rw [Scheme.Hom.finrank_comp_left_of_isIso] at h
  change (pullback.snd Y.obj.hom U.hom).finrank y =
    (trivialCover U.left A).obj.hom.finrank y at h
  rw [Scheme.Hom.finrank_pullback_snd, hprojection,
    Scheme.Hom.finrank_comp_left_of_isIso, Scheme.SplitProjection.rank] at h
  exact h.symm.trans (congrArg (fun z : X => Y.obj.hom.finrank z) hy)

end AlgebraicGeometry.Scheme.FiniteEtale
