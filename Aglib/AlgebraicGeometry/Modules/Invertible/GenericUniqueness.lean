/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.RationalTrivialization


/-!
# Ordinary maps into a line are determined on a nonempty open

This is ordinary module-sheaf uniqueness on an integral scheme. It uses
injectivity of the original line-section restrictions and actual naturality.
It makes no assertion about equality of derived arrows from generic values.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules.Invertible

/-- Ordinary morphisms into an actual line agree globally if their original
restrictions to one nonempty open agree. The source need not be torsion-free. -/
theorem hom_ext_of_nonempty_over
    {X : Scheme.{u}} [IsIntegral X] {M N : X.Modules}
    (hN : IsLocallyRankOne X N) (U : X.Opens) [Nonempty U]
    {f g : M ⟶ N} (h : f.over U = g.over U) : f = g := by
  ext V m
  by_cases hV : Nonempty V
  · let : Nonempty V := hV
    let : Nonempty (V ⊓ U : X.Opens) :=
      RationalTrivialization.nonempty_inf X V U
    let i : V ⊓ U ⟶ V := homOfLE inf_le_left
    apply RationalTrivialization.restrict_injective X N hN i
    refine (PresheafOfModules.naturality_apply f.val i.op m).symm.trans
      (Eq.trans ?_ (PresheafOfModules.naturality_apply g.val i.op m))
    exact congrArg
      (fun q : M.over U ⟶ N.over U =>
        q.val.app (op (Over.mk (homOfLE (show V ⊓ U ≤ U from inf_le_right))))
          (M.val.map i.op m)) h
  · apply N.isSheaf.isSeparated V ⊥
    · intro x hx
      exact (hV ⟨⟨x, hx⟩⟩).elim
    · intro W i hi
      cases hi

end AlgebraicGeometry.Scheme.Modules.Invertible
