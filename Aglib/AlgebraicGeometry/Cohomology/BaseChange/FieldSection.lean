/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Field
public import Aglib.AlgebraicGeometry.ResidueField.Constants

/-!
# Sections of a field base change from points

Let `k` be a field, `X : FScheme k` and `K` a field over `k`, with the base change
`X_K = fieldBaseChange K X ⟶ Spec K`.

* A `K`-point `s : Spec K ⟶ X` over `k` (`s ≫ X.hom = Spec (algebraMap k K)`) gives the section
  `(s, 𝟙)` of `X_K ⟶ Spec K` (`isSplitEpi_fieldBaseChange_hom`).
* Every point `x` of a scheme `X` over `Spec k` is such a point for its residue field: with the
  `k`-algebra structure of `κ(x)` induced by the structure morphism (`Scheme.residueAlgebra`),
  `Spec κ(x) ⟶ X ⟶ Spec k` is `Spec (algebraMap k κ(x))`
  (`fromSpecResidueField_comp_eq_spec_map_algebraMap`).
* Hence every point `x` of `X` gives a field `K = κ(x)` over `k` such that `X_K ⟶ Spec K` has a
  section (`exists_isSplitEpi_fieldBaseChange_hom`). No finiteness of `κ(x)` over `k` is needed.

The current consumer is `Picard/Tangent/StructureCohomology`, which applies Kleiman's Thm 2.5(2)
(*The Picard scheme*, arXiv:math/0504020v1, p. 18) to `X_K` in place of the passage to an
algebraically closed field on p. 44.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.OverField

universe u

namespace AlgebraicGeometry.Scheme

variable {k : Type u} [Field k]

/-- `Spec κ(x) ⟶ X ⟶ Spec k` is `Spec` of the `k`-algebra structure of `κ(x)` induced by the
structure morphism `p` (`Scheme.residueAlgebra`). -/
theorem fromSpecResidueField_comp_eq_spec_map_algebraMap (X : Scheme.{u})
    (p : X ⟶ Spec (.of k)) (x : X) :
    letI := residueAlgebra X p x
    X.fromSpecResidueField x ≫ p =
      Spec.map (CommRingCat.ofHom (algebraMap k (X.residueField x))) :=
  (Spec.map_preimage (X.fromSpecResidueField x ≫ p)).symm

namespace Cohomology

variable (X : FScheme k)

/-- **A `K`-point gives a section of the base change**: for `s : Spec K ⟶ X` over `k`, the
morphism `(s, 𝟙) : Spec K ⟶ X_K` is a section of `X_K ⟶ Spec K`. -/
theorem isSplitEpi_fieldBaseChange_hom {K : Type u} [Field K] [Algebra k K]
    {s : Spec (.of K) ⟶ X.left}
    (hs : s ≫ X.hom = Spec.map (CommRingCat.ofHom (algebraMap k K))) :
    IsSplitEpi (fieldBaseChange K X).hom :=
  IsSplitEpi.mk' ⟨pullback.lift s (𝟙 _) (hs.trans (Category.id_comp _).symm),
    pullback.lift_snd _ _ _⟩

/-- **Every point gives a section after a field extension**: for a point `x` of `X`, the base
change of `X` to `K = κ(x)` (a `k`-algebra through the structure morphism) has a section. -/
theorem exists_isSplitEpi_fieldBaseChange_hom (x : X.left) :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K), IsSplitEpi (fieldBaseChange K X).hom := by
  let := residueAlgebra X.left X.hom x
  exact ⟨X.left.residueField x, inferInstance, inferInstance,
    isSplitEpi_fieldBaseChange_hom X (s := X.left.fromSpecResidueField x)
      (fromSpecResidueField_comp_eq_spec_map_algebraMap X.left X.hom x)⟩

end Cohomology

end AlgebraicGeometry.Scheme
