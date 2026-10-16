/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.KProjective.Representatives


/-!
# Actual comparisons between K-projective replacements

Maps from K-projective complexes lift across actual quasi-isomorphisms with
actual homotopies, homotopies cancel after quasi-isomorphisms, and two genuine
K-projective resolutions of one complex are chain-homotopy equivalent.
-/
/-!
Source: frozen dirty Quillen `6db56ddd3fdb898ef5de29d5fe51a0c61f9ba116`.
`Quillen/Algebra/Homology/KProjectiveComparison.lean`.
SHA-256: `7a9116acae3fbe93ddf08c08c646984432813822ef34c3b9a3c3ba17f75a870f`.
Selected source lines: 1–67.
Actual source objects, maps, hypotheses and independent universes are preserved.
-/

@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A map from an actual K-projective complex lifts across a quasi-isomorphism,
with an actual chain homotopy witnessing the triangle. -/
theorem exists_lift_quasiIso_up_to_homotopy {P Q K : CochainComplex C ℤ}
    [P.IsKProjective] (q : Q ⟶ K) [QuasiIso q] (a : P ⟶ K) :
    ∃ g : P ⟶ Q, Nonempty (Homotopy (g ≫ q) a) := by
  let := HasDerivedCategory.standard C
  obtain ⟨g, hg⟩ := exists_chain_representative_of_isKProjective
    (DerivedCategory.Q.map a ≫ inv (DerivedCategory.Q.map q))
  refine ⟨g, ⟨homotopyOfDerivedEqOfIsKProjective (g ≫ q) a ?_⟩⟩
  rw [Functor.map_comp, hg]
  simp

/-- Homotopies after a quasi-isomorphism cancel for actual K-projective sources. -/
def homotopyOfCompQuasiIso {P Q K : CochainComplex C ℤ}
    [P.IsKProjective] (q : Q ⟶ K) [QuasiIso q] (g h : P ⟶ Q)
    (H : Homotopy (g ≫ q) (h ≫ q)) : Homotopy g h := by
  let := HasDerivedCategory.standard C
  apply homotopyOfDerivedEqOfIsKProjective
  apply (cancel_mono (DerivedCategory.Q.map q)).mp
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact DerivedCategory.Q_map_eq_of_homotopy C H

/-- Any two actual K-projective resolutions of the same complex admit a comparison
which is a genuine chain homotopy equivalence. -/
theorem exists_homotopyEquiv_comparison {P Q K : CochainComplex C ℤ}
    [P.IsKProjective] [Q.IsKProjective] (p : P ⟶ K) (q : Q ⟶ K)
    [QuasiIso p] [QuasiIso q] :
    ∃ e : HomotopyEquiv P Q, Nonempty (Homotopy (e.hom ≫ q) p) := by
  obtain ⟨g, ⟨H⟩⟩ := exists_lift_quasiIso_up_to_homotopy q p
  have : QuasiIso (g ≫ q) := by
    rw [quasiIso_iff]
    intro n
    rw [quasiIsoAt_iff_isIso_homologyMap, H.homologyMap_eq n]
    infer_instance
  have : QuasiIso g := (quasiIso_iff_comp_right g q).mp inferInstance
  obtain ⟨e, he⟩ := (CochainComplex.IsKProjective.quasiIso_iff g).mp inferInstance
  exact ⟨e, ⟨he.symm ▸ H⟩⟩

end CochainComplex
