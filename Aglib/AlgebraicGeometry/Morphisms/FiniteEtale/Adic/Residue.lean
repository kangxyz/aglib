/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Adic.Fullness
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.BaseChange.Isomorphism

/-!
# Marked residue-field pullback on finite-etale covers
-/

@[expose] public section


noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

namespace AlgebraicGeometry.Scheme.FiniteEtale.Adic
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (baseChange baseChangeComp baseChangeId)
universe u

variable (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
  [IsAdicComplete (maximalIdeal R) R]

/-- Fullness for the actual closed map with any residue-field marking. -/
theorem marked_closed_full {F : Type u} [Field F] (e : ResidueField R ≃+* F) :
    (baseChange (Spec.map (CommRingCat.ofHom
      (e.toRingHom.comp (IsLocalRing.residue R))))).Full := by
  let c : Spec (.of (ResidueField R)) ⟶ Spec (.of R) :=
    Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
  let j : Spec (.of F) ⟶ Spec (.of (ResidueField R)) :=
    Spec.map (CommRingCat.ofHom e.toRingHom)
  have : (baseChange c).Full := by
    change (baseChange (Spec.algebraMap R (R ⧸ maximalIdeal R))).Full
    exact quotient_baseChange_full R (maximalIdeal R)
  have : IsIso (CommRingCat.ofHom e.toRingHom) := by
    change IsIso e.toCommRingCatIso.hom
    infer_instance
  have : IsIso j := by
    change IsIso (Spec.map e.toCommRingCatIso.hom)
    infer_instance
  have : (baseChange j).Full := Scheme.FiniteEtale.baseChange_full_of_isIso j
  have he : j ≫ c = Spec.map (CommRingCat.ofHom
      (e.toRingHom.comp (IsLocalRing.residue R))) := by
    dsimp only [j, c]
    rw [← Spec.map_comp]
    rfl
  rw [← he]
  exact Functor.Full.of_iso (baseChangeComp c j).symm

end AlgebraicGeometry.Scheme.FiniteEtale.Adic

/- Migration source: R5Lab/Aglib/AlgebraicGeometry/Morphisms/FiniteEtale/Adic/Residue.lean
Frozen packet R5 f8a3314ddecffcada2ec721d26d56a937bed9690.
SHA-256 dc29e19bd1e830ce9fc56fc683241de597a3bb4300d45078e47fd59b8fec5e3e.
Native names and imports replace the source wrappers; stated conditions and maps are retained. -/
