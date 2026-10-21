/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Adic.Residue
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.ResidueLift

/-!
# Finite etale residue equivalence for complete Noetherian local rings

The existing complete-base fullness theorem combines with faithfulness and
essential surjectivity of residue base change. The resulting equivalences use
the literal native finite-etale base-change functors, both for the residue
quotient and for an explicitly marked residue field.

The Noetherian and maximal-ideal-adic completeness hypotheses remain explicit.
This is a comparison over the base spectrum, not a proper-scheme comparison.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

namespace AlgebraicGeometry.Scheme.FiniteEtale.Adic

universe u

variable (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  [IsAdicComplete (maximalIdeal R) R]

/-- The actual residue base-change functor is an equivalence for a complete
Noetherian local ring. Fullness is the existing adic homomorphism-lifting
theorem; faithfulness and essential surjectivity need only locality. -/
instance residue_baseChange_isEquivalence :
    (baseChange (LocalRing.residueSpecMap R)).IsEquivalence where
  full := by
    change (baseChange (Spec.algebraMap R (R ⧸ maximalIdeal R))).Full
    exact quotient_baseChange_full R (maximalIdeal R)

/-- Finite etale covers of a complete Noetherian local spectrum are equivalent
to finite etale covers of its actual residue spectrum. -/
def residueEquivalence :
    FiniteEtale (Spec (.of R)) ≌ FiniteEtale (Spec (.of (ResidueField R))) :=
  (baseChange (LocalRing.residueSpecMap R)).asEquivalence

@[simp]
theorem residueEquivalence_functor :
    (residueEquivalence R).functor = baseChange (LocalRing.residueSpecMap R) := rfl

/-- The equivalence's forward object retains the literal pullback projection. -/
@[simp]
theorem residueEquivalence_functor_obj_hom (Y : FiniteEtale (Spec (.of R))) :
    ((residueEquivalence R).functor.obj Y).obj.hom =
      pullback.snd Y.obj.hom (LocalRing.residueSpecMap R) := rfl

/-- The forward morphism is the native pullback map, with its original first
projection equation. -/
@[reassoc]
theorem residueEquivalence_functor_map_fst {Y Z : FiniteEtale (Spec (.of R))}
    (f : Y ⟶ Z) :
    ((residueEquivalence R).functor.map f).hom.left ≫
        pullback.fst Z.obj.hom (LocalRing.residueSpecMap R) =
      pullback.fst Y.obj.hom (LocalRing.residueSpecMap R) ≫ f.hom.left :=
  pullback.lift_fst _ _ _

/-- The same equivalence property for the exact residue quotient followed by
the supplied ring equivalence to the marked residue field. -/
theorem marked_closed_isEquivalence {F : Type u} [Field F] (e : ResidueField R ≃+* F) :
    (baseChange (Spec.map (CommRingCat.ofHom
      (e.toRingHom.comp (IsLocalRing.residue R))))).IsEquivalence := by
  let c := LocalRing.residueSpecMap R
  let j : Spec (.of F) ⟶ Spec (.of (ResidueField R)) :=
    Spec.map (CommRingCat.ofHom e.toRingHom)
  have : IsIso (CommRingCat.ofHom e.toRingHom) := by
    change IsIso e.toCommRingCatIso.hom
    infer_instance
  have : IsIso j := by
    dsimp only [j]
    infer_instance
  have : (baseChange c).IsEquivalence := residue_baseChange_isEquivalence R
  have : (baseChange j).Faithful := baseChange_faithful_of_isIso j
  let ej : baseChange (inv j) ⋙ baseChange j ≅ 𝟭 (FiniteEtale (Spec (.of F))) :=
    (baseChangeComp (inv j) j).symm ≪≫
      eqToIso (congrArg baseChange (IsIso.hom_inv_id j)) ≪≫ baseChangeId _
  have : (baseChange j).EssSurj :=
    ⟨fun Y ↦ ⟨(baseChange (inv j)).obj Y, ⟨ej.app Y⟩⟩⟩
  have he : j ≫ c = Spec.map (CommRingCat.ofHom
      (e.toRingHom.comp (IsLocalRing.residue R))) := by
    dsimp only [j, c, LocalRing.residueSpecMap]
    rw [← Spec.map_comp]
    rfl
  have hfaith : (baseChange (j ≫ c)).Faithful :=
    Functor.Faithful.of_iso (baseChangeComp c j).symm
  have hess : (baseChange (j ≫ c)).EssSurj :=
    Functor.essSurj_of_iso (baseChangeComp c j).symm
  rw [he] at hfaith hess
  exact ⟨hfaith, marked_closed_full R e, hess⟩

/-- The equivalence with a marked residue field, using the literal composite
ring map in its forward base-change functor. -/
def markedClosedEquivalence {F : Type u} [Field F] (e : ResidueField R ≃+* F) :
    FiniteEtale (Spec (.of R)) ≌ FiniteEtale (Spec (.of F)) := by
  let : (baseChange (Spec.map (CommRingCat.ofHom
    (e.toRingHom.comp (IsLocalRing.residue R))))).IsEquivalence :=
      marked_closed_isEquivalence R e
  exact (baseChange (Spec.map (CommRingCat.ofHom
    (e.toRingHom.comp (IsLocalRing.residue R))))).asEquivalence

@[simp]
theorem markedClosedEquivalence_functor {F : Type u} [Field F]
    (e : ResidueField R ≃+* F) :
    (markedClosedEquivalence R e).functor =
      baseChange (Spec.map (CommRingCat.ofHom
        (e.toRingHom.comp (IsLocalRing.residue R)))) := rfl

end AlgebraicGeometry.Scheme.FiniteEtale.Adic
