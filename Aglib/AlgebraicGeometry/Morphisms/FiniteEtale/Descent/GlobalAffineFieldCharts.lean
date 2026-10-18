/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.GlobalFinitePureAffineEquivalence

/-!
# GlobalAffineFieldCharts

General constructions and comparisons for this native mathematical family.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (baseChange baseChangeComp baseChangeId)

namespace AlgebraicGeometry.Scheme.FiniteEtale.PurelyInseparable.Global

universe u

/-- Base change along a scheme isomorphism, with the actual base-change functor. -/
def baseChangeIsoEquivalence {X Y : Scheme.{u}} (e : X
    ≅ Y) : Scheme.FiniteEtale Y ≌ Scheme.FiniteEtale X :=
  CategoryTheory.Equivalence.mk (baseChange e.hom) (baseChange e.inv)
    ((baseChangeId Y).symm ≪≫
      eqToIso (congrArg (fun f : Y ⟶ Y ↦ baseChange f) e.inv_hom_id.symm) ≪≫
      baseChangeComp e.hom e.inv)
    ((baseChangeComp e.inv e.hom).symm ≪≫
      eqToIso (congrArg (fun f : X ⟶ X ↦ baseChange f) e.hom_inv_id) ≪≫
      baseChangeId X)

/-- The base-change functor isomorphism associated to the supplied commutative square with
isomorphic sides. -/
def baseChangeIsoSquare {X X' T T' : Scheme.{u}} (eT : T' ≅ T) (eX : X' ≅ X)
    (f : T ⟶ X) (g : T' ⟶ X') (h : eT.hom ≫ f = g ≫ eX.hom) :
    baseChange f ≅ baseChange eX.hom ⋙ baseChange g ⋙ baseChange eT.inv := by
  have H : eT.inv ≫ g ≫ eX.hom = f := by rw [← h, eT.inv_hom_id_assoc]
  exact eqToIso (congrArg (fun k : T ⟶ X ↦ baseChange k) H.symm) ≪≫
    baseChangeComp (g ≫ eX.hom) eT.inv ≪≫
    Functor.isoWhiskerRight (baseChangeComp eX.hom g) (baseChange eT.inv) ≪≫
    Functor.associator _ _ _

theorem baseChange_isEquivalence_of_isoSquare {X X' T T' : Scheme.{u}}
    (eT : T' ≅ T) (eX : X' ≅ X) (f : T ⟶ X) (g : T' ⟶ X')
    (h : eT.hom ≫ f = g ≫ eX.hom) [(baseChange g).IsEquivalence] :
    (baseChange f).IsEquivalence := by
  let : (baseChange eX.hom).IsEquivalence := (baseChangeIsoEquivalence eX).isEquivalence_functor
  let : (baseChange eT.inv).IsEquivalence := (baseChangeIsoEquivalence
    eT.symm).isEquivalence_functor
  exact Functor.isEquivalence_of_iso (baseChangeIsoSquare eT eX f g h).symm

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [IsPurelyInseparable K L] [Module.Finite K L]

/-- Actual finite purely inseparable cover equivalence on every affine scheme,
independently of a chosen Spec presentation of that scheme. -/
theorem affineFieldProjection_isEquivalence {X : Scheme.{u}} [IsAffine X]
    (p : X ⟶ Spec (CommRingCat.of K)) :
    (baseChange (pullback.fst p (Spec.algebraMap K L))).IsEquivalence := by
  let R := Γ(X, ⊤)
  let a : K →+* R := ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ p.appTop).hom
  let : Algebra K R := a.toAlgebra
  let eX : Spec (CommRingCat.of R) ≅ X := X.isoSpec.symm
  have hX : eX.hom ≫ p = Spec.algebraMap K R := by
    change X.isoSpec.inv ≫ p = Spec.algebraMap K R
    rw [← Scheme.isoSpec_inv_naturality, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
    rfl
  let q := pullback.map (Spec.algebraMap K R) (Spec.algebraMap K L)
    p (Spec.algebraMap K L) eX.hom (𝟙 _) (𝟙 _) (by simpa using hX.symm) (by simp)
  let : IsIso q := by dsimp [q]; infer_instance
  let eT : Spec (CommRingCat.of (R ⊗[K] L)) ≅ pullback p (Spec.algebraMap K L) :=
    (pullbackSpecIso K R L).symm ≪≫ asIso q
  have hT : eT.hom ≫ pullback.fst p (Spec.algebraMap K L) =
      Spec.algebraMap R (R ⊗[K] L) ≫ eX.hom := by
    simp only [eT, Iso.trans_hom, Iso.symm_hom, asIso_hom, q, Category.assoc,
      pullback.map, pullback.lift_fst, pullbackSpecIso_inv_fst'_assoc]
  let : (baseChange (Spec.algebraMap R (R ⊗[K] L))).IsEquivalence :=
    (affinePureEquivalence K L R).isEquivalence_functor
  exact baseChange_isEquivalence_of_isoSquare eT eX _ _ hT

end AlgebraicGeometry.Scheme.FiniteEtale.PurelyInseparable.Global

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 8ebbcd21c383482cebfb9acf83d2d3009fce474ad326051fd973df7194e0b440.
Definitions, hypotheses and universes are retained modulo native names. -/
