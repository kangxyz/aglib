/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteCogenerators.Global.GenericModel
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteCogenerators.NormalGenericModel

/-! # Actual global normal models from original integral strata

Choose an actual affine open meeting the stratum generically. Its original
open pullback is integral and dominant, so the frozen affine normal-model
producer supplies the actual generic finite constant trivialization. The
whole-base normalization constructor retains its original generic point and
coefficient, with no finite-normalization or Noetherian assumption here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteCogenerators.Global

universe u

attribute [local instance] hasSheafifyLarge

/-- A frozen original affine normal model supplies the generic data for the
actual whole-base model, preserving the original cartesian stratum equation. -/
def globalNormalGenericModelOfAffineRestriction
    (R : Type u) [CommRing R] {T S X : Scheme.{u}}
    (j : Spec (.of R) ⟶ X) [IsOpenImmersion j] (s : S ⟶ X)
    (q : T ⟶ S) [IsDominant q] (t : T ⟶ Spec (.of R))
    (h : q ≫ s = t ≫ j) (F : AbelianSheaf.{u, u + 1} X)
    (m : NormalGenericModel R t ((inverseImage j).obj F)) :
    GlobalNormalGenericModel s F := by
  let C := Spec (.of m.ringType)
  let g := Spec.algebraMap R m.ringType
  have (x : C) : IsIntegrallyClosed (C.presheaf.stalk x) :=
    NormalGenericModel.integrallyClosed_stalk m x
  have : IsIntegralHom g := IsIntegralHom.SpecMap_iff.mpr
    (algebraMap_isIntegral_iff.mpr (inferInstanceAs (Algebra.IsIntegral R m.ringType)))
  let ζ := m.point ≫ q
  have hζ : ζ ≫ s = (C.fromSpecStalk (genericPoint C) ≫ g) ≫ j :=
    (Category.assoc m.point q s).trans
      ((congrArg (fun k => m.point ≫ k) h).trans
        ((Category.assoc m.point t j).symm.trans
          (congrArg (fun k => k ≫ j) m.over)))
  let eB : (inverseImage ((C.fromSpecStalk (genericPoint C) ≫ g) ≫ j)).obj F ≅
      ConstantFinite.coefficient m.value (Spec C.functionField) :=
    (inverseImageComp j (C.fromSpecStalk (genericPoint C) ≫ g)).app F ≪≫ m.trivialization
  exact globalNormalGenericModelOfIntegralChart g j s F m.value ζ hζ eB

/-- An actual integral immersed stratum with finite locally constant original
restriction has an actual normal integral global model. The normalization may
be infinite over the base. No Noetherian or finite-normalization premise is used. -/
theorem nonempty_globalNormalGenericModel {X S : Scheme.{u}} [IsIntegral S]
    (s : S ⟶ X) [IsImmersion s] (F : AbelianSheaf.{u, u + 1} X)
    (hF : IsFiniteLocallyConstant ((inverseImage s).obj F)) :
    Nonempty (GlobalNormalGenericModel s F) := by
  classical
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, _⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (s (genericPoint S))) isOpen_univ
  let R := Γ(X, U)
  let j : Spec R ⟶ X := hU.fromSpec
  have : IsOpenImmersion j := IsAffineOpen.isOpenImmersion_fromSpec hU
  have hxrange : s (genericPoint S) ∈ Set.range j := by
    change s (genericPoint S) ∈ Set.range hU.fromSpec
    rw [hU.range_fromSpec]
    exact hxU
  obtain ⟨u, hu⟩ := hxrange
  obtain ⟨z, _, _⟩ := Scheme.Pullback.exists_preimage_pullback (genericPoint S) u hu.symm
  let T : Scheme.{u} := pullback s j
  have : Nonempty T := ⟨z⟩
  let q : T ⟶ S := pullback.fst s j
  let t : T ⟶ Spec R := pullback.snd s j
  have : IsIntegral T := isIntegral_of_isOpenImmersion q
  have : IsDominant q := Scheme.isDominant_of_isOpenImmersion q
  have hsq : q ≫ s = t ≫ j := pullback.condition
  let e : (inverseImage t).obj ((inverseImage j).obj F) ≅
      (inverseImage q).obj ((inverseImage s).obj F) :=
    ((inverseImageComp j t).app F).symm ≪≫
      eqToIso (congrArg (fun k => (inverseImage k).obj F) hsq.symm) ≪≫
        (inverseImageComp s q).app F
  have hFt : IsFiniteLocallyConstant ((inverseImage t).obj ((inverseImage j).obj F)) :=
    (isFiniteLocallyConstant_iff_of_iso e).mpr (isFiniteLocallyConstant_pullback q hF)
  exact ⟨globalNormalGenericModelOfAffineRestriction R j s q t hsq F
    (normalGenericModel R t ((inverseImage j).obj F) hFt)⟩

/-- Choose the produced actual global normal model of the original stratum. -/
def globalNormalGenericModel {X S : Scheme.{u}} [IsIntegral S]
    (s : S ⟶ X) [IsImmersion s] (F : AbelianSheaf.{u, u + 1} X)
    (hF : IsFiniteLocallyConstant ((inverseImage s).obj F)) : GlobalNormalGenericModel s F :=
  Classical.choice (nonempty_globalNormalGenericModel s F hF)

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteCogenerators.Global
