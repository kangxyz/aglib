/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.GenericUnitCoordinates
public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.GenericArtinBaseChangeIndex
public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.GenericUnitRepresentatives
public import Aglib.AlgebraicGeometry.Stalk.DiscreteLocalExtension

/-!
# Actual local extensions of generic pullback units

An original unit on a generic Artin pullback has an affine local unit
representative near each of its image points. On every discrete scheme
mapping into that isolated neighborhood the original restrictions agree,
not merely their residue-field values.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Curves

universe u

variable {X : Scheme.{u}} [IsNoetherian X] (U : X.Etale) [QuasiCompact U.hom]

private theorem genericBaseChangeUnitCoordinates_stalkMap
    (a : Γ(pullback U.hom (genericArtinMap X), ⊤)ˣ)
    (p : (pullback U.hom (genericArtinMap X) : Scheme.{u})) :
    (pullback.fst U.hom (genericArtinMap X)).stalkMap p
      (genericBaseChangeUnitCoordinates U a p :
        U.left.presheaf.stalk ((pullback.fst U.hom (genericArtinMap X)) p)) =
      (pullback U.hom (genericArtinMap X)).presheaf.germ ⊤ p trivial
        (a : Γ(pullback U.hom (genericArtinMap X), ⊤)) := by
  let : IsArtinianScheme (pullback U.hom (genericArtinMap X)) :=
    genericArtinBaseChange_isArtinian (X := X) (U := U.left) U.hom
  let : ∀ p : (pullback U.hom (genericArtinMap X) : Scheme.{u}),
      IsIso ((pullback.fst U.hom (genericArtinMap X)).stalkMap p) :=
    genericArtinBaseChange_stalkMap_isIso U.hom
  change (pullback.fst U.hom (genericArtinMap X)).stalkMap p
    (CategoryTheory.inv ((pullback.fst U.hom (genericArtinMap X)).stalkMap p)
      (Scheme.globalSectionsStalkProduct (pullback U.hom (genericArtinMap X)) a p)) = _
  exact (ConcreteCategory.congr_hom (IsIso.inv_hom_id
    ((pullback.fst U.hom (genericArtinMap X)).stalkMap p)) _).trans
      (Scheme.globalSectionsStalkProduct_apply _ _ p)

/-- A generic pullback unit has an affine extension stable under actual discrete restriction. -/
theorem exists_generic_local_unit_extension
    (a : Γ(pullback U.hom (genericArtinMap X), ⊤)ˣ)
    (p : (pullback U.hom (genericArtinMap X) : Scheme.{u})) :
    ∃ (W : U.left.Opens) (_ : IsAffineOpen W)
      (_hpW : (pullback.fst U.hom (genericArtinMap X)) p ∈ W) (s : Γ(U.left, W)ˣ),
      ∀ (Q : Scheme.{u}) [DiscreteTopology Q]
        (r : Q ⟶ pullback U.hom (genericArtinMap X))
        (hr : ∀ q : Q, (pullback.fst U.hom (genericArtinMap X)) (r q) ∈ W),
        Units.map r.appTop.hom.toMonoidHom a =
          Units.map ((r ≫ pullback.fst U.hom (genericArtinMap X)).appLE W ⊤
            (fun q _ => hr q)).hom.toMonoidHom s := by
  let : IsNoetherian U.left := {
    toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian (X := U.left) (Y := X) U.hom
    toCompactSpace := QuasiCompact.compactSpace_of_compactSpace (X := U.left) (Y := X) U.hom }
  let e := genericArtinBaseChangeIndexEquiv (X := X) (U := U.left) U.hom
  have hpgen : (pullback.fst U.hom (genericArtinMap X)) p ∈ genericPoints U.left := by
    have h := (e p).property
    rwa [genericArtinBaseChangeIndexEquiv_val] at h
  let η : genericPoints U.left := ⟨(pullback.fst U.hom (genericArtinMap X)) p, hpgen⟩
  obtain ⟨W, hW, hpW, s, hiso, hs⟩ := exists_isolated_generic_unit_representative
    U.left η (genericBaseChangeUnitCoordinates U a p)
  refine ⟨W, hW, hpW, s, ?_⟩
  intro Q _ r hr
  have hconst : ∀ q : Q, r q = p := by
    intro q
    apply e.injective
    have hqW : (e (r q)).val ∈ W := by
      rw [genericArtinBaseChangeIndexEquiv_val]
      exact hr q
    have hp : e p = η :=
      Subtype.ext (genericArtinBaseChangeIndexEquiv_val (X := X) (U := U.left) U.hom p)
    exact (hiso (e (r q)) hqW).trans hp.symm
  apply Scheme.units_pullback_eq_appLE_of_constant_image r
    (pullback.fst U.hom (genericArtinMap X)) p hconst W hpW a s
  exact (congrArg (fun b => ((pullback.fst U.hom (genericArtinMap X)).stalkMap p) b) hs).trans
    (genericBaseChangeUnitCoordinates_stalkMap U a p)

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves
