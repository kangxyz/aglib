/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteCogenerators.LocallyConstant
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.GaloisRefinement

/-! # Connected refinements of actual finite coefficient trivializations

The existing Galois refinement supplies one connected surjective finite-etale
cover. Its original map to the original trivializing cover transports the
same finite constant value. No component enumeration or replacement model
of finite local systems is introduced.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteCogenerators

universe u

attribute [local instance] hasSheafifyLarge

/-- Every actual finite-etale coefficient trivialization over a connected
scheme has a connected surjective refinement, retaining its original arrow
and its original finite constant value. -/
theorem FiniteEtaleTrivialization.exists_connected_refinement
    {X : Scheme.{u}} [ConnectedSpace X] {F : AbelianSheaf.{u, u + 1} X}
    (t : FiniteEtaleTrivialization F) :
    ∃ (Z : Scheme.FiniteEtale X) (_a : Z ⟶ t.cover),
      ConnectedSpace Z.obj.left ∧ Surjective Z.obj.hom ∧ Nonempty
        ((inverseImage Z.obj.hom).obj F ≅
          (constantSheaf Z.obj.left.smallEtaleTopology AddCommGrpCat.{u + 1}).obj t.value) := by
  let : Surjective t.cover.obj.hom := t.surjective
  let : Nonempty t.cover.obj.left :=
    Nonempty.map (fun x : X => (t.surjective.surj x).choose) inferInstance
  obtain ⟨Z, a, _hZ, hconn, hsurj⟩ := Scheme.FiniteEtale.exists_galois_refinement t.cover
  refine ⟨Z, a, hconn, hsurj, ⟨?_⟩⟩
  exact eqToIso (congrArg (fun f => (inverseImage f).obj F) (Over.w a.hom).symm) ≪≫
    (inverseImageComp t.cover.obj.hom a.hom.left).app F ≪≫
    (inverseImage a.hom.left).mapIso t.iso ≪≫
    (inverseImageConstantIso a.hom.left).app t.value

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteCogenerators
