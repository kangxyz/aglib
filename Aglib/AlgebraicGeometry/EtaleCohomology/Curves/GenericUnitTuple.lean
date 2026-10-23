/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.GenericUnitCoordinates
public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.GenericArtinBaseChangeIndex

/-!
# Original generic direct-image sections as generic unit tuples

The indexing uses the literal base-change projection. The factors are the
original local Artin rings, not their residue fields.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
open GroupCohomology.Kummer.Coefficients

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Curves

universe u

variable {X : Scheme.{u}} [IsNoetherian X] (U : X.Etale) [QuasiCompact U.hom]

/-- Reindex the actual target-stalk product by the genuine component-generic points. -/
def genericUnitReindex :
    (∀ p : (pullback U.hom (genericArtinMap X) : Scheme.{u}),
      (U.left.presheaf.stalk ((pullback.fst U.hom (genericArtinMap X)) p))ˣ) ≃
      ∀ η : genericPoints U.left, (U.left.presheaf.stalk η.val)ˣ :=
  Equiv.piCongr (genericArtinBaseChangeIndexEquiv (X := X) (U := U.left) U.hom) fun p =>
    Equiv.cast (congrArg (fun x : U.left => (U.left.presheaf.stalk x)ˣ)
      (genericArtinBaseChangeIndexEquiv_val (X := X) (U := U.left) U.hom p).symm)

/-- The actual direct-image section equivalence, without replacing the coefficient sheaf. -/
def genericDirectImageUnitTupleEquiv :
    (((directImage (genericArtinMap X)).obj (gm (genericArtinLocus X))).obj.obj (op U)) ≃
      ∀ η : genericPoints U.left, (U.left.presheaf.stalk η.val)ˣ :=
  (unitsSections (genericArtinLocus X)
    ((siteBaseChange (genericArtinMap X)).op.obj (op U))).toEquiv.trans
    ((show Additive Γ(pullback U.hom (genericArtinMap X), ⊤)ˣ ≃
        Γ(pullback U.hom (genericArtinMap X), ⊤)ˣ from
      ⟨Additive.toMul, Additive.ofMul, fun _ => rfl, fun _ => rfl⟩).trans
      ((genericBaseChangeUnitCoordinates U).toEquiv.trans (genericUnitReindex U)))

private theorem cast_unitGerm {Y : Scheme.{u}} {x y : Y} (h : x = y)
    (a : Γ(Y, ⊤)ˣ) :
    Equiv.cast (congrArg (fun z : Y => (Y.presheaf.stalk z)ˣ) h)
      (Units.map (Y.presheaf.germ ⊤ x trivial).hom.toMonoidHom a) =
      Units.map (Y.presheaf.germ ⊤ y trivial).hom.toMonoidHom a := by
  subst y
  rfl

/-- The original Gm unit becomes exactly the tuple of actual generic unit germs. -/
theorem genericDirectImageUnitTupleEquiv_unit (a : (gm X).obj.obj (op U))
    (η : genericPoints U.left) :
    genericDirectImageUnitTupleEquiv U ((genericArtinUnit X).hom.app (op U) a) η =
      Units.map (U.left.presheaf.germ ⊤ η.val trivial).hom.toMonoidHom
        (unitsSections X (op U) a).toMul := by
  obtain ⟨p, rfl⟩ :=
    (genericArtinBaseChangeIndexEquiv (X := X) (U := U.left) U.hom).surjective η
  change genericUnitReindex U
    (genericDirectImageUnitCoordinates U ((genericArtinUnit X).hom.app (op U) a))
      (genericArtinBaseChangeIndexEquiv (X := X) (U := U.left) U.hom p) = _
  rw [genericUnitReindex, Equiv.piCongr_apply_apply]
  exact (congrArg (Equiv.cast (congrArg (fun x : U.left => (U.left.presheaf.stalk x)ˣ)
    (genericArtinBaseChangeIndexEquiv_val (X := X) (U := U.left) U.hom p).symm))
      (genericDirectImageUnitCoordinates_unit U a p)).trans (cast_unitGerm
        (genericArtinBaseChangeIndexEquiv_val (X := X) (U := U.left) U.hom p).symm _)

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves
