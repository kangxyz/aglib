/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedLocalRestriction
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.RestrictionUnit

/-! # Original section units in local graded restriction -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Coherent
open scoped TensorProduct DirectSum ChangeOfRings
namespace AlgebraicGeometry.Scheme.Cohomology

variable {A : Type u} [CommRing A] {X : Scheme.{u}} [IsLocallyNoetherian X]
  (f : X ⟶ Spec (CommRingCat.of A)) (I : Ideal A)
  (F : AdicSystem X (idealThickeningIdealSheaf f I))

/-- The actual tensor-module restriction preserves every original homogeneous section. -/
theorem formalGradedLocalModuleRestrictionIso_one_tmul_of
    (U V : X.affineOpens) (h : V.val ≤ U.val) (n : ℕ)
    (x : Γ(F.gradedPiece n, U)) :
    letI (W : X.Opens) : Algebra A Γ(X, W) := formalGradedSectionAlgebra f W
    letI (W : X.Opens) : Module (Γ(X, W) ⊗[A] I.associatedGraded)
        (⨁ n, Γ(F.gradedPiece n, W)) := formalGradedAffineModule f I F W
    letI : Algebra Γ(X, U) Γ(X, V) :=
      (X.presheaf.map (homOfLE h).op).hom.toAlgebra
    letI : IsScalarTower A Γ(X, U) Γ(X, V) :=
      IsScalarTower.of_algebraMap_eq fun a =>
        ((formalGradedCoordinateRestriction f h).commutes a).symm
    letI : Algebra (Γ(X, U) ⊗[A] I.associatedGraded)
        (Γ(X, V) ⊗[A] I.associatedGraded) :=
      Algebra.TensorProduct.coordinateAlgebra A Γ(X, U) Γ(X, V) I.associatedGraded
    (formalGradedLocalModuleRestrictionIso f I F U V h).hom
      ((1 : Γ(X, V) ⊗[A] I.associatedGraded) ⊗ₜ[Γ(X, U) ⊗[A] I.associatedGraded,
        (Algebra.TensorProduct.map (formalGradedCoordinateRestriction f h)
          (AlgHom.id A I.associatedGraded)).toRingHom]
        DirectSum.of (fun k => Γ(F.gradedPiece k, U)) n x) =
      DirectSum.of (fun k => Γ(F.gradedPiece k, V)) n
        ((F.gradedPiece n).val.map (homOfLE h).op x) := by
  let (W : X.Opens) : Algebra A Γ(X, W) := formalGradedSectionAlgebra f W
  let (W : X.Opens) : Module (Γ(X, W) ⊗[A] I.associatedGraded)
      (⨁ n, Γ(F.gradedPiece n, W)) := formalGradedAffineModule f I F W
  let : Algebra Γ(X, U) Γ(X, V) :=
    (X.presheaf.map (homOfLE h).op).hom.toAlgebra
  let : IsScalarTower A Γ(X, U) Γ(X, V) :=
    IsScalarTower.of_algebraMap_eq fun a =>
        ((formalGradedCoordinateRestriction f h).commutes a).symm
  let : Algebra (Γ(X, U) ⊗[A] I.associatedGraded)
      (Γ(X, V) ⊗[A] I.associatedGraded) :=
    Algebra.TensorProduct.coordinateAlgebra A Γ(X, U) Γ(X, V) I.associatedGraded
  dsimp only [formalGradedLocalModuleRestrictionIso, Iso.trans_hom]
  simp only [ConcreteCategory.comp_apply]
  erw [ModuleCat.extendScalarsAlgebraIso_tmul]
  exact formalGradedTensorRestrictionEquiv_one_tmul_of f I F U V (homOfLE h) n x

/-- The original local restriction comparison sends restrictions of homogeneous
sections to their actual coefficient restrictions. -/
theorem formalGradedLocalRestrictionIso_unit_of
    (U V : X.affineOpens) (h : V.val ≤ U.val)
    (n : ℕ) (x : Γ(F.gradedPiece n, U)) :
    letI (W : X.Opens) : Algebra A Γ(X, W) := formalGradedSectionAlgebra f W
    letI (W : X.Opens) : Module (Γ(X, W) ⊗[A] I.associatedGraded)
        (⨁ n, Γ(F.gradedPiece n, W)) := formalGradedAffineModule f I F W
    letI : Algebra Γ(X, U) Γ(X, V) :=
      (X.presheaf.map (homOfLE h).op).hom.toAlgebra
    letI : IsScalarTower A Γ(X, U) Γ(X, V) :=
      IsScalarTower.of_algebraMap_eq fun a =>
        ((formalGradedCoordinateRestriction f h).commutes a).symm
    letI : Algebra (Γ(X, U) ⊗[A] I.associatedGraded)
        (Γ(X, V) ⊗[A] I.associatedGraded) :=
      Algebra.TensorProduct.coordinateAlgebra A Γ(X, U) Γ(X, V) I.associatedGraded
    let φ := CommRingCat.ofHom (Algebra.TensorProduct.map
      (formalGradedCoordinateRestriction f h) (AlgHom.id A I.associatedGraded)).toRingHom
    letI : IsOpenImmersion (Spec.map φ) :=
      inferInstanceAs (IsOpenImmersion (formalGradedChartRestriction f I U V h))
    let N := formalGradedLocalModule f I F U
    ((tilde.toTildeΓNatIso (R := CommRingCat.of (Γ(X, V) ⊗[A] I.associatedGraded))).app
       (formalGradedLocalModule f I F V)).inv
      (moduleSpecΓFunctor.map (formalGradedLocalRestrictionIso f I F U V h).hom
        ((pushforwardGlobalSectionsIso φ).hom.app ((tilde N).restrict (Spec.map φ))
          (moduleSpecΓFunctor.map ((restrictAdjunction (Spec.map φ)).unit.app (tilde N))
            (((tilde.toTildeΓNatIso (R := CommRingCat.of (Γ(X, U) ⊗[A] I.associatedGraded))).app
               N).hom (DirectSum.of (fun k => Γ(F.gradedPiece k, U)) n x))))) =
      DirectSum.of (fun k => Γ(F.gradedPiece k, V)) n
        ((F.gradedPiece n).val.map (homOfLE h).op x) := by
  let (W : X.Opens) : Algebra A Γ(X, W) := formalGradedSectionAlgebra f W
  let (W : X.Opens) : Module (Γ(X, W) ⊗[A] I.associatedGraded)
      (⨁ n, Γ(F.gradedPiece n, W)) := formalGradedAffineModule f I F W
  let : Algebra Γ(X, U) Γ(X, V) :=
    (X.presheaf.map (homOfLE h).op).hom.toAlgebra
  let : IsScalarTower A Γ(X, U) Γ(X, V) :=
    IsScalarTower.of_algebraMap_eq fun a =>
      ((formalGradedCoordinateRestriction f h).commutes a).symm
  let : Algebra (Γ(X, U) ⊗[A] I.associatedGraded)
      (Γ(X, V) ⊗[A] I.associatedGraded) :=
    Algebra.TensorProduct.coordinateAlgebra A Γ(X, U) Γ(X, V) I.associatedGraded
  let φ := CommRingCat.ofHom (Algebra.TensorProduct.map
    (formalGradedCoordinateRestriction f h) (AlgHom.id A I.associatedGraded)).toRingHom
  let : IsOpenImmersion (Spec.map φ) :=
    inferInstanceAs (IsOpenImmersion (formalGradedChartRestriction f I U V h))
  let N := formalGradedLocalModule f I F U
  have hd := formalGradedLocalRestrictionIso_sections f I F U V h
  dsimp only [formalGradedLocalRestrictionSectionsIso, Iso.trans_hom, Iso.symm_hom,
    Iso.app_hom, Iso.app_inv, Functor.mapIso_hom] at hd
  exact (tildeRestriction_unit_of_sections φ N (formalGradedLocalModule f I F V)
    (formalGradedLocalRestrictionIso f I F U V h).hom
    (formalGradedLocalModuleRestrictionIso f I F U V h).hom hd
    (DirectSum.of (fun k => Γ(F.gradedPiece k, U)) n x)).trans
      (formalGradedLocalModuleRestrictionIso_one_tmul_of f I F U V h n x)

end AlgebraicGeometry.Scheme.Cohomology
