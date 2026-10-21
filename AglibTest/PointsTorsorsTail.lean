/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.FunctionField.SmoothConstants
public import Aglib.AlgebraicGeometry.FunctionField.UnitOpen
public import Aglib.AlgebraicGeometry.Morphisms.Etale.At
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.Sections
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.InertiaFibres
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.SplitProjection
public import Aglib.AlgebraicGeometry.Morphisms.Proper.ConstantFieldHelpers
public import Aglib.AlgebraicGeometry.Morphisms.Proper.GlobalSections
public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.TorsorExtension
public import Aglib.AlgebraicGeometry.Points.FiniteResidue
public import Aglib.AlgebraicGeometry.RationalPoint.AffineCoordinates
public import Aglib.AlgebraicGeometry.RationalPoint.ClosedLift
public import Aglib.AlgebraicGeometry.RationalPoint.FieldExtension
public import Aglib.AlgebraicGeometry.RationalPoint.FiniteField
public import Aglib.AlgebraicGeometry.ResidueField.SectionIsomorphism
public import Aglib.AlgebraicGeometry.Torsors.Relative
public import Aglib.AlgebraicGeometry.Torsors.Restriction
public import Aglib.RingTheory.Smooth.FiniteResidueFibre

/-! # Native clients of actual points, residue maps and relative torsor actions -/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option warningAsError true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.OverField (FScheme)
open AlgebraicGeometry.Scheme.FiniteEtale
open scoped CategoryTheory.MonObj TensorProduct

namespace AglibTest.PointsTorsorsTail
universe u
attribute [local instance] Over.cartesianMonoidalCategory

example (X : Scheme.{u}) [IsIntegral X] {I : Type*} [Finite I]
    (f : I → X.functionFieldˣ) :
    ∃ U ∈ X.affineOpens, ∃ s : I → Γ(X, U)ˣ, ∃ _ : Nonempty U,
      ∀ i, Units.map (X.germToFunctionField U).hom.toMonoidHom (s i) = f i :=
  exists_nonempty_affine_unit_open X f

example (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (p : X ⟶ Spec (.of K)) (U : X.Opens) [Nonempty U] :
    (X.germToFunctionField U).hom.comp (chartConstantMap K X p U) =
      X.functionFieldConstants p :=
  chart_genericConstantMap K X p U

example (F : Type u) [Field F] (X : FScheme F) [IsProper X.hom] [IsIntegral X.left] :
    IsField Γ(X.left, ⊤) := globalSections_isField X

example (F : Type u) [Field F] [IsAlgClosed F] (X : FScheme F) [IsIntegral X.left]
    (hfinite : Module.Finite F (structureCohomology F X 0)) :
    Function.Bijective (constants X) :=
  constants_bijective_of_isAlgClosed_of_finite_h0 X hfinite

example (A : Type u) [CommRing A] [Algebra ℤ A] [Algebra.FiniteType ℤ A]
    (X : Scheme.{u}) (p : X ⟶ Spec (.of A)) [LocallyOfFiniteType p]
    (U : X.Opens) (hU : (U : Set X).Nonempty) :
    ∃ x : X, x ∈ U ∧ IsClosed ({x} : Set X) ∧ Finite (X.residueField x) :=
  exists_finite_closedPoint_in_open A X p U hU

example (A C : Type u) [CommRing A] [CommRing C] [Algebra A C] (m : Ideal C) (c : C) :
    Algebra.Smooth.fibreEvaluation A C m (1 ⊗ₜ[A] c) = Ideal.Quotient.mk m c :=
  Algebra.Smooth.fibreEvaluation_one_tmul A C m c

example (F C : Type u) [Field F] [CommRing C] [Algebra F C]
    (g : Field.absoluteGaloisGroup F) (f : C →ₐ[F] AlgebraicClosure F) :
    (RationalPoint.affinePointEquiv F C).symm (g.toAlgHom.comp f) =
      FieldGalois.pointEnd F g ≫ (RationalPoint.affinePointEquiv F C).symm f :=
  RationalPoint.affinePointEquiv_symm_galois F C g f

example {X Y : Scheme.{u}} (i : X ⟶ Y) [IsClosedImmersion i]
    (K : Type u) [Field K] (q : Y ⟶ Spec (.of K))
    (p : Spec (.of K) ⟶ Y) (hp : p default ∈ Set.range i) (hpoint : p ≫ q = 𝟙 _) :
    ∃ s : Spec (.of K) ⟶ X, s ≫ i = p ∧ s ≫ (i ≫ q) = 𝟙 _ :=
  RationalPoint.closedImmersion_rationalPoint_lift i K q p hp hpoint

example {F K : Type u} [Field F] [Field K] (i : F →+* K) (X : FScheme F)
    [IsFinite X.hom] : Function.Bijective (RationalPoint.pointExtensionMap i X) :=
  RationalPoint.pointExtensionMap_bijective i X

example (k : Type u) [Field k] [Fintype k] (X : FScheme k)
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] :
    Finite (𝟙_ (FScheme k) ⟶ X) := RationalPoint.finite_rationalPoints k X

example {X Y : Scheme.{u}} (p : X ⟶ Y) (s : Y ⟶ X) (h : p ≫ s = 𝟙 X) (x : X) :
    IsIso (p.residueFieldMap x) := residueFieldMap_isIso_of_section p s h x

example {S : Scheme.{u}} (E : Over S) (A : Grp (Over S)) (X : Over E.left)
    (τ : TorsorAction (Torsors.Relative.pullbackGroup E A) (toUnit X)) :
    Torsors.Restriction.relativeTorsorRestriction E A X
      (Torsors.Relative.relativeTorsorAction E A X τ) = τ :=
  Torsors.Restriction.restriction_flatten E A X τ

example {S : Scheme.{u}} (E : Over S) (A : Grp (Over S)) (X : Over E.left)
    (τ : TorsorAction A (Torsors.Relative.relativeMap E X)) :
    Torsors.Relative.relativeTorsorAction E A X
      (Torsors.Restriction.relativeTorsorRestriction E A X τ) = τ :=
  Torsors.Restriction.flatten_restriction E A X τ

example (X : Scheme.{u}) [IsIntegral X]
    [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)]
    (A : Grp (Over X)) [IsFinite A.X.hom] [Etale A.X.hom] (Y : Scheme.FiniteEtale X)
    (τ : TorsorAction (GenericTorsorExtension.genericGroup X A)
      (toUnit ((GenericTorsorExtension.genericFunctor X).obj Y.obj))) :
    ∃! σ : TorsorAction A (toUnit Y.obj),
      (GenericTorsorExtension.genericFunctor X).map σ.actionMap =
        (Functor.Monoidal.μIso (GenericTorsorExtension.genericFunctor X) A.X Y.obj).inv ≫
          τ.actionMap :=
  GenericTorsorExtension.existsUnique_torsor_extension X A Y τ

example {B : Scheme.{u}} {K : Type u} [Field K] (s : Spec (.of K) ⟶ B)
    [GaloisCategory (Scheme.FiniteEtale B)]
    [PreGaloisCategory.FiberFunctor (fiberToFinite s)]
    (Y : Scheme.FiniteEtale B) (q : FixedPoints.globalSection Y) :
    (FixedPoints.globalSectionEquivFixedFiber s Y q).val.left = s ≫ q.left :=
  FixedPoints.globalSectionEquivFixedFiber_value_left s Y q

example {R K : Type u} [CommRing R] [Field K] [Algebra R K]
    (Q : Ideal (integralClosure.Inertia.IntegralModel R K)) [Q.IsPrime]
    (γ : integralClosure.Inertia.inertia R K Q) (Y : Scheme.FiniteEtale (Spec (.of R)))
    (t : Fiber (FieldGalois.geometricPoint K) ((baseChange (Spec.algebraMap R K)).obj Y)) :
    FieldGalois.pointEnd K γ.val ≫ t = t := Inertia.inertia_fixes_genericFiber Q γ Y t

example (I : Type u) [Finite I] (X : Scheme.{u}) :
    IsFinite (Sigma.desc (fun _ : I => 𝟙 X)) ∧
      Etale (Sigma.desc (fun _ : I => 𝟙 X)) ∧
      ∀ x : X, (Sigma.desc (fun _ : I => 𝟙 X)).finrank x = Nat.card I :=
  SplitProjection.sigmaDesc_finite_etale_finrank I X

example {Z X : Scheme.{u}} (f : Z ⟶ X) (h : ∀ z, Scheme.Hom.etaleAt f z) : Etale f :=
  Scheme.Hom.etale_of_forall_etaleAt f h

end AglibTest.PointsTorsorsTail
