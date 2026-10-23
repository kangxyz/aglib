/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.FiniteTypeBaseChangeLimit
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.ConstantFinite.Basic
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Limits.Preserves.Ulift
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic

/-! # Original finite-constant sections along affine integral approximation

The published finitely generated subalgebra diagram is a genuine affine
inverse limit, including after base change to a fixed qcqs test scheme.
Its stages are finite over the original coefficient ring when the original
algebra is integral. Maps into the actual finite constant group scheme commute
with this limit by the native finite-presentation theorem.

The additive section functor below retains original scheme maps and their
precomposition. Its colimit is proved by the original represented-set theorem
and the conservative forgetful functor. Identifying this section cocone with
the full original constant direct-image sheaf cocone is a separate consumer;
no general varying-coefficient or higher-degree continuity is asserted here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.AffineIntegralConstants

universe u

attribute [local instance] hasSheafifyLarge

/-- Original additive sections of a commutative group scheme on arbitrary
scheme-valued tests over its fixed base. -/
def sectionFunctor {U : Scheme.{u}} (H : Grp (Over U)) [IsCommMonObj H.X] :
    (Over U)ᵒᵖ ⥤ AddCommGrpCat.{u + 1} where
  obj T := AddCommGrpCat.of (RepresentedSections H T.unop)
  map f := AddCommGrpCat.ofHom (representedSectionsPullback H f.unop)
  map_id T := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro a
    apply ULift.ext
    change Additive.ofMul (𝟙 T.unop ≫ a.down.toMul) = a.down
    simp
  map_comp f g := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro a
    apply ULift.ext
    change Additive.ofMul ((g.unop ≫ f.unop) ≫ a.down.toMul) =
      Additive.ofMul (g.unop ≫ (f.unop ≫ a.down.toMul))
    rw [Category.assoc]

/-- Forgetting addition leaves the original Yoneda sections, with only the
necessary value-universe lift. -/
def sectionFunctorForgetIso {U : Scheme.{u}} (H : Grp (Over U)) [IsCommMonObj H.X] :
    sectionFunctor H ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1} ≅
      yoneda.obj H.X ⋙ uliftFunctor.{u + 1} :=
  NatIso.ofComponents (fun T => Equiv.toIso {
    toFun := fun a => ULift.up a.down.toMul
    invFun := fun a => ULift.up (Additive.ofMul a.down)
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl })
    (fun f => by ext a; rfl)

/-- Fixed represented additive sections retain the native finite-presentation
colimit universal property, including their original additive maps. -/
private def sectionCoconeIsColimit {U : Scheme.{u}} {I : Type u}
    [Category.{u} I] [IsCofiltered I] (D : I ⥤ Over U)
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f).left]
    [∀ i, CompactSpace (D.obj i).left] [∀ i, QuasiSeparatedSpace (D.obj i).left]
    (c : Cone D) (hc : IsLimit c) (H : Grp (Over U)) [IsCommMonObj H.X]
    [LocallyOfFinitePresentation H.X.hom] :
    IsColimit ((sectionFunctor H).mapCocone c.op) := by
  have : PreservesColimit D.op (sectionFunctor H ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    preservesColimit_of_natIso D.op (sectionFunctorForgetIso H).symm
  have : PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1, u, u} _
  have : ReflectsColimit (D.op ⋙ sectionFunctor H) (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  apply isColimitOfReflects (CategoryTheory.forget AddCommGrpCat.{u + 1})
  exact isColimitOfPreserves (sectionFunctor H ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1}) hc.op

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

/-- Each original finite-generated subalgebra of an integral algebra is finite
as a module over the original ring. No Noetherian or injectivity premise is used. -/
theorem stage_finite [Algebra.IsIntegral R A] (s : Finset A) :
    Module.Finite R (Algebra.FiniteTypeSubalgebraLimit.stage R A s) :=
  Algebra.finite_adjoin_of_finite_of_isIntegral s.finite_toSet
    (fun x _ => Algebra.IsIntegral.isIntegral x)

/-- The actual spectrum stage is a finite morphism over the original affine base. -/
theorem stageMap_isFinite [Algebra.IsIntegral R A] (s : Finset A) :
    IsFinite (Spec.algebraMap R (Algebra.FiniteTypeSubalgebraLimit.stage R A s)) := by
  apply (IsFinite.SpecMap_iff _).mpr
  exact RingHom.finite_algebraMap.mpr (stage_finite R A s)

variable {U : Scheme.{u}} (p : U ⟶ Spec (.of R))

/-- The original stagewise pullbacks as objects over the fixed test scheme. -/
abbrev testDiagram : (Finset A)ᵒᵖ ⥤ Over U :=
  Scheme.FiniteTypeSubalgebraLimit.baseDiagram R A ⋙ Over.pullback p

/-- The actual cone of pullbacks over the fixed test scheme. -/
abbrev testCone : Cone (testDiagram R A p) :=
  (Over.pullback p).mapCone (Scheme.FiniteTypeSubalgebraLimit.baseCone R A)

/-- The published original affine inverse limit remains limiting after pullback. -/
def testConeIsLimit : IsLimit (testCone R A p) :=
  isLimitOfPreserves (Over.pullback p)
    (Scheme.FiniteTypeSubalgebraLimit.baseConeIsLimit R A)

/-- The actual finite-constant group sections on the original finite-generated
base changes have their original limiting sections as an additive colimit.
Only the fixed test scheme is required to be qcqs. -/
theorem nonempty_constantSectionCoconeIsColimit [CompactSpace U] [QuasiSeparatedSpace U]
    (B : Type u) [AddCommGroup B] [Finite B] :
    Nonempty (IsColimit ((sectionFunctor (ConstantFinite.representation B U).group).mapCocone
      (testCone R A p).op)) := by
  have {i j : (Finset A)ᵒᵖ} (f : i ⟶ j) :
      IsAffineHom ((testDiagram R A p).map f).left := by
    apply MorphismProperty.overPullbackMap (P := @IsAffineHom) p
      ((Scheme.FiniteTypeSubalgebraLimit.baseDiagram R A).map f)
    change IsAffineHom (Spec.map _)
    infer_instance
  have (i : (Finset A)ᵒᵖ) : CompactSpace ((testDiagram R A p).obj i).left := by
    change CompactSpace ((Scheme.FiniteTypeSubalgebraLimit.schemeDiagram R A p).obj i)
    infer_instance
  have (i : (Finset A)ᵒᵖ) : QuasiSeparatedSpace ((testDiagram R A p).obj i).left := by
    change QuasiSeparatedSpace ((Scheme.FiniteTypeSubalgebraLimit.schemeDiagram R A p).obj i)
    infer_instance
  exact ⟨sectionCoconeIsColimit (testDiagram R A p) (testCone R A p)
    (testConeIsLimit R A p) (ConstantFinite.representation B U).group⟩

/-- The constructed colimit universal property of the fixed original
finite-constant section cocone. Only this constant-coefficient consumer is public. -/
def constantSectionCoconeIsColimit [CompactSpace U] [QuasiSeparatedSpace U]
    (B : Type u) [AddCommGroup B] [Finite B] :
    IsColimit ((sectionFunctor (ConstantFinite.representation B U).group).mapCocone
      (testCone R A p).op) :=
  Classical.choice (nonempty_constantSectionCoconeIsColimit R A p B)

/-- The colimit cocone keeps literal precomposition by the original scheme
projection on every represented constant section. -/
theorem constantSectionCocone_app_apply
    (B : Type u) [AddCommGroup B] [Finite B] (s : Finset A)
    (a : RepresentedSections (ConstantFinite.representation B U).group
      ((testDiagram R A p).obj (op s))) :
    (((sectionFunctor (ConstantFinite.representation B U).group).mapCocone
      (testCone R A p).op).ι.app (op (op s))) a =
        ULift.up (Additive.ofMul ((testCone R A p).π.app (op s) ≫ a.down.toMul)) := rfl

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.AffineIntegralConstants
