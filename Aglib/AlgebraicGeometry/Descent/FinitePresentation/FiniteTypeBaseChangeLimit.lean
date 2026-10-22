/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.FiniteType.SubalgebraColimit
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.CategoryTheory.Comma.Over.Pullback

/-!
# Base change through the finite-generated subalgebras

Pulling back the actual spectrum limit of finite-generated subalgebras gives
the actual inverse system of scheme base changes. The canonical cone and its
projections retain their original structural maps. No faithful-flatness or
injectivity assumption on the coefficient algebra map is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.FiniteTypeSubalgebraLimit

universe u

open Algebra.FiniteTypeSubalgebraLimit

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

/-- The spectrum diagram of the native finite-generated subalgebras. -/
def specDiagram : (Finset A)ᵒᵖ ⥤ Scheme.{u} :=
  (ringDiagram R A).op ⋙ Scheme.Spec

/-- The original spectrum cone, obtained from the native inclusion cocone. -/
def specCone : Cone (specDiagram R A) :=
  Scheme.Spec.mapCone (ringCocone R A).op

/-- The native inclusion cocone supplies the spectrum limit. -/
def specConeIsLimit : IsLimit (specCone R A) :=
  isLimitOfPreserves Scheme.Spec (ringCoconeIsColimit R A).op

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Every finite-generated stage retains its original coefficient map. -/
def baseStructure : specDiagram R A ⟶
    (Functor.const (Finset A)ᵒᵖ).obj (Spec (.of R)) where
  app s := Spec.algebraMap R (stage R A s.unop)
  naturality s t g := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1

/-- The native spectrum diagram regarded over the original coefficient base. -/
def baseDiagram : (Finset A)ᵒᵖ ⥤ Over (Spec (.of R)) :=
  Over.lift (specDiagram R A) (baseStructure R A)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original limiting spectrum map respects every stage's coefficient map. -/
theorem baseStructure_fac (s : (Finset A)ᵒᵖ) :
    (specCone R A).π.app s ≫ (baseStructure R A).app s = Spec.algebraMap R A := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1

/-- The limiting cone in the native over category. -/
def baseCone : Cone (baseDiagram R A) :=
  Over.liftCone (specDiagram R A) (baseStructure R A) (specCone R A)
    (Spec.algebraMap R A) (baseStructure_fac R A)

/-- The original spectrum cone remains limiting over the coefficient spectrum. -/
def baseConeIsLimit : IsLimit (baseCone R A) :=
  Over.isLimitLiftCone (specDiagram R A) (baseStructure R A) (specCone R A)
    (Spec.algebraMap R A) (baseStructure_fac R A) (specConeIsLimit R A)

variable {X : Scheme.{u}} (p : X ⟶ Spec (.of R))

/-- The original finite-generated base changes, viewed as schemes. -/
def schemeDiagram : (Finset A)ᵒᵖ ⥤ Scheme.{u} :=
  baseDiagram R A ⋙ Over.pullback p ⋙ Over.forget X

/-- The cone of actual base changes. Its point is `pullback (Spec.algebraMap R A) p`. -/
def schemeCone : Cone (schemeDiagram R A p) :=
  (Over.pullback p ⋙ Over.forget X).mapCone (baseCone R A)

/-- The actual base-change cone is a limit. -/
def schemeConeIsLimit : IsLimit (schemeCone R A p) :=
  isLimitOfPreserves (Over.pullback p ⋙ Over.forget X) (baseConeIsLimit R A)

instance transition_isAffineHom {s t : (Finset A)ᵒᵖ} (g : s ⟶ t) :
    IsAffineHom ((schemeDiagram R A p).map g) := by
  apply MorphismProperty.overPullbackMap (P := @IsAffineHom) p ((baseDiagram R A).map g)
  change IsAffineHom (Spec.map _)
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
instance stage_compact [QuasiCompact p] (s : (Finset A)ᵒᵖ) :
    CompactSpace ((schemeDiagram R A p).obj s) := by
  change CompactSpace (pullback (Spec.algebraMap R (stage R A s.unop)) p : Scheme)
  exact QuasiCompact.compactSpace_of_compactSpace
    (pullback.fst (Spec.algebraMap R (stage R A s.unop)) p)

set_option backward.isDefEq.respectTransparency.types false in
instance stage_quasiSeparated [QuasiSeparated p] (s : (Finset A)ᵒᵖ) :
    QuasiSeparatedSpace ((schemeDiagram R A p).obj s) := by
  change QuasiSeparatedSpace (pullback (Spec.algebraMap R (stage R A s.unop)) p : Scheme)
  exact quasiSeparatedSpace_of_quasiSeparated
    (pullback.fst (Spec.algebraMap R (stage R A s.unop)) p)

/-- The canonical projection from the standard-order base change to a
finite-generated coefficient stage. -/
def projection (s : (Finset A)ᵒᵖ) :
    pullback p (Spec.algebraMap R A) ⟶ (schemeDiagram R A p).obj s :=
  (pullbackSymmetry p (Spec.algebraMap R A)).hom ≫ (schemeCone R A p).π.app s

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
theorem projection_snd (s : (Finset A)ᵒᵖ) :
    projection R A p s ≫
      pullback.snd (Spec.algebraMap R (stage R A s.unop)) p =
        pullback.fst p (Spec.algebraMap R A) := by
  have h : (schemeCone R A p).π.app s ≫
      pullback.snd (Spec.algebraMap R (stage R A s.unop)) p =
        pullback.snd (Spec.algebraMap R A) p :=
    Over.w ((Over.pullback p).map ((baseCone R A).π.app s))
  rw [projection, Category.assoc, h]
  simp

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
theorem projection_fst (s : (Finset A)ᵒᵖ) :
    projection R A p s ≫
      pullback.fst (Spec.algebraMap R (stage R A s.unop)) p =
        pullback.snd p (Spec.algebraMap R A) ≫
          Spec.map (CommRingCat.ofHom (stage R A s.unop).val.toRingHom) := by
  have h : (schemeCone R A p).π.app s ≫
      pullback.fst (Spec.algebraMap R (stage R A s.unop)) p =
        pullback.fst (Spec.algebraMap R A) p ≫
          Spec.map (CommRingCat.ofHom (stage R A s.unop).val.toRingHom) :=
    pullback.lift_fst _ _ _
  rw [projection, Category.assoc, h]
  simp

end AlgebraicGeometry.Scheme.FiniteTypeSubalgebraLimit
