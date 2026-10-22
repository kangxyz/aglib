/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Adic.CompletionComparison

/-!
# Naturality of actual global-cover completion comparisons

The natural transformation between restriction towers has the literal maps
induced by the given cover morphism on every actual pullback stage. Its
construction by the original unit comparisons supplies all-order naturality;
the native stage-map formula verifies that no replacement maps were introduced.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.FiniteEtale.Adic

universe u

/-- Unit-determined isomorphisms retain a prescribed original map. -/
theorem unitIsoMapTransport {D : Type*} [Category D] {M N Q R S T : D}
    (u : M ⟶ Q) (v : N ⟶ R) [Epi u]
    (a : M ⟶ S) (b : N ⟶ T) (e : Q ≅ S) (d : R ≅ T)
    (he : u ≫ e.hom = a) (hd : v ≫ d.hom = b)
    (f : M ⟶ N) (q : Q ⟶ R) (r : S ⟶ T)
    (hq : u ≫ q = f ≫ v) (hr : a ≫ r = f ≫ b) :
    e.inv ≫ q ≫ d.hom = r := by
  apply (cancel_epi e.hom).mp
  simp only [Iso.hom_inv_id_assoc]
  apply (cancel_epi u).mp
  rw [← Category.assoc, hq, Category.assoc, hd, ← Category.assoc, he, hr]

/-- The actual pulled-back cover map retains the original projection. -/
@[reassoc]
theorem baseChangeMap_projection {X Z : Scheme.{u}} (j : Z ⟶ X)
    {C D : FiniteEtale X} (f : C ⟶ D) :
    ((baseChange j).map f).hom.left ≫ pullback.fst D.obj.hom j =
      pullback.fst C.obj.hom j ≫ f.hom.left := by
  simp [baseChange, forget, Over.pullback]

/-- Apply a contravariant functor to an entire original square equation. -/
theorem contravariantSquareEquation {C D : Type*} [Category C] [Category D]
    (F : Cᵒᵖ ⥤ D) {A B P Q : C} (s : A ⟶ B) (p : A ⟶ P)
    (q : B ⟶ Q) (f : P ⟶ Q) (h : s ≫ q = p ≫ f) :
    F.map q.op ≫ F.map s.op = F.map f.op ≫ F.map p.op := by
  rw [← F.map_comp, ← F.map_comp, ← op_comp, ← op_comp, h]

open Modules Modules.Coherent

variable {X : Scheme.{u}} [IsLocallyNoetherian X]
  (K : X.IdealSheafData) {C D : FiniteEtale X} (f : C ⟶ D)

/-- The original base-changed cover map, regarded over the original ambient scheme. -/
def restrictionStageMorphism (n : ℕ) :
    Over.mk ((restrictionCoverSystem K C).ambientMap n) ⟶
      Over.mk ((restrictionCoverSystem K D).ambientMap n) :=
  (Over.map (K ^ n).subschemeι).map (((baseChange (K ^ n).subschemeι).map f).hom)

omit [IsLocallyNoetherian X] in
/-- Original restriction-stage maps commute with the original global projections. -/
@[reassoc]
theorem restrictionStageMorphism_projection (n : ℕ) :
    restrictionStageMorphism K f n ≫ restrictionProjection K D n =
      restrictionProjection K C n ≫ f.hom := by
  apply Over.OverMorphism.ext
  exact baseChangeMap_projection (K ^ n).subschemeι f

omit [IsLocallyNoetherian X] in
/-- The original restriction-module units commute with the original cover map. -/
@[reassoc]
theorem restrictionModuleUnit_map (n : ℕ) :
    (restrictionModuleUnit K D).app (op n) ≫
      (Modules.Algebra.structureSheafFunctor X).map (restrictionStageMorphism K f n).op =
    (Modules.Algebra.structureSheafFunctor X).map f.hom.op ≫
      (restrictionModuleUnit K C).app (op n) := by
  exact contravariantSquareEquation (Modules.Algebra.structureSheafFunctor X)
    (restrictionStageMorphism K f n) (restrictionProjection K C n)
    (restrictionProjection K D n) f.hom (restrictionStageMorphism_projection K f n)

/-- The original global structure map with its native coherent-module endpoints fixed. -/
def globalStructureMap : (globalStructureCoherent D).obj ⟶ (globalStructureCoherent C).obj :=
  Modules.Algebra.structurePullbackMap (p := D.obj.hom) (q := C.obj.hom)
    f.hom.left f.hom.w

/-- The actual all-order restriction-module map induced by the original cover map. -/
def restrictionModuleMap :
    (restrictionCoverSystem K D).moduleDiagram ⟶ (restrictionCoverSystem K C).moduleDiagram :=
  (restrictionCompletionData K D).val.inv ≫
    idealSheafQuotientTowerHom X K (globalStructureMap f) ≫
      (restrictionCompletionData K C).val.hom

/-- Every component is literally the original structure map of the actual
base-changed cover morphism. -/
@[simp]
theorem restrictionModuleMap_app (n : ℕ) :
    (restrictionModuleMap K f).app (op n) =
      (Modules.Algebra.structureSheafFunctor X).map (restrictionStageMorphism K f n).op := by
  exact unitIsoMapTransport
    ((idealSheafQuotientUnit X (K ^ n)).app (globalStructureCoherent D).obj)
    ((idealSheafQuotientUnit X (K ^ n)).app (globalStructureCoherent C).obj)
    ((restrictionModuleUnit K D).app (op n)) ((restrictionModuleUnit K C).app (op n))
    ((restrictionCompletionData K D).val.app (op n))
    ((restrictionCompletionData K C).val.app (op n))
    ((restrictionCompletionData K D).property n) ((restrictionCompletionData K C).property n)
    (globalStructureMap f)
    ((idealSheafQuotientFunctor X (K ^ n)).map
      (globalStructureMap f))
    ((Modules.Algebra.structureSheafFunctor X).map (restrictionStageMorphism K f n).op)
    ((idealSheafQuotientUnit X (K ^ n)).naturality
      (globalStructureMap f)).symm
    (restrictionModuleUnit_map K f n)

/-- Naturality of the completion comparison in the original global-cover map. -/
@[reassoc]
theorem restrictionCompletion_naturality :
    idealSheafQuotientTowerHom X K (globalStructureMap f) ≫
      (restrictionCompletionData K C).val.hom =
    (restrictionCompletionData K D).val.hom ≫ restrictionModuleMap K f := by
  simp only [restrictionModuleMap, Iso.hom_inv_id_assoc]

/-- The same original restriction map in the native adic-system category. -/
def restrictionAdicMap :
    (restrictionCoverSystem K D).adicSystem ⟶ (restrictionCoverSystem K C).adicSystem :=
  ObjectProperty.homMk (restrictionModuleMap K f)

end AlgebraicGeometry.Scheme.FiniteEtale.Adic
