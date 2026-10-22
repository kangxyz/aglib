/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Adic.CoverSystemHom
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Adic.CoverSystemModules

/-!
# Algebra maps of actual adic cover modules from prescribed first-stage maps

The nilpotently lifted cover map induces the original contravariant
structure-module map at every stage. All components preserve the native unit
and multiplication; the prescribed first-stage map remains literal.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.FiniteEtale.Adic

universe u

/-- Assemble the whole naturality packet before substituting actual cover diagrams. -/
def sequenceHomData {D : Type*} [Category D] {P Q : ℕ → D}
    (t : ∀ n, P n ⟶ P (n + 1)) (u : ∀ n, Q n ⟶ Q (n + 1))
    (a : ∀ n, P n ⟶ Q n) (ha : ∀ n, t n ≫ a (n + 1) = a n ≫ u n) :
    Functor.ofSequence t ⟶ Functor.ofSequence u :=
  NatTrans.ofSequence a (fun n => by
    simpa only [Functor.ofSequence_map_homOfLE_succ] using ha n)

namespace CoverSystem

variable {X : Scheme.{u}} {K : X.IdealSheafData} {T U : CoverSystem K}

namespace Hom

variable (h : Hom T U)

/-- The original compatible cover-stage maps form a map of original ambient diagrams. -/
def diagramMap : T.diagram ⟶ U.diagram :=
  sequenceHomData
    (P := fun n => Over.mk (T.ambientMap n))
    (Q := fun n => Over.mk (U.ambientMap n))
    (fun n => Over.homMk (T.transition n) (T.transition_ambientMap n))
    (fun n => Over.homMk (U.transition n) (U.transition_ambientMap n))
    h.ambientStage (fun n => by
      apply Over.OverMorphism.ext
      exact h.transition n)

/-- The actual contravariant module map, retaining every original scheme-map component. -/
def moduleMap : U.moduleDiagram ⟶ T.moduleDiagram :=
  Functor.whiskerRight (NatTrans.op h.diagramMap) (Modules.Algebra.structureSheafFunctor X)

@[simp]
theorem moduleMap_app (n : ℕᵒᵖ) :
    h.moduleMap.app n =
      (Modules.Algebra.structureSheafFunctor X).map (h.ambientStage n.unop).op := rfl

/-- Every original component preserves the actual stage multiplication and unit. -/
instance instIsMonHomModuleMapApp (n : ℕᵒᵖ) :
    IsMonHom (C := X.Modules) (h.moduleMap.app n) :=
  Modules.Algebra.instIsMonHomStructureSheafFunctorMap (h.ambientStage n.unop).op

/-- The native adic-system map associated to the actual compatible cover map. -/
def adicMap [IsLocallyNoetherian X] : U.adicSystem ⟶ T.adicSystem :=
  ObjectProperty.homMk h.moduleMap

/-- The original native adic-map components retain the algebra-map certificates. -/
instance instIsMonHomAdicMapApp [IsLocallyNoetherian X] (n : ℕᵒᵖ) :
    IsMonHom (C := X.Modules) (h.adicMap.hom.app n) :=
  h.instIsMonHomModuleMapApp n

end Hom

/-- The prescribed first-stage map is literally the first component of the
nilpotently lifted native adic algebra map. -/
@[simp]
theorem homOfFirstStage_adicMap_app_one [IsLocallyNoetherian X]
    (f : T.cover 1 ⟶ U.cover 1) :
    (homOfFirstStage T U f).adicMap.hom.app (op 1) =
      Modules.Algebra.structurePullbackMap (p := U.ambientMap 1) (q := T.ambientMap 1)
        f.hom.left (Over.w ((Over.map (K ^ 1).subschemeι).map f.hom)) := rfl

end CoverSystem

end AlgebraicGeometry.Scheme.FiniteEtale.Adic
