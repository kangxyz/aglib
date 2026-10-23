/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.InjectiveDiagram.SystemCoherence
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.Exact

/-! # Pointwise cokernels of compatible coefficient systems

For a morphism of systems in varying abelian categories, ordinary pointwise
cokernels inherit transitions by their universal property. The identity and
composition equations retain the original right-adjoint comparisons and follow
by cancelling the original cokernel projections. In particular, no right
adjoint is assumed to preserve cokernels or epimorphisms.

Preservation of zero morphisms is derived explicitly from the given adjunctions.
The resulting projection is a morphism of the original systems, and its
component short complexes are exact, and short exact when the corresponding
input component is monic. This is the compatible quotient needed for dimension
shifting in scheme-limit continuity; it does not equip all systems with an
abelian category structure.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits

namespace CategoryTheory.InjectiveSystem

universe vI vA uI uA

variable {I : Type uI} [Category.{vI} I]
  {A : I → Type uA} [∀ i, Category.{vA} (A i)]
  (D : AdjunctionData A)

/-- The actual adjunction supplies preservation of zero morphisms, without an
additivity hypothesis on the adjunction data. -/
theorem AdjunctionData.right_map_zero [∀ i, HasZeroMorphisms (A i)]
    {i j : I} (a : i ⟶ j) (X Y : A j) :
    (D.right a).map (0 : X ⟶ Y) = 0 := by
  have : (D.right a).IsRightAdjoint := ⟨D.left a, ⟨D.adj a⟩⟩
  exact (D.right a).map_zero X Y

namespace System

variable [∀ i, Abelian (A i)] {F Q : System D} (η : System.Hom D F Q)

/-- The original transition followed by the target projection kills the source
component of the system morphism. -/
theorem cokernelMap_zero {i j : I} (a : i ⟶ j) :
    η.app i ≫ (Q.map a ≫ (D.right a).map (Limits.cokernel.π (η.app j))) = 0 := by
  rw [← Category.assoc, η.naturality, Category.assoc, ← Functor.map_comp,
    Limits.cokernel.condition, D.right_map_zero, comp_zero]

/-- The quotient transition is induced by the ordinary cokernel universal
property at its source index. -/
def cokernelMap {i j : I} (a : i ⟶ j) :
    Limits.cokernel (η.app i) ⟶ (D.right a).obj (Limits.cokernel (η.app j)) :=
  Limits.cokernel.desc (η.app i)
    (Q.map a ≫ (D.right a).map (Limits.cokernel.π (η.app j)))
    (cokernelMap_zero D η a)

/-- The defining quotient square uses the original right-adjoint transition. -/
@[reassoc (attr := simp)]
theorem cokernel_π_map {i j : I} (a : i ⟶ j) :
    Limits.cokernel.π (η.app i) ≫ cokernelMap D η a =
      Q.map a ≫ (D.right a).map (Limits.cokernel.π (η.app j)) :=
  Limits.cokernel.π_desc _ _ _

/-- The quotient transition satisfies the original identity comparison. -/
theorem cokernelMap_id (i : I) :
    cokernelMap D η (𝟙 i) ≫
        (D.idIso i).hom.app (Limits.cokernel (η.app i)) =
      𝟙 (Limits.cokernel (η.app i)) := by
  apply (cancel_epi (Limits.cokernel.π (η.app i))).1
  calc
    Limits.cokernel.π (η.app i) ≫ (cokernelMap D η (𝟙 i) ≫
        (D.idIso i).hom.app (Limits.cokernel (η.app i))) =
        Q.map (𝟙 i) ≫ (D.right (𝟙 i)).map (Limits.cokernel.π (η.app i)) ≫
          (D.idIso i).hom.app (Limits.cokernel (η.app i)) := by
      rw [← Category.assoc, cokernel_π_map, Category.assoc]
    _ = Q.map (𝟙 i) ≫ (D.idIso i).hom.app (Q.obj i) ≫
        Limits.cokernel.π (η.app i) :=
      congrArg (fun f => Q.map (𝟙 i) ≫ f)
        ((D.idIso i).hom.naturality (Limits.cokernel.π (η.app i)))
    _ = Limits.cokernel.π (η.app i) := by
      rw [← Category.assoc, Q.map_id, Category.id_comp]
    _ = Limits.cokernel.π (η.app i) ≫ 𝟙 _ := (Category.comp_id _).symm

/-- The quotient transitions satisfy the original composition comparison. -/
theorem cokernelMap_comp {i j k : I} (a : i ⟶ j) (b : j ⟶ k) :
    cokernelMap D η (a ≫ b) ≫
        (D.compIso a b).hom.app (Limits.cokernel (η.app k)) =
      cokernelMap D η a ≫ (D.right a).map (cokernelMap D η b) := by
  apply (cancel_epi (Limits.cokernel.π (η.app i))).1
  calc
    Limits.cokernel.π (η.app i) ≫ (cokernelMap D η (a ≫ b) ≫
        (D.compIso a b).hom.app (Limits.cokernel (η.app k))) =
        Q.map (a ≫ b) ≫ (D.right (a ≫ b)).map (Limits.cokernel.π (η.app k)) ≫
          (D.compIso a b).hom.app (Limits.cokernel (η.app k)) := by
      rw [← Category.assoc, cokernel_π_map, Category.assoc]
    _ = Q.map (a ≫ b) ≫ (D.compIso a b).hom.app (Q.obj k) ≫
        (D.right a).map ((D.right b).map (Limits.cokernel.π (η.app k))) :=
      congrArg (fun f => Q.map (a ≫ b) ≫ f)
        ((D.compIso a b).hom.naturality (Limits.cokernel.π (η.app k)))
    _ = Q.map a ≫ (D.right a).map
        (Q.map b ≫ (D.right b).map (Limits.cokernel.π (η.app k))) := by
      rw [← Category.assoc, Q.map_comp, Category.assoc, Functor.map_comp]
    _ = Q.map a ≫ (D.right a).map
        (Limits.cokernel.π (η.app j) ≫ cokernelMap D η b) := by
      rw [cokernel_π_map]
    _ = (Q.map a ≫ (D.right a).map (Limits.cokernel.π (η.app j))) ≫
        (D.right a).map (cokernelMap D η b) := by
      rw [Functor.map_comp, Category.assoc]
    _ = Limits.cokernel.π (η.app i) ≫
        (cokernelMap D η a ≫ (D.right a).map (cokernelMap D η b)) := by
      rw [← Category.assoc, cokernel_π_map]

/-- The compatible system of ordinary pointwise cokernels. -/
def cokernel : System D where
  obj i := Limits.cokernel (η.app i)
  map := cokernelMap D η
  map_id := cokernelMap_id D η
  map_comp := cokernelMap_comp D η

@[simp]
theorem cokernel_obj (i : I) :
    (cokernel D η).obj i = Limits.cokernel (η.app i) := rfl

@[simp]
theorem cokernel_map {i j : I} (a : i ⟶ j) :
    (cokernel D η).map a = cokernelMap D η a := rfl

/-- The original cokernel projections form a compatible system morphism. -/
def cokernelπ : System.Hom D Q (cokernel D η) where
  app i := Limits.cokernel.π (η.app i)
  naturality := cokernel_π_map D η

@[simp]
theorem cokernelπ_app (i : I) :
    (cokernelπ D η).app i = Limits.cokernel.π (η.app i) := rfl

/-- The projection is epic at every original index. -/
instance cokernelπ_app_epi (i : I) : Epi ((cokernelπ D η).app i) := by
  change Epi (Limits.cokernel.π (η.app i))
  infer_instance

@[reassoc]
theorem comp_cokernelπ (i : I) : η.app i ≫ (cokernelπ D η).app i = 0 :=
  Limits.cokernel.condition (η.app i)

/-- The component short complex retains the original morphism and the
projection from the constructed quotient system. -/
def cokernelShortComplex (i : I) : ShortComplex (A i) :=
  ShortComplex.mk (η.app i) ((cokernelπ D η).app i) (comp_cokernelπ D η i)

/-- Each original component sequence is exact. -/
theorem cokernelShortComplex_exact (i : I) :
    (cokernelShortComplex D η i).Exact :=
  ShortComplex.exact_cokernel (η.app i)

/-- A monic original component gives a short exact sequence in its own
coefficient category. -/
theorem cokernelShortComplex_shortExact (i : I) [Mono (η.app i)] :
    (cokernelShortComplex D η i).ShortExact where
  exact := cokernelShortComplex_exact D η i
  mono_f := inferInstanceAs (Mono (η.app i))
  epi_g := cokernelπ_app_epi D η i

end System

end CategoryTheory.InjectiveSystem
