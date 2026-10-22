/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.FormalPushforwardComparison
public import Aglib.AlgebraicGeometry.Modules.ClosedImmersion.Unit

/-! # Completion retains the original algebraic adjunction equation

This identifies completion of the actual algebraic adjoint with the specified
formal adjunction diagram. The proof uses the original quotient units, not
an arbitrary isomorphism between the source and target completions.
-/

@[expose] public noncomputable section
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme.Modules.Coherent
universe u
variable {A : Type u} [CommRing A] {X Y : Scheme.{u}}
  [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
  (p : Y ⟶ X) [IsProper p] (f : X ⟶ Spec (CommRingCat.of A)) (I : Ideal A)
  (M : X.CoherentSheaf) (G : Y.CoherentSheaf)
  (e : (coherentPullback p).obj M ⟶ G)

local instance : M.obj.IsQuasicoherent :=
  QuasiCoherent.quasicoherent_of_affineCharts _ (fun R j _ => (M.property R j).1)

/-- The original algebraic adjoint, with coherent membership retained. -/
def properCoherentAdjoint : M ⟶ properPushforwardCoefficient p G :=
  ObjectProperty.homMk ((pullbackPushforwardAdjunction p).homEquiv _ _ e.hom)

/-- Adjunction of an original unit-compatible family is detected before
specializing to geometric quotients. -/
theorem adjointDiagram_eq_of_units
    {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    {M : C} {N : D} (e : L.obj M ⟶ N)
    {F : ℕᵒᵖ ⥤ C} {V : ℕᵒᵖ ⥤ D}
    (u : ∀ n, M ⟶ F.obj (op n)) (v : ∀ n, N ⟶ V.obj (op n))
    (hu : ∀ n, Epi (u n)) (a : F ⟶ V ⋙ R) (b : F ⋙ L ⟶ V)
    (ha : ∀ n, u n ≫ a.app (op n) = adj.homEquiv _ _ e ≫ R.map (v n))
    (hb : ∀ n, L.map (u n) ≫ b.app (op n) = e ≫ v n) :
    a = ((adj.whiskerRight ℕᵒᵖ).homEquiv F V) b := by
  apply NatTrans.ext
  funext n
  let := hu n.unop
  apply (cancel_epi (u n.unop)).mp
  change u n.unop ≫ a.app n = u n.unop ≫
    ((((adj.whiskerRight ℕᵒᵖ).unit.app F).app n) ≫ R.map (b.app n))
  rw [Adjunction.whiskerRight_unit_app_app]
  change u n.unop ≫ a.app n = u n.unop ≫ adj.homEquiv _ _ (b.app n)
  rw [← adj.homEquiv_naturality_left, hb, adj.homEquiv_naturality_right, ha]

private theorem comp_unit_square {C : Type*} [Category C]
    {A B D E F : C} (u : A ⟶ B) (a : B ⟶ D) (b : D ⟶ E)
    (q : A ⟶ F) (v : F ⟶ D) (w : F ⟶ E)
    (ha : u ≫ a = q ≫ v) (hb : v ≫ b = w) :
    u ≫ (a ≫ b) = q ≫ w := by rw [← Category.assoc, ha, Category.assoc, hb]

private theorem comp_unit_pair {C : Type*} [Category C]
    {A B D E : C} (u : A ⟶ B) (a : B ⟶ D) (b : D ⟶ E)
    (v : A ⟶ D) (w : A ⟶ E) (ha : u ≫ a = v) (hb : v ≫ b = w) :
    u ≫ (a ≫ b) = w := by rw [← Category.assoc, ha, hb]

/-- The algebraic adjoint preserves the original quotient units as a whole diagram. -/
theorem algebraicAdjoint_quotientDiagram :
    idealSheafQuotientTowerHom X (idealThickeningIdealSheaf f I)
        ((pullbackPushforwardAdjunction p).homEquiv _ _ e.hom) ≫
      formalPushforwardComparison p f I G =
    ((pullbackPushforwardAdjunction p).whiskerRight ℕᵒᵖ).homEquiv _ _
      ((pullbackCompletionDiagramComparison p f I M).val.hom ≫
        idealSheafQuotientTowerHom Y (idealThickeningIdealSheaf (p ≫ f) I) e.hom) := by
  apply adjointDiagram_eq_of_units (pullbackPushforwardAdjunction p)
    (M := M.obj) (N := G.obj) e.hom
    (F := idealSheafQuotientTower X (idealThickeningIdealSheaf f I) M.obj)
    (V := idealSheafQuotientTower Y (idealThickeningIdealSheaf (p ≫ f) I) G.obj)
    (fun n => (idealSheafQuotientUnit X (idealThickeningIdealSheaf f I ^ n)).app M.obj)
    (fun n => (idealSheafQuotientUnit Y (idealThickeningIdealSheaf (p ≫ f) I ^ n)).app
      G.obj) (fun n => pullbackPushforwardUnit_epi
        (idealThickeningIdealSheaf f I ^ n).subschemeι M.obj)
  · intro n
    exact comp_unit_square _ _ _ _ _ _
      ((quotientTowerMapComparison (idealThickeningIdealSheaf f I)
        ((pullbackPushforwardAdjunction p).homEquiv M.obj G.obj e.hom)).property n)
      (formalPushforwardComparison_unit p f I G n)
  · intro n
    exact comp_unit_pair _ _ _ _ _
      ((pullbackCompletionDiagramComparison p f I M).property n)
      ((quotientTowerMapComparison (idealThickeningIdealSheaf (p ≫ f) I) e.hom).property n)

/-- The equality is of original compatible sheaf-valued families. -/
theorem formalAlgebraicAdjoint_diagram :
    ((completionFunctor X (idealThickeningIdealSheaf f I)).map
        (properCoherentAdjoint p M G e)).hom ≫ formalPushforwardComparison p f I G =
      formalModificationAdjoint p f I _ _
        ((baseIdealPullbackCompletionIso p f I M).hom ≫
          (completionFunctor Y (idealThickeningIdealSheaf (p ≫ f) I)).map e) := by
  have h := algebraicAdjoint_quotientDiagram p f I M G e
  rw [pullbackCompletionDiagramComparison_val] at h
  exact h

/-- Completion of the actual algebraic adjoint satisfies the original formal
comparison equation at every ordinary stage. -/
theorem formalAlgebraicAdjoint_diagram_app (n : ℕ) :
    ((completionFunctor X (idealThickeningIdealSheaf f I)).map
        (properCoherentAdjoint p M G e)).hom.app (op n) ≫
      (formalPushforwardComparison p f I G).app (op n) =
    (formalModificationAdjoint p f I _ _
      ((baseIdealPullbackCompletionIso p f I M).hom ≫
        (completionFunctor Y (idealThickeningIdealSheaf (p ≫ f) I)).map e)).app (op n) := by
  exact NatTrans.congr_app (formalAlgebraicAdjoint_diagram p f I M G e) (op n)

end AlgebraicGeometry.Scheme.Modules.Coherent
