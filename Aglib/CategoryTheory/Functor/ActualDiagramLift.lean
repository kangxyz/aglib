/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import Mathlib.CategoryTheory.Limits.Preserves.Basic

/-! # Faithful diagram lifts with the supplied actual maps

Object isomorphisms conjugate the original diagram to the prescribed image
objects. Native `Faithful.div` then retains the supplied maps and proves their
functor laws. The supplied cocone point is compared directly with the preserved
value colimit; no colimit of the original diagram is chosen.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

universe uI vI uC vC uD vD

variable {I : Type uI} [Category.{vI} I]
  {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  (F : C ⥤ D) [F.Faithful] (K : I ⥤ D) (A : I → C)
  (e : ∀ i, K.obj i ≅ F.obj (A i))
  (g : ∀ {i j : I}, (i ⟶ j) → (A i ⟶ A j))
  (hg : ∀ {i j : I} (f : i ⟶ j),
    F.map (g f) = (e i).inv ≫ K.map f ≫ (e j).hom)

/-- The original supplied maps form a diagram by native faithful division.
The conjugated target is forced by the given object isomorphisms. -/
def actualDiagramLift : I ⥤ C :=
  let T : I ⥤ D :=
    { obj := fun i => F.obj (A i)
      map := fun {i j} f => (e i).inv ≫ K.map f ≫ (e j).hom
      map_id := by intro i; simp
      map_comp := by intros; simp [Category.assoc] }
  Functor.Faithful.div T F A (fun _ => rfl) g (by
    intro i j f
    exact heq_of_eq (hg f))

/-- Faithful division retains the exact supplied arrow, without another choice. -/
@[simp]
theorem actualDiagramLift_map {i j : I} (f : i ⟶ j) :
    (actualDiagramLift F K A e g hg).map f = g f := rfl

/-- The whole lifted diagram has the original specified isomorphism components. -/
def actualDiagramLiftIso : K ≅ actualDiagramLift F K A e g hg ⋙ F :=
  NatIso.ofComponents e (by
    intro i j f
    change K.map f ≫ (e j).hom = (e i).hom ≫ F.map (g f)
    rw [hg]
    simp)

variable [HasColimit (actualDiagramLift F K A e g hg)]
  [PreservesColimit (actualDiagramLift F K A e g hg) F]

/-- Compare the given original cocone point directly with the one preserved
value-colimit cocone, precomposed by the original whole diagram isomorphism. -/
def actualDiagramLiftColimitIso {c : Cocone K} (hc : IsColimit c) :
    c.pt ≅ F.obj (colimit (actualDiagramLift F K A e g hg)) :=
  hc.coconePointUniqueUpToIso
    ((IsColimit.precomposeHomEquiv (actualDiagramLiftIso F K A e g hg)
      (F.mapCocone (colimit.cocone (actualDiagramLift F K A e g hg)))).symm
        (isColimitOfPreserves F (colimit.isColimit (actualDiagramLift F K A e g hg))))

/-- The comparison preserves every original cocone leg and actual value map. -/
@[reassoc]
theorem ι_actualDiagramLiftColimitIso_hom {c : Cocone K} (hc : IsColimit c) (i : I) :
    c.ι.app i ≫ (actualDiagramLiftColimitIso F K A e g hg hc).hom =
      (e i).hom ≫ F.map (colimit.ι (actualDiagramLift F K A e g hg) i) := by
  exact hc.comp_coconePointUniqueUpToIso_hom
    ((IsColimit.precomposeHomEquiv (actualDiagramLiftIso F K A e g hg)
      (F.mapCocone (colimit.cocone (actualDiagramLift F K A e g hg)))).symm
        (isColimitOfPreserves F (colimit.isColimit (actualDiagramLift F K A e g hg)))) i

end CategoryTheory.Functor
