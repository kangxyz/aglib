/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.CechFamily
public import Mathlib.CategoryTheory.Sites.LocallySurjective

/-! # The actual covering family of local lifts of a section -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite

namespace CategoryTheory.Sheaf.ModuleCoefficients

universe v u

variable {C : Type u} [Category.{v} C]
  {F G : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}} (g : F ⟶ G)
  {W : C} (s : G.obj (op W))

/-- All arrows along which the given section admits a lift. -/
abbrev LocalLiftIndex := Σ V : C, {f : V ⟶ W // Presheaf.imageSieve g s f}

/-- The family of actual objects over `W` carrying the local lifts. -/
def localLiftFamily : LocalLiftIndex g s → Over W :=
  fun a => Over.mk a.2.1

/-- The chosen local lifts, extended along representables. -/
def localLiftSections :
    Presheaf.Cech.familyPresheaf (fun a => (localLiftFamily g s a).left) ⟶
      F ⋙ forget AddCommGrpCat where
  app X := ↾fun a => F.map a.2.op
    (Presheaf.localPreimage g s a.1.2.1 a.1.2.2)
  naturality X Y f := by
    ext a
    change F.map (f.unop ≫ a.2).op _ = F.map f (F.map a.2.op _)
    simp only [op_comp, Quiver.Hom.op_unop, Functor.map_comp, ConcreteCategory.comp_apply]
    rfl

/-- Restriction of the chosen target section along the represented base. -/
def representedSection : uliftYoneda.{max u v}.obj W ⟶ G ⋙ forget AddCommGrpCat where
  app X := ↾fun a => G.map a.down.op s
  naturality X Y f := by
    ext a
    change G.map (f.unop ≫ a.down).op s = G.map f (G.map a.down.op s)
    simp only [op_comp, Quiver.Hom.op_unop, Functor.map_comp, ConcreteCategory.comp_apply]

/-- The lift retains the original quotient map and the original covering map. -/
lemma localLiftSections_comp :
    localLiftSections g s ≫ whiskerRight g (forget AddCommGrpCat) =
      Presheaf.Cech.familyMap (localLiftFamily g s) ≫ representedSection s := by
  ext X a
  change g.app X (F.map a.2.op _) = G.map (a.2 ≫ a.1.2.1).op s
  rw [NatTrans.naturality_apply, Presheaf.app_localPreimage]
  simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]

/-- Local surjectivity supplies a genuinely covering family, not an assumed
section-surjectivity statement. -/
theorem localLiftFamily_locallySurjective (J : GrothendieckTopology C)
    [Presheaf.IsLocallySurjective J g] :
    Presheaf.IsLocallySurjective J (Presheaf.Cech.familyMap (localLiftFamily g s)) where
  imageSieve_mem {X} y := by
    apply J.superset_covering _ (J.pullback_stable y.down (Presheaf.imageSieve_mem J g s))
    intro V f hf
    refine ⟨⟨⟨V, f ≫ y.down, hf⟩, 𝟙 V⟩, ?_⟩
    apply ULift.ext
    change 𝟙 V ≫ (f ≫ y.down) = f ≫ y.down
    simp only [Category.id_comp]

end CategoryTheory.Sheaf.ModuleCoefficients
