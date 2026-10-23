/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts

/-! # Original sheaf sections on disjoint small etale covers -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Finite

universe u

variable {X : Scheme.{u}} (F : AbelianSheaf.{u, u + 1} X)

/-- The original sheaf has a terminal section group on an empty etale object. -/
theorem sections_hom_ext_of_isEmpty (W : X.Etale) [IsEmpty W.left]
    {E : AddCommGrpCat.{u + 1}} (a b : E ⟶ F.obj.obj (op W)) : a = b := by
  let V : Empty → X.Etale := Empty.elim
  let f : ∀ i, V i ⟶ W := fun i => i.elim
  have hf : Sieve.ofArrows V f ∈ X.smallEtaleTopology W := by
    apply (Scheme.ofArrows_mem_smallEtaleTopology_iff f).mpr
    ext x
    exact isEmptyElim x
  exact F.property.hom_ext_ofArrows f hf (fun i => i.elim)

variable {ι : Type u} {W : X.Etale} {U : ι → X.Etale} (f : ∀ i, U i ⟶ W)
  (hf : Sieve.ofArrows U f ∈ X.smallEtaleTopology W)
  [∀ i, Mono (f i)]
  (hd : ∀ (i j : ι), i ≠ j → ∀ (Z : X.Etale) (a : Z ⟶ U i) (b : Z ⟶ U j),
    a ≫ f i = b ≫ f j → IsEmpty Z.left)

/-- The literal restriction cone for sections on a disjoint etale cover. -/
def disjointSectionsFan : Fan (fun i => F.obj.obj (op (U i))) :=
  Fan.mk (F.obj.obj (op W)) (fun i => F.obj.map (f i).op)

include hd in
/-- Every family of morphisms into component sections is compatible, since
cross-component test objects are empty. -/
theorem disjointSections_compatible {E : AddCommGrpCat.{u + 1}}
    (s : ∀ i, E ⟶ F.obj.obj (op (U i))) {Z : X.Etale} {i j : ι}
    (a : Z ⟶ U i) (b : Z ⟶ U j) (h : a ≫ f i = b ≫ f j) :
    s i ≫ F.obj.map a.op = s j ≫ F.obj.map b.op := by
  by_cases hij : i = j
  · subst j
    obtain rfl := (cancel_mono (f i)).mp h
    rfl
  · let := hd i j hij Z a b h
    exact sections_hom_ext_of_isEmpty F Z _ _

include hf hd

/-- The actual sheaf condition identifies global sections with component
sections, retaining the original restriction maps as projections. -/
def disjointSectionsFanIsLimit : IsLimit (disjointSectionsFan F f) := by
  refine Fan.IsLimit.mk _
    (fun s => F.property.amalgamateOfArrows f hf s.proj
      (fun {_ _ _} a b h => disjointSections_compatible F f hd s.proj a b h)) ?_ ?_
  · intro s i
    exact F.property.amalgamateOfArrows_map f hf s.proj
      (fun {_ _ _} a b h => disjointSections_compatible F f hd s.proj a b h) i
  · intro s m hm
    apply F.property.hom_ext_ofArrows f hf
    intro i
    exact (hm i).trans
      (F.property.amalgamateOfArrows_map f hf s.proj
        (fun {_ _ _} a b h => disjointSections_compatible F f hd s.proj a b h) i).symm

/-- The product identification with its original restriction projections. -/
def disjointSectionsIso : F.obj.obj (op W) ≅ ∏ᶜ fun i => F.obj.obj (op (U i)) :=
  (disjointSectionsFanIsLimit F f hf hd).conePointUniqueUpToIso (productIsProduct _)

@[reassoc (attr := simp)]
lemma disjointSectionsIso_hom_π (i : ι) :
    (disjointSectionsIso F f hf hd).hom ≫ Pi.π (fun i => F.obj.obj (op (U i))) i =
      F.obj.map (f i).op :=
  (disjointSectionsFanIsLimit F f hf hd).conePointUniqueUpToIso_hom_comp
    (productIsProduct _) ⟨i⟩

/-- The product identification is natural for the original sheaf morphisms. -/
@[reassoc]
lemma disjointSectionsIso_naturality {G : AbelianSheaf.{u, u + 1} X} (φ : F ⟶ G) :
    φ.hom.app (op W) ≫ (disjointSectionsIso G f hf hd).hom =
      (disjointSectionsIso F f hf hd).hom ≫
        Limits.Pi.map (fun i => φ.hom.app (op (U i))) := by
  apply Pi.hom_ext
  intro i
  simp only [Category.assoc, disjointSectionsIso_hom_π, Pi.map_π,
    disjointSectionsIso_hom_π_assoc]
  exact (φ.hom.naturality (f i).op).symm

include f hf hd in
/-- On a finite disjoint cover, epimorphisms on component sections give an
 epimorphism on the original section group. -/
theorem epi_sections_of_epi_components [Finite ι]
    {G : AbelianSheaf.{u, u + 1} X} (φ : F ⟶ G)
    [∀ i, Epi (φ.hom.app (op (U i)))] : Epi (φ.hom.app (op W)) := by
  let : HasFiniteBiproducts AddCommGrpCat.{u + 1} := Abelian.hasFiniteBiproducts
  have : Epi (φ.hom.app (op W) ≫ (disjointSectionsIso G f hf hd).hom) := by
    rw [disjointSectionsIso_naturality F f hf hd φ]
    infer_instance
  exact (epi_comp_iff_of_isIso (φ.hom.app (op W))
    (disjointSectionsIso G f hf hd).hom).mp inferInstance

end AlgebraicGeometry.Scheme.EtaleCohomology.Finite
