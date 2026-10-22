/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.FiniteType.SubalgebraColimit
public import Mathlib.CategoryTheory.Filtered.Final

/-!
# Finitely generated subalgebras in a filtered ring diagram

The index objects are pairs of a ring-diagram stage and an admissible finitely
generated integer subalgebra at that stage. Morphisms retain the actual base
arrow and require it to carry the source subalgebra into the target subalgebra.
In particular this construction works for non-thin filtered categories.

Admissibility need only be cofinal among finite sets at each stage. No stability
under transition maps is needed: a finite set of image generators can always
be enlarged to an admissible target. The projection is final, and the actual
subalgebra diagram has the same ring colimit as the original diagram.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CommRingCat.FilteredSubalgebra

universe u

variable {I : Type u} [Category.{u} I] (F : I ⥤ CommRingCat.{u})
variable (P : ∀ i, Subalgebra ℤ (F.obj i) → Prop)

/-- A dependent finite-subalgebra index with an arbitrary admissibility condition. -/
structure Index where
  /-- The original diagram stage. -/
  base : I
  /-- The chosen subalgebra of that stage. -/
  algebra : Subalgebra ℤ (F.obj base)
  /-- Only finitely generated subalgebras are retained. -/
  fg : algebra.FG
  /-- The chosen subalgebra satisfies the prescribed extra condition. -/
  eligible : P base algebra

namespace Index

/-- An arrow records its original stage arrow, not merely its existence. -/
structure Hom (X Y : Index F P) where
  /-- The arrow in the original indexing category. -/
  base : X.base ⟶ Y.base
  /-- Its ring map restricts to the chosen subalgebras. -/
  map_mem : ∀ x ∈ X.algebra, (F.map base).hom x ∈ Y.algebra

@[ext]
lemma Hom.ext {X Y : Index F P} (f g : Hom F P X Y) (h : f.base = g.base) :
    f = g := by
  cases f
  cases g
  cases h
  rfl

instance : Category (Index F P) where
  Hom := Hom F P
  id X :=
    { base := 𝟙 X.base
      map_mem x hx := by simpa using hx }
  comp f g :=
    { base := f.base ≫ g.base
      map_mem x hx := by
        simpa only [Functor.map_comp, CommRingCat.hom_comp, RingHom.comp_apply] using
          g.map_mem _ (f.map_mem x hx) }
  id_comp f := Hom.ext F P _ _ (Category.id_comp _)
  comp_id f := Hom.ext F P _ _ (Category.comp_id _)
  assoc f g h := Hom.ext F P _ _ (Category.assoc _ _ _)

@[simp]
lemma id_base (X : Index F P) : (𝟙 X : X ⟶ X).base = 𝟙 X.base := rfl

@[simp]
lemma comp_base {X Y Z : Index F P} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).base = f.base ≫ g.base := rfl

/-- The literal restriction of the original ring map. -/
def Hom.ringHom {X Y : Index F P} (f : X ⟶ Y) : X.algebra →+* Y.algebra :=
  ((F.map f.base).hom.comp X.algebra.val.toRingHom).codRestrict Y.algebra
    (fun x ↦ f.map_mem x x.property)

@[simp]
lemma Hom.ringHom_apply {X Y : Index F P} (f : X ⟶ Y) (x : X.algebra) :
    (f.ringHom F P x : F.obj Y.base) = (F.map f.base).hom x := rfl

instance (X : Index F P) : Algebra.FiniteType ℤ X.algebra :=
  (Subalgebra.fg_iff_finiteType X.algebra).mp X.fg

end Index

/-- Every finite set at every stage is contained in an admissible finite subalgebra. -/
def Cofinal : Prop :=
  ∀ (i : I) (s : Finset (F.obj i)), ∃ A : Subalgebra ℤ (F.obj i),
    A.FG ∧ P i A ∧ (s : Set (F.obj i)) ⊆ A

variable {F P}

/-- The finite-set condition also allows enlargement of a whole finite subalgebra. -/
lemma exists_le (hP : Cofinal F P) (i : I) (A : Subalgebra ℤ (F.obj i)) (hA : A.FG) :
    ∃ B : Subalgebra ℤ (F.obj i), B.FG ∧ P i B ∧ A ≤ B := by
  obtain ⟨s, hs⟩ := hA
  obtain ⟨B, hB, hPB, hsB⟩ := hP i s
  refine ⟨B, hB, hPB, ?_⟩
  rw [← hs]
  exact Algebra.adjoin_le hsB

/-- Every base arrow lifts after enlarging the finite image to an admissible target. -/
lemma exists_target (hP : Cofinal F P) (X : Index F P) {j : I} (f : X.base ⟶ j) :
    ∃ A : Subalgebra ℤ (F.obj j), A.FG ∧ P j A ∧
      ∀ x ∈ X.algebra, (F.map f).hom x ∈ A := by
  obtain ⟨A, hA, hPA, hle⟩ := exists_le hP j
    (X.algebra.map (F.map f).hom.toIntAlgHom)
    (X.fg.map (F.map f).hom.toIntAlgHom)
  exact ⟨A, hA, hPA, fun x hx ↦ hle (Subalgebra.mem_map.mpr ⟨x, hx, rfl⟩)⟩

variable (F P)

/-- Forget the finite subalgebra but retain the original stage and arrow. -/
def forget : Index F P ⥤ I where
  obj X := X.base
  map f := f.base

/-- The actual diagram of restricted ring maps between the chosen subalgebras. -/
def ringDiagram : Index F P ⥤ CommRingCat.{u} where
  obj X := CommRingCat.of X.algebra
  map f := CommRingCat.ofHom (f.ringHom F P)
  map_id X := by
    ext x
    change (F.map (𝟙 X.base)).hom x = x
    simp
  map_comp f g := by
    ext x
    change (F.map (f.base ≫ g.base)).hom x =
      (F.map g.base).hom ((F.map f.base).hom x)
    simp

/-- The literal inclusions into the original ring stages form a natural transformation. -/
def inclusion : ringDiagram F P ⟶ forget F P ⋙ F where
  app X := CommRingCat.ofHom X.algebra.val.toRingHom
  naturality _ _ _ := rfl

/-- Compose the stage inclusions with the original cocone. -/
def ringCocone (c : Cocone F) : Cocone (ringDiagram F P) where
  pt := c.pt
  ι :=
    { app X := CommRingCat.ofHom X.algebra.val.toRingHom ≫ c.ι.app X.base
      naturality X Y f := by
        ext x
        change X.algebra at x
        change (c.ι.app Y.base).hom ((F.map f.base).hom x) =
          (c.ι.app X.base).hom x
        exact congrArg (fun q : F.obj X.base ⟶ c.pt ↦ q.hom x) (c.w f.base) }

variable {F P} [IsFiltered I]

/-- Cofinal admissible finite subalgebras form a filtered category. -/
theorem isFiltered (hP : Cofinal F P) : IsFiltered (Index F P) := by
  classical
  let : Nonempty (Index F P) := by
    obtain ⟨i⟩ := IsFiltered.nonempty (C := I)
    obtain ⟨A, hA, hPA, -⟩ := hP i ∅
    exact ⟨⟨i, A, hA, hPA⟩⟩
  let : IsFilteredOrEmpty (Index F P) :=
    { cocone_objs := by
        intro X Y
        let j := IsFiltered.max X.base Y.base
        let f := IsFiltered.leftToMax X.base Y.base
        let g := IsFiltered.rightToMax X.base Y.base
        obtain ⟨A, hA, hPA, hle⟩ := exists_le hP j
          (X.algebra.map (F.map f).hom.toIntAlgHom ⊔
            Y.algebra.map (F.map g).hom.toIntAlgHom)
          ((X.fg.map (F.map f).hom.toIntAlgHom).sup
            (Y.fg.map (F.map g).hom.toIntAlgHom))
        exact ⟨⟨j, A, hA, hPA⟩,
          ⟨f, fun x hx ↦ hle (Algebra.mem_sup_left (Subalgebra.mem_map.mpr ⟨x, hx, rfl⟩))⟩,
          ⟨g, fun y hy ↦ hle (Algebra.mem_sup_right (Subalgebra.mem_map.mpr ⟨y, hy, rfl⟩))⟩,
          trivial⟩
      cocone_maps := by
        intro X Y f g
        let j := IsFiltered.coeq f.base g.base
        let t := IsFiltered.coeqHom f.base g.base
        obtain ⟨A, hA, hPA, ht⟩ := exists_target hP Y t
        exact ⟨⟨j, A, hA, hPA⟩, ⟨t, ht⟩,
          Index.Hom.ext F P _ _ (IsFiltered.coeq_condition f.base g.base)⟩ }
  exact IsFiltered.mk

/-- The dependent finite-subalgebra projection is final (cofinal for colimits). -/
theorem forget_final (hP : Cofinal F P) : (forget F P).Final := by
  let := isFiltered hP
  apply Functor.final_of_exists_of_isFiltered
  · intro i
    obtain ⟨A, hA, hPA, -⟩ := hP i ∅
    exact ⟨⟨i, A, hA, hPA⟩, ⟨𝟙 i⟩⟩
  · intro i X f g
    obtain ⟨A, hA, hPA, ht⟩ :=
      exists_target hP X (IsFiltered.coeqHom f g)
    exact ⟨⟨IsFiltered.coeq f g, A, hA, hPA⟩,
      ⟨IsFiltered.coeqHom f g, ht⟩, IsFiltered.coeq_condition f g⟩

/-- The original colimit is also the colimit of the admissible finite subalgebras. -/
def ringCoconeIsColimit (hP : Cofinal F P) {c : Cocone F} (hc : IsColimit c) :
    IsColimit (ringCocone F P c) := by
  classical
  letI := isFiltered hP
  let hcT := isColimitOfPreserves (CategoryTheory.forget CommRingCat.{u}) hc
  letI : ReflectsColimit (ringDiagram F P) (CategoryTheory.forget CommRingCat.{u}) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  apply isColimitOfReflects (CategoryTheory.forget CommRingCat.{u})
  apply Types.FilteredColimit.isColimitOf'
  · intro x
    obtain ⟨i, y, hy⟩ := Types.jointly_surjective_of_isColimit hcT x
    obtain ⟨A, hA, hPA, hs⟩ := hP i {y}
    refine ⟨⟨i, A, hA, hPA⟩, ⟨y, hs (by simp)⟩, hy.symm⟩
  · intro X x y h
    change X.algebra at x y
    change (c.ι.app X.base).hom (x : F.obj X.base) =
      (c.ι.app X.base).hom (y : F.obj X.base) at h
    obtain ⟨j, f, hf⟩ :=
      (Types.FilteredColimit.isColimit_eq_iff' hcT (x : F.obj X.base)
        (y : F.obj X.base)).mp h
    obtain ⟨A, hA, hPA, ht⟩ := exists_target hP X f
    refine ⟨⟨j, A, hA, hPA⟩, ⟨f, ht⟩, ?_⟩
    exact Subtype.ext hf

end CommRingCat.FilteredSubalgebra
