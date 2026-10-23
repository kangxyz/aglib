/-
Copyright (c) 2026 Motivic cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Adjunction.Whiskering

/-!
# Unbounded hypercohomology of complexes of abelian sheaves

For a site `(C, J)` and `X : C`, `freeAbelianSheaf J X` is the sheafification
of the free abelian presheaf on the actual representable presheaf `yoneda.obj X`.
It represents evaluation at `X`, as witnessed by `sectionsEquiv`.

For an arbitrary integer-indexed cochain complex `K` of abelian sheaves, define
`H J K p X` to be the group of morphisms from this sheaf in degree zero to
`K[p]` in the unbounded derived category. The localization is taken at genuine
quasi-isomorphisms of all integer-indexed complexes. In particular, this
construction accepts bounded-above, unbounded-below complexes without using
the bounded-below right-derived-functor API.

The sheafification and chosen derived-localization universe are explicit.
No enough-injectives assumption, boundedness assumption, or smaller-universe
claim is built into the definition. A standard large derived localization
always exists. The comparison with Mathlib's sheaf cohomology is provided for
complexes concentrated in degree zero.

This is generic ordinary-sheaf hypercohomology, not a construction of the
motivic complex, transfers, a Nisnevich site, or the field-evaluation theorem.
-/

@[expose] public noncomputable section

universe w w' t v u

open CategoryTheory CategoryTheory.Abelian Opposite

namespace CategoryTheory.Sheaf.Hypercohomology

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max v t}]

/-- The free abelian sheaf on a representable, functorially in its representing object. -/
def freeAbelianSheafFunctor : C ⥤ Sheaf J AddCommGrpCat.{max v t} :=
  uliftYoneda.{t} ⋙ (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free ⋙
    presheafToSheaf J AddCommGrpCat.{max v t}

/-- The sheafification of the presheaf `U ↦ ℤ[Hom(U, X)]`. -/
abbrev freeAbelianSheaf (X : C) : Sheaf J AddCommGrpCat.{max v t} :=
  (freeAbelianSheafFunctor J).obj X

/-- The explicit free-abelian/sheafification/Yoneda representation of sections. -/
def sectionsEquiv (X : C) (F : Sheaf J AddCommGrpCat.{max v t}) :
    (freeAbelianSheaf J X ⟶ F) ≃ F.obj.obj (op X) :=
  ((sheafificationAdjunction J AddCommGrpCat).homEquiv _ F).trans
    (((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv _ F.obj).trans uliftYonedaEquiv)

/-- The representing equivalence evaluates the sheafification adjoint on the identity generator. -/
theorem sectionsEquiv_apply (X : C) (F : Sheaf J AddCommGrpCat.{max v t})
    (f : freeAbelianSheaf J X ⟶ F) :
    sectionsEquiv J X F f =
      (((sheafificationAdjunction J AddCommGrpCat).homEquiv _ F f).app (op X))
        (FreeAbelianGroup.of (ULift.up (𝟙 X))) := rfl

/-- Evaluation is represented additively, not just as a bijection of sets. -/
def sectionsAddEquiv (X : C) (F : Sheaf J AddCommGrpCat.{max v t}) :
    (freeAbelianSheaf J X ⟶ F) ≃+ F.obj.obj (op X) where
  toEquiv := sectionsEquiv J X F
  map_add' _ _ := rfl

/-- The representing equivalence respects morphisms of coefficient sheaves. -/
theorem sectionsEquiv_naturality (X : C) {F G : Sheaf J AddCommGrpCat.{max v t}}
    (f : freeAbelianSheaf J X ⟶ F) (g : F ⟶ G) :
    sectionsEquiv J X G (f ≫ g) = g.hom.app (op X) (sectionsEquiv J X F f) := rfl

/-- If evaluation at `X` sends epimorphisms to surjections, its actual representing sheaf
is projective. This hypothesis is the precise site-dependent input for field evaluation. -/
theorem projective_freeAbelianSheaf (X : C)
    (hX : ∀ {F G : Sheaf J AddCommGrpCat.{max v t}} (g : F ⟶ G) [Epi g],
      Function.Surjective (g.hom.app (op X))) :
    Projective (freeAbelianSheaf J X) where
  factors {F G} f g _ := by
    obtain ⟨x, hx⟩ := hX g (sectionsEquiv J X G f)
    refine ⟨(sectionsEquiv J X F).symm x, (sectionsEquiv J X G).injective ?_⟩
    rw [sectionsEquiv_naturality, Equiv.apply_symm_apply, hx]

section Derived

variable [HasDerivedCategory.{w} (Sheaf J AddCommGrpCat.{max v t})]

/-- The fixed representing sheaf placed in cochain degree zero in the actual derived category. -/
abbrev sectionsSource (X : C) : DerivedCategory (Sheaf J AddCommGrpCat.{max v t}) :=
  (DerivedCategory.singleFunctor _ 0).obj (freeAbelianSheaf J X)

/-- Unbounded hypercohomology as an abelian group of derived morphisms. -/
abbrev H (K : CochainComplex (Sheaf J AddCommGrpCat.{max v t}) ℤ) (p : ℤ) (X : C) : Type w :=
  sectionsSource J X ⟶ (DerivedCategory.Q.obj K)⟦p⟧

/-- The derived hypercohomology presheaf, covariant in its derived coefficient object. -/
def derivedPresheafFunctor (p : ℤ) :
    DerivedCategory (Sheaf J AddCommGrpCat.{max v t}) ⥤ Cᵒᵖ ⥤ AddCommGrpCat.{w} :=
  shiftFunctor _ p ⋙ Functor.flip
    ((freeAbelianSheafFunctor J ⋙ DerivedCategory.singleFunctor _ 0).op ⋙
      preadditiveCoyoneda)

/-- Hypercohomology of actual cochain complexes, functorial in the complex and the site object. -/
def presheafFunctor (p : ℤ) :
    CochainComplex (Sheaf J AddCommGrpCat.{max v t}) ℤ ⥤ Cᵒᵖ ⥤ AddCommGrpCat.{w} :=
  DerivedCategory.Q ⋙ derivedPresheafFunctor J p

/-- Hypercohomology is an additive presheaf in the object of the site. -/
abbrev presheaf (K : CochainComplex (Sheaf J AddCommGrpCat.{max v t}) ℤ) (p : ℤ) :
    Cᵒᵖ ⥤ AddCommGrpCat.{w} :=
  (presheafFunctor J p).obj K

/-- The presheaf construction has the stated, specified-source derived-Hom groups. -/
theorem presheaf_obj (K : CochainComplex (Sheaf J AddCommGrpCat.{max v t}) ℤ)
    (p : ℤ) (X : C) :
    (presheaf J K p).obj (op X) = AddCommGrpCat.of (H J K p X) := rfl

/-- The map induced by an actual cochain map. -/
abbrev map {K L : CochainComplex (Sheaf J AddCommGrpCat.{max v t}) ℤ}
    (f : K ⟶ L) (p : ℤ) (X : C) :
    AddCommGrpCat.of (H J K p X) ⟶ AddCommGrpCat.of (H J L p X) :=
  ((presheafFunctor J p).map f).app (op X)

/-- The coefficient map is postcomposition with the shifted localized cochain map. -/
theorem map_apply {K L : CochainComplex (Sheaf J AddCommGrpCat.{max v t}) ℤ}
    (f : K ⟶ L) (p : ℤ) (X : C) (x : H J K p X) :
    map J f p X x = x ≫ (DerivedCategory.Q.map f)⟦p⟧' := rfl

/-- Restriction along an actual morphism of the site. -/
abbrev restriction (K : CochainComplex (Sheaf J AddCommGrpCat.{max v t}) ℤ)
    (p : ℤ) {X Y : C} (f : X ⟶ Y) :
    AddCommGrpCat.of (H J K p Y) ⟶ AddCommGrpCat.of (H J K p X) :=
  (presheaf J K p).map f.op

/-- Restriction is precomposition with the free representable's derived morphism. -/
theorem restriction_apply (K : CochainComplex (Sheaf J AddCommGrpCat.{max v t}) ℤ)
    (p : ℤ) {X Y : C} (f : X ⟶ Y) (x : H J K p Y) :
    restriction J K p f x =
      (DerivedCategory.singleFunctor _ 0).map ((freeAbelianSheafFunctor J).map f) ≫ x := rfl

@[simp]
theorem map_id (K : CochainComplex (Sheaf J AddCommGrpCat.{max v t}) ℤ) (p : ℤ) (X : C) :
    map J (𝟙 K) p X = 𝟙 _ := by
  ext x
  change x ≫ (DerivedCategory.Q.map (𝟙 K))⟦p⟧' = x
  simp

@[simp]
theorem map_comp {K L M : CochainComplex (Sheaf J AddCommGrpCat.{max v t}) ℤ}
    (f : K ⟶ L) (g : L ⟶ M) (p : ℤ) (X : C) :
    map J (f ≫ g) p X = map J f p X ≫ map J g p X := by
  ext x
  change x ≫ (DerivedCategory.Q.map (f ≫ g))⟦p⟧' =
    (x ≫ (DerivedCategory.Q.map f)⟦p⟧') ≫ (DerivedCategory.Q.map g)⟦p⟧'
  simp [Category.assoc]

/-- Quasi-isomorphisms induce isomorphisms of hypercohomology presheaves in every integer degree. -/
instance map_isIso {K L : CochainComplex (Sheaf J AddCommGrpCat.{max v t}) ℤ}
    (f : K ⟶ L) [QuasiIso f] (p : ℤ) : IsIso ((presheafFunctor J p).map f) := by
  change IsIso ((derivedPresheafFunctor J p).map (DerivedCategory.Q.map f))
  infer_instance

/-- A quasi-isomorphism of unbounded complexes gives the actual induced presheaf isomorphism. -/
def quasiIsoPresheafIso {K L : CochainComplex (Sheaf J AddCommGrpCat.{max v t}) ℤ}
    (f : K ⟶ L) [QuasiIso f] (p : ℤ) : presheaf J K p ≅ presheaf J L p :=
  asIso ((presheafFunctor J p).map f)

end Derived

end CategoryTheory.Sheaf.Hypercohomology
