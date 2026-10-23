/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.TupleStalkColimit
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper

/-! # Original coefficient maps and exactness of finite-source stage colimits -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Finite

universe u

attribute [local instance] hasSheafifyLarge

variable (A B : Type u) [CommRing A] [CommRing B]
  [HenselianLocalRing B] [IsSepClosed (IsLocalRing.ResidueField B)]
  [Algebra B A] [Module.Finite B A] {X : Scheme.{u}}
  {I : Type u} [Category.{u} I] [IsCofiltered I]
  (D : I ⥤ X.Etale) (c : Cone (D ⋙ Scheme.Etale.forget X))
  (e : Spec (.of A) ≅ c.pt.left)
  {F G : AbelianSheaf.{u, u + 1} X} (α : F ⟶ G)

/-- Original coefficient maps on the individual geometric stalks. -/
def finiteSourceStalkTupleMap : finiteSourceStalkTuple A B D c e F ⟶
    finiteSourceStalkTuple A B D c e G :=
  AddCommGrpCat.ofHom
    { toFun := fun z m =>
        (finiteSourceComponentPoint A B (e.hom ≫ c.pt.hom) m).presheafFiber.map α.hom (z m)
      map_zero' := by ext m; exact map_zero _
      map_add' := by intro a b; ext m; exact map_add _ _ _ }

omit [IsCofiltered I] in
/-- Every component is the native coefficient naturality square on original germs. -/
@[reassoc]
theorem finiteSourceStageGerms_naturality (i : I) :
    finiteSourceStageGerms A B D c e F i ≫ finiteSourceStalkTupleMap A B D c e α =
      α.hom.app (op (D.obj i)) ≫ finiteSourceStageGerms A B D c e G i := by
  apply ConcreteCategory.hom_ext
  intro a
  apply funext
  intro m
  exact ConcreteCategory.congr_hom
    ((finiteSourceComponentPoint A B (e.hom ≫ c.pt.hom) m).toPresheafFiber_naturality
      α.hom (D.obj i) (finiteLimitStagePoint A B D c e i m)) a

omit [IsCofiltered I] in
/-- The canonical colimit comparison retains the original coefficient maps. -/
@[reassoc]
theorem finiteSourceColimitToStalkTuple_naturality :
    colim.map (Functor.whiskerLeft D.op α.hom) ≫ finiteSourceColimitToStalkTuple A B D c e G =
      finiteSourceColimitToStalkTuple A B D c e F ≫ finiteSourceStalkTupleMap A B D c e α := by
  apply colimit.hom_ext
  intro i
  rw [colimit.ι_map_assoc, ι_finiteSourceColimitToStalkTuple,
    ι_finiteSourceColimitToStalkTuple_assoc]
  exact (finiteSourceStageGerms_naturality A B D c e α i.unop).symm

omit [IsCofiltered I] in
/-- Actual epimorphisms of original sheaves induce surjections of stalk tuples. -/
theorem finiteSourceStalkTupleMap_surjective [Epi α] :
    Function.Surjective (finiteSourceStalkTupleMap A B D c e α) := by
  intro z
  have hsurj (m : MaximalSpectrum A) : Function.Surjective
      ((finiteSourceComponentPoint A B (e.hom ≫ c.pt.hom) m).presheafFiber.map α.hom) := by
    let η := finiteSourceComponentPoint A B (e.hom ≫ c.pt.hom) m
    have : Epi ((η.sheafFiber (A := AddCommGrpCat.{u + 1})).map α) := inferInstance
    exact (AddCommGrpCat.epi_iff_surjective _).mp this
  choose y hy using fun m => hsurj m (z m)
  exact ⟨y, funext hy⟩

include A B e in
/-- The actual stage colimit preserves epimorphisms when its limit source is
finite over a strictly local base; prescribed target sections are preserved. -/
theorem finiteSourceSectionsColimitMap_surjective
    (hc : IsLimit ((Over.forget X).mapCone c))
    [∀ i, CompactSpace (D.obj i).left]
    [∀ i, QuasiSeparatedSpace (D.obj i).left]
    [∀ {i j} (a : i ⟶ j), IsAffineHom (D.map a).left] [Epi α] :
    Function.Surjective (colim.map (Functor.whiskerLeft D.op α.hom)) := by
  intro z
  obtain ⟨y, hy⟩ := finiteSourceStalkTupleMap_surjective A B D c e α
    (finiteSourceColimitToStalkTuple A B D c e G z)
  obtain ⟨x, hx⟩ := (finiteSourceColimitToStalkTuple_bijective A B D c e F hc).2 y
  refine ⟨x, (finiteSourceColimitToStalkTuple_bijective A B D c e G hc).1 ?_⟩
  exact (ConcreteCategory.congr_hom
    (finiteSourceColimitToStalkTuple_naturality A B D c e α) x).trans
    ((congrArg (finiteSourceStalkTupleMap A B D c e α) hx).trans hy)

end AlgebraicGeometry.Scheme.EtaleCohomology.Finite
