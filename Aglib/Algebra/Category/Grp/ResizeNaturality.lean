/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.Grp.Resize
public import Mathlib.Algebra.Category.Grp.Preadditive
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Functoriality and original unit squares for additive resizing

All objects and maps use the existing `resizeAdditiveDiagram`. Source, target,
index and coefficient category universes remain independent. Naturality is
proved for whole original diagrams before evaluation at a coefficient or index.
-/

@[expose] public noncomputable section

namespace CategoryTheory

universe r e e' uI vI uC vC

variable {I : Type uI} [Category.{vI} I]

/-- Resize an additive map of original diagrams, allowing independent value universes. -/
def resizeAdditiveDiagramMapOfHom
    {P : I ⥤ AddCommGrpCat.{e}} {Q : I ⥤ AddCommGrpCat.{e'}}
    [∀ i, Small.{r} (P.obj i)] [∀ i, Small.{r} (Q.obj i)]
    (a : ∀ i, P.obj i →+ Q.obj i)
    (ha : ∀ {i j : I} (b : i ⟶ j) (x : P.obj i),
      a j (P.map b x) = Q.map b (a i x)) :
    resizeAdditiveDiagram.{r} P ⟶ resizeAdditiveDiagram.{r} Q where
  app i := AddCommGrpCat.ofHom
    (Shrink.addEquiv.symm.toAddMonoidHom.comp
      ((a i).comp Shrink.addEquiv.toAddMonoidHom))
  naturality i j b := by
    apply ConcreteCategory.ext_apply
    intro x
    change Shrink.addEquiv.symm
        (a j (Shrink.addEquiv (Shrink.addEquiv.symm (P.map b (Shrink.addEquiv x))))) =
      Shrink.addEquiv.symm
        (Q.map b (Shrink.addEquiv (Shrink.addEquiv.symm (a i (Shrink.addEquiv x)))))
    simp only [AddEquiv.apply_symm_apply]
    exact congrArg Shrink.addEquiv.symm (ha b (Shrink.addEquiv x))

/-- The complete resized map retains its original additive values. -/
theorem resizeAdditiveDiagramMapOfHom_app_shrink
    {P : I ⥤ AddCommGrpCat.{e}} {Q : I ⥤ AddCommGrpCat.{e'}}
    [∀ i, Small.{r} (P.obj i)] [∀ i, Small.{r} (Q.obj i)]
    (a : ∀ i, P.obj i →+ Q.obj i)
    (ha : ∀ {i j : I} (b : i ⟶ j) (x : P.obj i),
      a j (P.map b x) = Q.map b (a i x)) (i : I) (x : P.obj i) :
    (resizeAdditiveDiagramMapOfHom a ha).app i (Shrink.addEquiv.symm x) =
      Shrink.addEquiv.symm (a i x) := by
  change Shrink.addEquiv.symm (a i (Shrink.addEquiv (Shrink.addEquiv.symm x))) = _
  rw [AddEquiv.apply_symm_apply]

/-- An existing original natural transformation uses the same conjugate maps. -/
def resizeAdditiveDiagramMap
    {P Q : I ⥤ AddCommGrpCat.{e}}
    [∀ i, Small.{r} (P.obj i)] [∀ i, Small.{r} (Q.obj i)] (a : P ⟶ Q) :
    resizeAdditiveDiagram.{r} P ⟶ resizeAdditiveDiagram.{r} Q :=
  resizeAdditiveDiagramMapOfHom (fun i => (a.app i).hom)
    (fun b x => ConcreteCategory.congr_hom (a.naturality b) x)

/-- Resizing an original identity is the identity on the same Shrink diagram. -/
theorem resizeAdditiveDiagramMap_id (P : I ⥤ AddCommGrpCat.{e})
    [∀ i, Small.{r} (P.obj i)] :
    resizeAdditiveDiagramMap.{r} (𝟙 P) = 𝟙 (resizeAdditiveDiagram.{r} P) := by
  ext i x
  change Shrink.addEquiv.symm (Shrink.addEquiv x) = x
  exact AddEquiv.symm_apply_apply _ _

/-- Resizing preserves composition of the original whole-diagram maps. -/
theorem resizeAdditiveDiagramMap_comp
    {P Q T : I ⥤ AddCommGrpCat.{e}}
    [∀ i, Small.{r} (P.obj i)] [∀ i, Small.{r} (Q.obj i)]
    [∀ i, Small.{r} (T.obj i)] (a : P ⟶ Q) (b : Q ⟶ T) :
    resizeAdditiveDiagramMap.{r} (a ≫ b) =
      resizeAdditiveDiagramMap.{r} a ≫ resizeAdditiveDiagramMap.{r} b := by
  ext i x
  change Shrink.addEquiv.symm (b.app i (a.app i (Shrink.addEquiv x))) =
    Shrink.addEquiv.symm
      (b.app i (Shrink.addEquiv (Shrink.addEquiv.symm (a.app i (Shrink.addEquiv x)))))
  rw [AddEquiv.apply_symm_apply]

/-- Resizing preserves addition of original whole-diagram maps. -/
theorem resizeAdditiveDiagramMap_add
    {P Q : I ⥤ AddCommGrpCat.{e}}
    [∀ i, Small.{r} (P.obj i)] [∀ i, Small.{r} (Q.obj i)] (a b : P ⟶ Q) :
    resizeAdditiveDiagramMap.{r} (a + b) =
      resizeAdditiveDiagramMap.{r} a + resizeAdditiveDiagramMap.{r} b := by
  ext i x
  change Shrink.addEquiv.symm (a.app i (Shrink.addEquiv x) + b.app i (Shrink.addEquiv x)) = _
  exact map_add _ _ _

/-- Resize an entire coefficient functor, retaining its original diagram at each coefficient. -/
def resizeAdditiveDiagramFunctor
    {C : Type uC} [Category.{vC} C] (P : C ⥤ I ⥤ AddCommGrpCat.{e})
    [∀ c i, Small.{r} ((P.obj c).obj i)] : C ⥤ I ⥤ AddCommGrpCat.{r} where
  obj c := resizeAdditiveDiagram.{r} (P.obj c)
  map a := resizeAdditiveDiagramMap.{r} (P.map a)
  map_id c := by rw [P.map_id, resizeAdditiveDiagramMap_id]
  map_comp a b := by rw [P.map_comp, resizeAdditiveDiagramMap_comp]

/-- The coefficient functor remains additive on precisely the original resized groups. -/
instance resizeAdditiveDiagramFunctor_additive
    {C : Type uC} [Category.{vC} C] [Preadditive C]
    (P : C ⥤ I ⥤ AddCommGrpCat.{e}) [P.Additive]
    [∀ c i, Small.{r} ((P.obj c).obj i)] :
    (resizeAdditiveDiagramFunctor.{r} P).Additive where
  map_add := by
    intro c d a b
    change resizeAdditiveDiagramMap (P.map (a + b)) = _
    rw [P.map_add, resizeAdditiveDiagramMap_add]
    rfl

/-- The existing resized isomorphism retains the original component equivalence. -/
theorem resizeAdditiveDiagramIsoOfAddEquiv_hom_app_shrink
    {P : I ⥤ AddCommGrpCat.{e}} {Q : I ⥤ AddCommGrpCat.{e'}}
    [∀ i, Small.{r} (P.obj i)] [∀ i, Small.{r} (Q.obj i)]
    (a : ∀ i, P.obj i ≃+ Q.obj i)
    (ha : ∀ {i j : I} (b : i ⟶ j) (x : P.obj i),
      a j (P.map b x) = Q.map b (a i x)) (i : I) (x : P.obj i) :
    (resizeAdditiveDiagramIsoOfAddEquiv a ha).hom.app i (Shrink.addEquiv.symm x) =
      Shrink.addEquiv.symm (a i x) := by
  change Shrink.addEquiv.symm (a i (Shrink.addEquiv (Shrink.addEquiv.symm x))) = _
  rw [AddEquiv.apply_symm_apply]

/-- Original values detect the complete square on the actual resized diagrams.
The given maps to the target diagrams are unchanged; no alternative unit is constructed. -/
theorem resizeAdditiveDiagram_unit_square
    {P : I ⥤ AddCommGrpCat.{e}} {Q : I ⥤ AddCommGrpCat.{e'}}
    [∀ i, Small.{r} (P.obj i)] [∀ i, Small.{r} (Q.obj i)]
    {H K : I ⥤ AddCommGrpCat.{r}}
    (a : ∀ i, P.obj i →+ Q.obj i)
    (ha : ∀ {i j : I} (b : i ⟶ j) (x : P.obj i),
      a j (P.map b x) = Q.map b (a i x))
    (k : resizeAdditiveDiagram.{r} P ⟶ H)
    (l : resizeAdditiveDiagram.{r} Q ⟶ K) (b : H ⟶ K)
    (h : ∀ i (x : P.obj i),
      l.app i (Shrink.addEquiv.symm (a i x)) =
        b.app i (k.app i (Shrink.addEquiv.symm x))) :
    resizeAdditiveDiagramMapOfHom a ha ≫ l = k ≫ b := by
  ext i x
  obtain ⟨y, rfl⟩ := Shrink.addEquiv.symm.surjective x
  change l.app i ((resizeAdditiveDiagramMapOfHom a ha).app i
    (Shrink.addEquiv.symm y)) = _
  rw [resizeAdditiveDiagramMapOfHom_app_shrink]
  exact h i y

/-- Assemble original unit values into the whole coefficient natural transformation. -/
def resizeAdditiveDiagramUnitNatTrans
    {C : Type uC} [Category.{vC} C] (P : C ⥤ I ⥤ AddCommGrpCat.{e})
    [∀ c i, Small.{r} ((P.obj c).obj i)] (H : C ⥤ I ⥤ AddCommGrpCat.{r})
    (k : ∀ c, resizeAdditiveDiagram.{r} (P.obj c) ⟶ H.obj c)
    (h : ∀ {c d : C} (a : c ⟶ d) (i : I) (x : (P.obj c).obj i),
      (k d).app i (Shrink.addEquiv.symm ((P.map a).app i x)) =
        (H.map a).app i ((k c).app i (Shrink.addEquiv.symm x))) :
    resizeAdditiveDiagramFunctor.{r} P ⟶ H where
  app := k
  naturality c d a :=
    resizeAdditiveDiagram_unit_square (fun i => ((P.map a).app i).hom)
      (fun b x => ConcreteCategory.congr_hom ((P.map a).naturality b) x)
      (k c) (k d) (H.map a) (h a)

end CategoryTheory
