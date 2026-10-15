/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.TotalComplex.FirstQuadrant
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
/-!
# First-quadrant comparison for additive commutative groups

The native total-complex comparison is transported through the equivalence
between additive commutative groups and integer modules. The comparison with
the image of the total is characterized by its original coproduct injections.

Extraction source: `R5Lab.CategoryTheory.Homology.AdditiveFirstQuadrant` at R5Lab revision
`95a3772b895fbc19a81684be4ffd519d0fdcd6b3`; all declarations are retained.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits HomologicalComplex HomologicalComplex₂

universe u

namespace HomologicalComplex₂.AddCommGrp

/-- Bicomplexes of additive commutative groups in nonnegative cochain degrees. -/
abbrev Bicomplex := HomologicalComplex₂ AddCommGrpCat.{u} (.up ℕ) (.up ℕ)

/-- The native equivalence induced by the forgetful functor from integer modules. -/
def moduleEquivalence : ModuleCat.{u} ℤ ≌ AddCommGrpCat.{u} :=
  (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).asEquivalence

/-- The inverse functor retains each additive group as an integer module. -/
abbrev toModule : AddCommGrpCat.{u} ⥤ ModuleCat.{u} ℤ := moduleEquivalence.{u}.inverse

instance toModule_additive : toModule.{u}.Additive := by
  have : moduleEquivalence.{u}.functor.Additive :=
    (inferInstance : (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).Additive)
  exact moduleEquivalence.{u}.inverse_additive

/-- Applying the native equivalence to both complex degrees. -/
abbrev toModuleBicomplex : Bicomplex.{u} ⥤ FirstQuadrant.{0, u} ℤ :=
  (toModule.{u}.mapHomologicalComplex (.up ℕ)).mapHomologicalComplex (.up ℕ)

private theorem ιTotal_d_up {C : Type*} [Category* C] [Preadditive C]
    (B : HomologicalComplex₂ C (.up ℕ) (.up ℕ)) [B.HasTotal (.up ℕ)]
    (n p q : ℕ) (h : p + q = n) :
    B.ιTotal (.up ℕ) p q n h ≫ (B.total (.up ℕ)).d n (n + 1) =
      (B.d p (p + 1)).f q ≫ B.ιTotal (.up ℕ) (p + 1) q (n + 1) (by
        change p + 1 + q = n + 1; omega) +
      (-1 : ℤˣ) ^ p • ((B.X p).d q (q + 1) ≫
        B.ιTotal (.up ℕ) p (q + 1) (n + 1) (by change p + (q + 1) = n + 1; omega)) := by
  rw [HomologicalComplex₂.total_d, Preadditive.comp_add,
    HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂,
    HomologicalComplex₂.d₁_eq B _ (show (ComplexShape.up ℕ).Rel p (p + 1) from rfl) q _ (by
      change p + 1 + q = n + 1; omega),
    HomologicalComplex₂.d₂_eq B _ p (show (ComplexShape.up ℕ).Rel q (q + 1) from rfl) _ (by
      change p + (q + 1) = n + 1; omega)]
  simp

/-- The canonical degreewise comparison sends each coproduct injection to its image. -/
def mapTotalComparisonX (B : Bicomplex.{u}) (n : ℕ) :
    ((toModuleBicomplex.{u}.obj B).total (.up ℕ)).X n ⟶ toModule.{u}.obj ((B.total (.up ℕ)).X n) :=
  (toModuleBicomplex.{u}.obj B).totalDesc fun p q h ↦ toModule.{u}.map (B.ιTotal (.up ℕ) p q n h)

@[reassoc (attr := simp)]
theorem ι_mapTotalComparisonX (B : Bicomplex.{u}) (n p q : ℕ) (h : p + q = n) :
    (toModuleBicomplex.{u}.obj B).ιTotal (.up ℕ) p q n h ≫ mapTotalComparisonX B n =
      toModule.{u}.map (B.ιTotal (.up ℕ) p q n h) := by
  simp [mapTotalComparisonX]

instance mapTotalComparisonX_isIso (B : Bicomplex.{u}) (n : ℕ) :
    IsIso (mapTotalComparisonX B n) := by
  change IsIso (sigmaComparison toModule.{u}
    (B.toGradedObject.mapObjFun (ComplexShape.π (.up ℕ) (.up ℕ) (.up ℕ)) n))
  infer_instance

/-- The coproduct comparison commutes with the native signed total differentials. -/
def mapTotalComparison (B : Bicomplex.{u}) :
    (toModuleBicomplex.{u}.obj B).total (.up ℕ) ⟶
      (toModule.{u}.mapHomologicalComplex (.up ℕ)).obj (B.total (.up ℕ)) where
  f n := mapTotalComparisonX B n
  comm' i j hij := by
    change i + 1 = j at hij
    subst j
    apply total.hom_ext
    intro p q h
    change (toModuleBicomplex.{u}.obj B).ιTotal (.up ℕ) p q i h ≫
        mapTotalComparisonX B i ≫ toModule.{u}.map ((B.total (.up ℕ)).d i (i + 1)) =
      (toModuleBicomplex.{u}.obj B).ιTotal (.up ℕ) p q i h ≫
        ((toModuleBicomplex.{u}.obj B).total (.up ℕ)).d i (i + 1) ≫ mapTotalComparisonX B (i + 1)
    rw [ι_mapTotalComparisonX_assoc, ← Functor.map_comp, ιTotal_d_up]
    rw [← Category.assoc, ιTotal_d_up, Preadditive.add_comp, Linear.units_smul_comp]
    simp only [Category.assoc, ι_mapTotalComparisonX,
      Functor.map_add, Functor.map_comp, Functor.map_units_smul]
    rfl

/-- The canonical comparison between the total of the image and the image of the total. -/
def mapTotalIso (B : Bicomplex.{u}) :
    (toModuleBicomplex.{u}.obj B).total (.up ℕ) ≅
      (toModule.{u}.mapHomologicalComplex (.up ℕ)).obj (B.total (.up ℕ)) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ asIso (mapTotalComparisonX B n))
    (fun i j _ ↦ (mapTotalComparison B).comm i j)

@[simp]
theorem mapTotalIso_hom (B : Bicomplex.{u}) :
    (mapTotalIso B).hom = mapTotalComparison B := rfl

/-- The normalized total comparison sends each summand to its transported injection. -/
@[reassoc (attr := simp)]
theorem ι_mapTotalComparison_f (B : Bicomplex.{u}) (n p q : ℕ) (h : p + q = n) :
    (toModuleBicomplex.{u}.obj B).ιTotal (.up ℕ) p q n h ≫ (mapTotalComparison B).f n =
      toModule.{u}.map (B.ιTotal (.up ℕ) p q n h) :=
  ι_mapTotalComparisonX B n p q h

@[reassoc]
theorem ι_mapTotalIso_hom_f (B : Bicomplex.{u}) (n p q : ℕ) (h : p + q = n) :
    (toModuleBicomplex.{u}.obj B).ιTotal (.up ℕ) p q n h ≫ (mapTotalIso B).hom.f n =
      toModule.{u}.map (B.ιTotal (.up ℕ) p q n h) :=
  ι_mapTotalComparisonX B n p q h

@[reassoc (attr := simp)]
theorem map_ι_mapTotalIso_inv_f (B : Bicomplex.{u}) (n p q : ℕ) (h : p + q = n) :
    toModule.{u}.map (B.ιTotal (.up ℕ) p q n h) ≫ (mapTotalIso B).inv.f n =
      (toModuleBicomplex.{u}.obj B).ιTotal (.up ℕ) p q n h := by
  rw [← ι_mapTotalIso_hom_f B n p q h]
  rw [Category.assoc, ← HomologicalComplex.comp_f, Iso.hom_inv_id,
    HomologicalComplex.id_f, Category.comp_id]

/-- The total comparison identifies the transported original total map. -/
@[reassoc]
theorem mapTotalIso_naturality {B C : Bicomplex.{u}} (φ : B ⟶ C) :
    total.map (toModuleBicomplex.{u}.map φ) (.up ℕ) ≫ (mapTotalIso C).hom =
      (mapTotalIso B).hom ≫ (toModule.{u}.mapHomologicalComplex (.up ℕ)).map (total.map φ (.up
        ℕ)) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply total.hom_ext
  intro p q h
  change (toModuleBicomplex.{u}.obj B).ιTotal (.up ℕ) p q n h ≫
      (total.map (toModuleBicomplex.{u}.map φ) (.up ℕ)).f n ≫ (mapTotalIso C).hom.f n =
    (toModuleBicomplex.{u}.obj B).ιTotal (.up ℕ) p q n h ≫
      (mapTotalIso B).hom.f n ≫ toModule.{u}.map ((total.map φ (.up ℕ)).f n)
  rw [ιTotal_map_assoc, ι_mapTotalIso_hom_f, ι_mapTotalIso_hom_f_assoc,
    ← Functor.map_comp, ιTotal_map, Functor.map_comp]
  rfl

/-- Rowwise quasi-isomorphisms imply a quasi-isomorphism of the original additive total map. -/
theorem quasiIso_total_of_rowwise {B C : Bicomplex.{u}} (φ : B ⟶ C)
    (hφ : ∀ p : ℕ, QuasiIso (φ.f p)) : QuasiIso (total.map φ (.up ℕ)) := by
  have hrows : ∀ p : ℕ, QuasiIso ((toModuleBicomplex.{u}.map φ).f p) := by
    intro p
    have := hφ p
    change QuasiIso ((toModule.{u}.mapHomologicalComplex (.up ℕ)).map (φ.f p))
    infer_instance
  have : QuasiIso (total.map (toModuleBicomplex.{u}.map φ) (.up ℕ)) :=
    HomologicalComplex₂.quasiIso_total_of_rowwise _ hrows
  have : QuasiIso ((mapTotalIso B).hom ≫
      (toModule.{u}.mapHomologicalComplex (.up ℕ)).map (total.map φ (.up ℕ))) := by
    rw [← mapTotalIso_naturality]
    infer_instance
  have : QuasiIso ((toModule.{u}.mapHomologicalComplex (.up ℕ)).map (total.map φ (.up ℕ))) :=
    quasiIso_of_comp_left (mapTotalIso B).hom _
  exact (quasiIso_map_iff_of_preservesHomology (total.map φ (.up ℕ)) toModule.{u}).mp this

/-- The native functor concentrating the second degree in zero. -/
abbrev SingleSecondZero : CochainComplex (AddCommGrpCat.{u}) ℕ ⥤ Bicomplex.{u} :=
  (CochainComplex.single₀ (AddCommGrpCat.{u})).mapHomologicalComplex (.up ℕ)

/-- Inclusion of a cochain complex in the `(n,0)` summand of its totalization. -/
def singleSecondZeroTotalInclusion (L : CochainComplex (AddCommGrpCat.{u}) ℕ) :
    L ⟶ ((SingleSecondZero.{u}).obj L).total (.up ℕ) where
  f n := ((SingleSecondZero.{u}).obj L).ιTotal (.up ℕ) n 0 n (Nat.add_zero n)
  comm' i j h := by
    change _ ≫ (((SingleSecondZero.{u}).obj L).D₁ (.up ℕ) i j +
      ((SingleSecondZero.{u}).obj L).D₂ (.up ℕ) i j) = L.d i j ≫ _
    rw [Preadditive.comp_add, ι_D₁, ι_D₂,
      d₁_eq _ _ h 0 j (Nat.add_zero j),
      d₂_eq' _ _ i (show (ComplexShape.up ℕ).Rel 0 1 from rfl) j]
    simp [SingleSecondZero, ComplexShape.ε₁]

/-- Projection away from the zero objects in positive second degree. -/
def singleSecondZeroTotalProjection (L : CochainComplex (AddCommGrpCat.{u}) ℕ) (n : ℕ) :
    (((SingleSecondZero.{u}).obj L).total (.up ℕ)).X n ⟶ L.X n :=
  ((SingleSecondZero.{u}).obj L).totalDesc fun p q h ↦
    if hq : q = 0 then by
      subst q
      have hp : p = n := by simpa using h
      subst p
      exact 𝟙 _
    else 0

@[reassoc (attr := simp)]
theorem singleSecondZeroTotalInclusion_projection
    (L : CochainComplex (AddCommGrpCat.{u}) ℕ) (n : ℕ) :
    (singleSecondZeroTotalInclusion L).f n ≫ singleSecondZeroTotalProjection L n = 𝟙 _ := by
  simp [singleSecondZeroTotalInclusion, singleSecondZeroTotalProjection, SingleSecondZero]

@[reassoc (attr := simp)]
theorem singleSecondZeroTotalProjection_inclusion
    (L : CochainComplex (AddCommGrpCat.{u}) ℕ) (n : ℕ) :
    singleSecondZeroTotalProjection L n ≫ (singleSecondZeroTotalInclusion L).f n = 𝟙 _ := by
  apply total.hom_ext
  intro p q h
  by_cases hq : q = 0
  · subst q
    have hp : p = n := by simpa using h
    subst p
    simp [singleSecondZeroTotalProjection, singleSecondZeroTotalInclusion]
  · apply (HomologicalComplex.isZero_single_obj_X (.up ℕ) 0 (L.X p) q hq).eq_of_src

instance singleSecondZeroTotalInclusion_f_isIso
    (L : CochainComplex (AddCommGrpCat.{u}) ℕ) (n : ℕ) :
    IsIso ((singleSecondZeroTotalInclusion L).f n) :=
  ⟨⟨singleSecondZeroTotalProjection L n, singleSecondZeroTotalInclusion_projection L n,
    singleSecondZeroTotalProjection_inclusion L n⟩⟩

/-- The canonical total isomorphism for concentration in second degree zero. -/
def singleSecondZeroTotalIso (L : CochainComplex (AddCommGrpCat.{u}) ℕ) :
    L ≅ ((SingleSecondZero.{u}).obj L).total (.up ℕ) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ asIso ((singleSecondZeroTotalInclusion L).f n))
    (fun i j _ ↦ (singleSecondZeroTotalInclusion L).comm i j)

@[simp]
theorem singleSecondZeroTotalIso_hom (L : CochainComplex (AddCommGrpCat.{u}) ℕ) :
    (singleSecondZeroTotalIso L).hom = singleSecondZeroTotalInclusion L := rfl

/-- The component formula is retained; simplification uses `singleSecondZeroTotalIso_hom`. -/
theorem singleSecondZeroTotalIso_hom_f (L : CochainComplex (AddCommGrpCat.{u}) ℕ) (n : ℕ) :
    (singleSecondZeroTotalIso L).hom.f n =
      ((SingleSecondZero.{u}).obj L).ιTotal (.up ℕ) n 0 n (Nat.add_zero n) := rfl

@[reassoc]
theorem singleSecondZeroTotalIso_naturality
    {L L' : CochainComplex (AddCommGrpCat.{u}) ℕ} (f : L ⟶ L') :
    f ≫ (singleSecondZeroTotalIso L').hom =
      (singleSecondZeroTotalIso L).hom ≫ total.map ((SingleSecondZero.{u}).map f) (.up ℕ) := by
  apply HomologicalComplex.Hom.ext
  funext n
  simp [singleSecondZeroTotalInclusion, SingleSecondZero]

/-- The actual total map induced by an augmentation into a bicomplex. -/
def totalAugmentation {L : CochainComplex (AddCommGrpCat.{u}) ℕ} {B : Bicomplex.{u}}
    (α : (SingleSecondZero.{u}).obj L ⟶ B) : L ⟶ B.total (.up ℕ) :=
  (singleSecondZeroTotalIso L).hom ≫ total.map α (.up ℕ)

@[simp]
theorem totalAugmentation_f {L : CochainComplex (AddCommGrpCat.{u}) ℕ} {B : Bicomplex.{u}}
    (α : (SingleSecondZero.{u}).obj L ⟶ B) (n : ℕ) :
    (totalAugmentation α).f n = (α.f n).f 0 ≫ B.ιTotal (.up ℕ) n 0 n (Nat.add_zero n) := by
  simp [totalAugmentation, singleSecondZeroTotalInclusion]

/-- A commuting augmentation square induces the same commuting square on actual totals. -/
@[reassoc]
theorem totalAugmentation_naturality
    {L L' : CochainComplex (AddCommGrpCat.{u}) ℕ} {B B' : Bicomplex.{u}}
    (α : (SingleSecondZero.{u}).obj L ⟶ B) (α' : (SingleSecondZero.{u}).obj L' ⟶ B')
    (f : L ⟶ L') (g : B ⟶ B')
    (h : (SingleSecondZero.{u}).map f ≫ α' = α ≫ g) :
    f ≫ totalAugmentation α' = totalAugmentation α ≫ total.map g (.up ℕ) := by
  simp only [totalAugmentation, ← Category.assoc]
  rw [singleSecondZeroTotalIso_naturality, Category.assoc, ← total.map_comp, h,
    total.map_comp, Category.assoc]

/-- Naturality of the native signed flip isomorphism. -/
@[reassoc]
theorem totalFlipIso_naturality {B C : Bicomplex.{u}} (φ : B ⟶ C) :
    total.map ((flipFunctor (AddCommGrpCat.{u}) (.up ℕ) (.up ℕ)).map φ) (.up ℕ) ≫
      (C.totalFlipIso (.up ℕ)).hom =
    (B.totalFlipIso (.up ℕ)).hom ≫ total.map φ (.up ℕ) := by
  apply HomologicalComplex.Hom.ext
  funext n
  change (total.map _ (.up ℕ)).f n ≫ (C.totalFlipIso (.up ℕ)).hom.f n =
    (B.totalFlipIso (.up ℕ)).hom.f n ≫ (total.map φ (.up ℕ)).f n
  apply total.hom_ext
  intro q p h
  simp

/-- On bidegree `(q,p)` of the flipped complex, the flip has Koszul sign `(-1)^(p*q)`. -/
@[reassoc]
theorem ιTotal_totalFlipIso_hom (B : Bicomplex.{u}) (p q n : ℕ) (h : q + p = n) :
    B.flip.ιTotal (.up ℕ) q p n h ≫ (B.totalFlipIso (.up ℕ)).hom.f n =
      (-1 : ℤˣ) ^ (p * q) • B.ιTotal (.up ℕ) p q n (by change p + q = n; omega) := by
  exact B.ιTotal_totalFlipIso_f_hom (.up ℕ) p q n h

/-- The augmentation on the other axis, followed by the native signed flip. -/
def totalAugmentationFlip {L : CochainComplex (AddCommGrpCat.{u}) ℕ} {B : Bicomplex.{u}}
    (α : (SingleSecondZero.{u}).obj L ⟶ B.flip) : L ⟶ B.total (.up ℕ) :=
  totalAugmentation α ≫ (B.totalFlipIso (.up ℕ)).hom

@[simp]
theorem totalAugmentationFlip_f {L : CochainComplex (AddCommGrpCat.{u}) ℕ}
    {B : Bicomplex.{u}} (α : (SingleSecondZero.{u}).obj L ⟶ B.flip) (n : ℕ) :
    (totalAugmentationFlip α).f n =
      (α.f n).f 0 ≫ B.ιTotal (.up ℕ) 0 n n (Nat.zero_add n) := by
  simp [totalAugmentationFlip]

/-- A commuting square on the flipped axis commutes after the signed identification. -/
@[reassoc]
theorem totalAugmentationFlip_naturality
    {L L' : CochainComplex (AddCommGrpCat.{u}) ℕ} {B B' : Bicomplex.{u}}
    (α : (SingleSecondZero.{u}).obj L ⟶ B.flip)
    (α' : (SingleSecondZero.{u}).obj L' ⟶ B'.flip)
    (f : L ⟶ L') (g : B ⟶ B')
    (h : (SingleSecondZero.{u}).map f ≫ α' =
      α ≫ (flipFunctor (AddCommGrpCat.{u}) (.up ℕ) (.up ℕ)).map g) :
    f ≫ totalAugmentationFlip α' = totalAugmentationFlip α ≫ total.map g (.up ℕ) := by
  simp only [totalAugmentationFlip, ← Category.assoc]
  rw [totalAugmentation_naturality α α' f _ h, Category.assoc,
    totalFlipIso_naturality, Category.assoc]

/-- A rowwise quasi-isomorphic augmentation gives the actual canonical total quasi-isomorphism. -/
theorem quasiIso_totalAugmentation {L : CochainComplex (AddCommGrpCat.{u}) ℕ}
    {B : Bicomplex.{u}} (α : (SingleSecondZero.{u}).obj L ⟶ B)
    (hα : ∀ p, QuasiIso (α.f p)) : QuasiIso (totalAugmentation α) := by
  have : QuasiIso (HomologicalComplex₂.total.map α (.up ℕ)) :=
    quasiIso_total_of_rowwise α hα
  change QuasiIso ((singleSecondZeroTotalIso L).hom ≫
    HomologicalComplex₂.total.map α (.up ℕ))
  infer_instance

/-- The other-axis augmentation is a quasi-isomorphism after the actual signed flip. -/
theorem quasiIso_totalAugmentationFlip {L : CochainComplex (AddCommGrpCat.{u}) ℕ}
    {B : Bicomplex.{u}} (α : (SingleSecondZero.{u}).obj L ⟶ B.flip)
    (hα : ∀ p, QuasiIso (α.f p)) : QuasiIso (totalAugmentationFlip α) := by
  have : QuasiIso (totalAugmentation α) := quasiIso_totalAugmentation α hα
  change QuasiIso (totalAugmentation α ≫ (B.totalFlipIso (.up ℕ)).hom)
  infer_instance

end HomologicalComplex₂.AddCommGrp
