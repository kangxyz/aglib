/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteCogenerators.AffineIntegralConstants.Sections
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.SchemeTorsorBaseChange

/-! # Fixed-site sections of actual finite-constant direct images

The original pullback of an étale test scheme, followed by its structural
map to the original base, gives coordinates for finite-constant direct images.
The section comparison is the original Over adjunction. Relative scheme maps
act by precomposition with the actual pullback map. No varying-coefficient or
higher-degree continuity theorem is asserted here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.AffineIntegralConstants

universe u

attribute [local instance] hasSheafifyLarge Over.cartesianMonoidalCategory

variable {X : Scheme.{u}}

/-- The actual base-changed étale tests, regarded over their original base. -/
def directImageTests (Y : Over X) : X.Etale ⥤ Over X :=
  siteBaseChange Y.hom ⋙ Scheme.Etale.forget Y.left ⋙ Over.map Y.hom

/-- The original relative pullback map, at a typed object of the over category. -/
def baseChangedTestMap (U : Over X) {Y Z : Over X} (a : Y ⟶ Z) :
    (Over.map Y.hom).obj ((Over.pullback Y.hom).obj U) ⟶
      (Over.map Z.hom).obj ((Over.pullback Z.hom).obj U) :=
  Over.homMk
    (pullback.lift (pullback.fst U.hom Y.hom)
      (pullback.snd U.hom Y.hom ≫ a.left)
      ((pullback.condition (f := U.hom) (g := Y.hom)).trans
        (by rw [Category.assoc, Over.w a])))
    (by simp only [Over.map_obj_hom, Over.pullback_obj_hom, Category.assoc,
      pullback.lift_snd_assoc, Over.w a])

/-- The underlying map is the literal native pullback lift. -/
theorem baseChangedTestMap_left (U : Over X) {Y Z : Over X} (a : Y ⟶ Z) :
    (baseChangedTestMap U a).left =
      pullback.lift (pullback.fst U.hom Y.hom)
        (pullback.snd U.hom Y.hom ≫ a.left)
        ((pullback.condition (f := U.hom) (g := Y.hom)).trans
          (by rw [Category.assoc, Over.w a])) := rfl

/-- The first projection of the actual relative test map. -/
theorem baseChangedTestMap_fst (U : Over X) {Y Z : Over X} (a : Y ⟶ Z) :
    (baseChangedTestMap U a).left ≫ pullback.fst U.hom Z.hom =
      pullback.fst U.hom Y.hom :=
  pullback.lift_fst _ _ _

/-- The second projection of the actual relative test map. -/
theorem baseChangedTestMap_snd (U : Over X) {Y Z : Over X} (a : Y ⟶ Z) :
    (baseChangedTestMap U a).left ≫ pullback.snd U.hom Z.hom =
      pullback.snd U.hom Y.hom ≫ a.left :=
  pullback.lift_snd _ _ _

private theorem pullbackMap_fst {S : Scheme.{u}} (f : S ⟶ X)
    {U V : Over X} (b : U ⟶ V) :
    ((Over.pullback f).map b).left ≫ pullback.fst V.hom f =
      pullback.fst U.hom f ≫ b.left :=
  pullback.lift_fst _ _ _

private theorem pullbackMap_snd {S : Scheme.{u}} (f : S ⟶ X)
    {U V : Over X} (b : U ⟶ V) :
    ((Over.pullback f).map b).left ≫ pullback.snd V.hom f =
      pullback.snd U.hom f :=
  pullback.lift_snd _ _ _

/-- The original pullback map induced by a relative scheme morphism. -/
def directImageTestsMap {Y Z : Over X} (a : Y ⟶ Z) :
    directImageTests Y ⟶ directImageTests Z where
  app U := baseChangedTestMap ((Scheme.Etale.forget X).obj U) a
  naturality {U V} b := by
    let U₀ := (Scheme.Etale.forget X).obj U
    let V₀ := (Scheme.Etale.forget X).obj V
    let b₀ : U₀ ⟶ V₀ := (Scheme.Etale.forget X).map b
    apply Over.OverMorphism.ext
    change ((Over.pullback Y.hom).map b₀).left ≫ (baseChangedTestMap V₀ a).left =
      (baseChangedTestMap U₀ a).left ≫ ((Over.pullback Z.hom).map b₀).left
    apply pullback.hom_ext
    · simp only [Category.assoc]
      rw [baseChangedTestMap_fst V₀ a, pullbackMap_fst Y.hom b₀,
        pullbackMap_fst Z.hom b₀, ← Category.assoc, baseChangedTestMap_fst U₀ a]
    · simp only [Category.assoc]
      rw [baseChangedTestMap_snd V₀ a, ← Category.assoc, pullbackMap_snd Y.hom b₀,
        pullbackMap_snd Z.hom b₀, baseChangedTestMap_snd U₀ a]

/-- The test map for an identity is the identity on the original pullbacks. -/
theorem directImageTestsMap_id (Y : Over X) :
    directImageTestsMap (𝟙 Y) = 𝟙 (directImageTests Y) := by
  apply NatTrans.ext
  funext U
  apply Over.OverMorphism.ext
  change (baseChangedTestMap ((Scheme.Etale.forget X).obj U) (𝟙 Y)).left = 𝟙 _
  apply pullback.hom_ext
  · rw [baseChangedTestMap_fst, Category.id_comp]
  · rw [baseChangedTestMap_snd, Over.id_left, Category.comp_id, Category.id_comp]

/-- Actual relative test maps compose in their scheme direction. -/
theorem directImageTestsMap_comp {Y Z W : Over X} (a : Y ⟶ Z) (b : Z ⟶ W) :
    directImageTestsMap (a ≫ b) = directImageTestsMap a ≫ directImageTestsMap b := by
  apply NatTrans.ext
  funext U
  apply Over.OverMorphism.ext
  change (baseChangedTestMap ((Scheme.Etale.forget X).obj U) (a ≫ b)).left =
    (baseChangedTestMap ((Scheme.Etale.forget X).obj U) a).left ≫
      (baseChangedTestMap ((Scheme.Etale.forget X).obj U) b).left
  apply pullback.hom_ext
  · rw [baseChangedTestMap_fst, Category.assoc, baseChangedTestMap_fst,
      baseChangedTestMap_fst]
  · rw [baseChangedTestMap_snd, Category.assoc, baseChangedTestMap_snd,
      ← Category.assoc (baseChangedTestMap ((Scheme.Etale.forget X).obj U) a).left
        (pullback.snd ((Scheme.Etale.forget X).obj U).hom Z.hom) b.left,
      baseChangedTestMap_snd]
    exact congrArg (fun q => pullback.snd ((Scheme.Etale.forget X).obj U).hom Y.hom ≫ q)
      (Over.comp_left Y Z W a b) |>.trans
      (Category.assoc _ _ _).symm

variable (B : Type u) [AddCommGroup B] [Finite B]

/-- The actual direct image of the represented pullback of the fixed finite
constant coefficient group. -/
abbrev constantRepresentedDirectImage (Y : Over X) : AbelianSheaf.{u, u + 1} X :=
  (directImage Y.hom).obj
    (representedSheaf (baseChangedGroup Y.hom (ConstantFinite.representation B X).group))

/-- Original scheme sections on the original base-changed étale tests. -/
def constantDirectImageCoordinates (Y : Over X) : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  (directImageTests Y).op ⋙ sectionFunctor (ConstantFinite.representation B X).group

/-- The original Over adjunction identifies actual direct-image sections with
maps from the base-changed test scheme to the fixed finite constant group. -/
def constantDirectImageCoordinatesIso (Y : Over X) :
    (constantRepresentedDirectImage B Y).obj ≅ constantDirectImageCoordinates B Y :=
  NatIso.ofComponents (fun U => AddEquiv.toAddCommGrpIso
    ((AddEquiv.ulift.trans
      (SchemeTorsorBaseChange.pullbackSectionMulEquiv Y.hom
        ((Scheme.Etale.forget Y.left).obj ((siteBaseChange Y.hom).obj U.unop))
        (ConstantFinite.representation B X).group).symm.toAdditive).trans
      AddEquiv.ulift.symm)) (by
    intro U V a
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro s
    apply ULift.ext
    change Additive.ofMul
        ((SchemeTorsorBaseChange.pullbackSectionEquiv Y.hom _
          (ConstantFinite.representation B X).group.X).symm
          ((Scheme.Etale.forget Y.left).map ((siteBaseChange Y.hom).map a.unop) ≫
            s.down.toMul)) =
      Additive.ofMul
        ((Over.map Y.hom).map
          ((Scheme.Etale.forget Y.left).map ((siteBaseChange Y.hom).map a.unop)) ≫
          (SchemeTorsorBaseChange.pullbackSectionEquiv Y.hom _
            (ConstantFinite.representation B X).group.X).symm s.down.toMul)
    exact congrArg Additive.ofMul
      (SchemeTorsorBaseChange.pullbackSectionEquiv_symm_naturality Y.hom
        ((Scheme.Etale.forget Y.left).map ((siteBaseChange Y.hom).map a.unop))
        (ConstantFinite.representation B X).group.X s.down.toMul))

/-- Relative coordinate transport is literal precomposition with the original
map of base-changed test schemes. -/
def constantDirectImageCoordinateMap {Y Z : Over X} (a : Y ⟶ Z) :
    constantDirectImageCoordinates B Z ⟶ constantDirectImageCoordinates B Y :=
  Functor.whiskerRight (NatTrans.op (directImageTestsMap a))
    (sectionFunctor (ConstantFinite.representation B X).group)

/-- The coordinate transition keeps the original scheme morphism on every section. -/
theorem constantDirectImageCoordinateMap_apply {Y Z : Over X} (a : Y ⟶ Z)
    (U : X.Etale)
    (s : RepresentedSections (ConstantFinite.representation B X).group
      ((directImageTests Z).obj U)) :
    (constantDirectImageCoordinateMap B a).app (op U) s =
      ULift.up (Additive.ofMul ((directImageTestsMap a).app U ≫ s.down.toMul)) := rfl

/-- The transition between actual direct-image sheaves, transported by the
original Over-adjunction section coordinates. -/
def constantRepresentedDirectImageMap {Y Z : Over X} (a : Y ⟶ Z) :
    constantRepresentedDirectImage B Z ⟶ constantRepresentedDirectImage B Y :=
  ⟨(constantDirectImageCoordinatesIso B Z).hom ≫
    constantDirectImageCoordinateMap B a ≫ (constantDirectImageCoordinatesIso B Y).inv⟩

/-- In the original coordinates, the actual sheaf transition is precisely
precomposition by the original relative pullback map. -/
@[reassoc]
theorem constantRepresentedDirectImageMap_coordinates {Y Z : Over X} (a : Y ⟶ Z) :
    (constantRepresentedDirectImageMap B a).hom ≫
        (constantDirectImageCoordinatesIso B Y).hom =
      (constantDirectImageCoordinatesIso B Z).hom ≫ constantDirectImageCoordinateMap B a := by
  change ((constantDirectImageCoordinatesIso B Z).hom ≫
    constantDirectImageCoordinateMap B a ≫ (constantDirectImageCoordinatesIso B Y).inv) ≫
      (constantDirectImageCoordinatesIso B Y).hom = _
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The actual finite-constant direct-image objects and their original section
transitions form a contravariant functor on relative schemes. -/
def constantRepresentedDirectImageFunctor : (Over X)ᵒᵖ ⥤ AbelianSheaf.{u, u + 1} X where
  obj Y := constantRepresentedDirectImage B Y.unop
  map a := constantRepresentedDirectImageMap B a.unop
  map_id Y := by
    have hi : constantDirectImageCoordinateMap B (𝟙 Y.unop) =
        𝟙 (constantDirectImageCoordinates B Y.unop) := by
      apply NatTrans.ext
      funext U
      change (sectionFunctor (ConstantFinite.representation B X).group).map
          ((directImageTestsMap (𝟙 Y.unop)).app U.unop).op = 𝟙 _
      rw [directImageTestsMap_id]
      exact (sectionFunctor (ConstantFinite.representation B X).group).map_id _
    apply Sheaf.hom_ext
    change (constantDirectImageCoordinatesIso B Y.unop).hom ≫
        constantDirectImageCoordinateMap B (𝟙 Y.unop) ≫
        (constantDirectImageCoordinatesIso B Y.unop).inv = 𝟙 _
    rw [hi]
    simp only [Category.id_comp, Iso.hom_inv_id]
  map_comp {Y Z W} a b := by
    have hc : constantDirectImageCoordinateMap B (b.unop ≫ a.unop) =
        constantDirectImageCoordinateMap B a.unop ≫
          constantDirectImageCoordinateMap B b.unop := by
      apply NatTrans.ext
      funext U
      change (sectionFunctor (ConstantFinite.representation B X).group).map
          ((directImageTestsMap (b.unop ≫ a.unop)).app U.unop).op =
        (sectionFunctor (ConstantFinite.representation B X).group).map
            ((directImageTestsMap a.unop).app U.unop).op ≫
          (sectionFunctor (ConstantFinite.representation B X).group).map
            ((directImageTestsMap b.unop).app U.unop).op
      rw [directImageTestsMap_comp]
      exact (sectionFunctor (ConstantFinite.representation B X).group).map_comp _ _
    apply Sheaf.hom_ext
    change (constantDirectImageCoordinatesIso B Y.unop).hom ≫
        constantDirectImageCoordinateMap B (b.unop ≫ a.unop) ≫
        (constantDirectImageCoordinatesIso B W.unop).inv =
      ((constantDirectImageCoordinatesIso B Y.unop).hom ≫
        constantDirectImageCoordinateMap B a.unop ≫
        (constantDirectImageCoordinatesIso B Z.unop).inv) ≫
      ((constantDirectImageCoordinatesIso B Z.unop).hom ≫
        constantDirectImageCoordinateMap B b.unop ≫
        (constantDirectImageCoordinatesIso B W.unop).inv)
    rw [hc]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- Each displayed object is an actual finite-constant pushforward. The
comparison uses the original represented pullback and original constant transport. -/
def constantRepresentedDirectImageIso (Y : Over X) :
    constantRepresentedDirectImage B Y ≅
      (directImage Y.hom).obj (ConstantFinite.coefficient B Y.left) :=
  (directImage Y.hom).mapIso
    ((representedSheafBaseChangeIso Y.hom (ConstantFinite.representation B X).group).symm ≪≫
      (inverseImage Y.hom).mapIso (ConstantFinite.representation B X).iso ≪≫
        (inverseImageConstantIso Y.hom).app (ConstantFinite.value B))

/-- The original adjunction unit, with its original represented coefficient
comparison, maps into the displayed actual direct image. -/
def constantRepresentedDirectImageUnit (Y : Over X) :
    ConstantFinite.coefficient B X ⟶ constantRepresentedDirectImage B Y :=
  (ConstantFinite.representation B X).iso.inv ≫
    SchemeTorsorBaseChange.representedCoefficientUnit Y.hom
      (ConstantFinite.representation B X).group

private theorem originalUnitTransport
    {C D : Type*} [Category* C] [Category* D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    {M N : C} (e : M ≅ N) {P Q : D} (t : L.obj M ≅ P) (c : L.obj N ≅ Q)
    (v : M ⟶ R.obj P) (hv : adj.unit.app M ≫ R.map t.hom = v) :
    e.inv ≫ v ≫ R.map (t.inv ≫ L.map e.hom ≫ c.hom) =
      adj.unit.app N ≫ R.map c.hom := by
  have hn : e.inv ≫ adj.unit.app M =
      adj.unit.app N ≫ R.map (L.map e.inv) := adj.unit.naturality e.inv
  calc
    e.inv ≫ v ≫ R.map (t.inv ≫ L.map e.hom ≫ c.hom) =
        e.inv ≫ adj.unit.app M ≫ R.map (t.hom ≫ t.inv ≫ L.map e.hom ≫ c.hom) := by
      rw [← hv]
      simp only [Functor.map_comp, Category.assoc]
    _ = e.inv ≫ adj.unit.app M ≫ R.map (L.map e.hom ≫ c.hom) := by
      rw [Iso.hom_inv_id_assoc]
    _ = adj.unit.app N ≫ R.map (L.map e.inv) ≫ R.map (L.map e.hom) ≫ R.map c.hom := by
      rw [R.map_comp, ← Category.assoc e.inv (adj.unit.app M), hn]
      simp only [Category.assoc]
    _ = adj.unit.app N ≫ R.map (L.map (e.inv ≫ e.hom)) ≫ R.map c.hom := by
      simp only [Functor.map_comp, Category.assoc]
    _ = adj.unit.app N ≫ R.map c.hom := by
      have hid : R.map (L.map (e.inv ≫ e.hom)) = 𝟙 (R.obj (L.obj N)) :=
        (congrArg (fun q => R.map (L.map q)) e.inv_hom_id).trans
          ((congrArg R.map (L.map_id N)).trans (R.map_id (L.obj N)))
      exact (congrArg (fun q => adj.unit.app N ≫ q ≫ R.map c.hom) hid).trans
        (congrArg (fun q => adj.unit.app N ≫ q) (Category.id_comp (R.map c.hom)))

/-- Transport to the actual constant coefficient gives precisely the original
adjunction unit followed by the original inverse-image constant isomorphism. -/
theorem constantRepresentedDirectImageUnit_original (Y : Over X) :
    constantRepresentedDirectImageUnit B Y ≫ (constantRepresentedDirectImageIso B Y).hom =
      (inverseImageAdjunction Y.hom).unit.app (ConstantFinite.coefficient B X) ≫
        (directImage Y.hom).map
          ((inverseImageConstantIso Y.hom).hom.app (ConstantFinite.value B)) := by
  exact originalUnitTransport (inverseImageAdjunction Y.hom)
    (ConstantFinite.representation B X).iso
    (representedSheafBaseChangeIso Y.hom (ConstantFinite.representation B X).group)
    ((inverseImageConstantIso Y.hom).app (ConstantFinite.value B))
    (SchemeTorsorBaseChange.representedCoefficientUnit Y.hom
      (ConstantFinite.representation B X).group)
    (SchemeTorsorBaseChange.representedSheafBaseChangeIso_unit Y.hom
      (ConstantFinite.representation B X).group)

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.AffineIntegralConstants
