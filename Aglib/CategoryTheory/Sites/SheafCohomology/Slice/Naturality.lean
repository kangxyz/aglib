/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.Slice.Comparison
public import Aglib.CategoryTheory.Sites.SheafCohomology.Slice.OverMap

/-!
# Naturality for the original slice restriction

The maps here use exact precomposition by `Over.map`, the original constant
sheafification unit, and the native iterated restriction isomorphism.
-/

@[expose] public noncomputable section

universe w₀ w₁ w₂ t v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

namespace CategoryTheory.Sheaf.SliceCohomology

section ExtNaturality

universe e₀ e₁ e₂

variable {A B D : Type*} [Category* A] [Category* B] [Category* D]
  [Abelian A] [Abelian B] [Abelian D]
  [HasExt.{e₀} A] [HasExt.{e₁} B] [HasExt.{e₂} D]
  (R : A ⥤ B) (S : A ⥤ D) (T : B ⥤ D)
  [R.Additive] [S.Additive] [T.Additive]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  [PreservesFiniteLimits S] [PreservesFiniteColimits S]
  [PreservesFiniteLimits T] [PreservesFiniteColimits T]

/-- The additive map on Ext induced by an exact functor and actual endpoint maps. -/
def extRestrictionMap {X Y : B} {X' Y' : D}
    (a : X' ⟶ T.obj X) (b : T.obj Y ⟶ Y') (n : ℕ) :
    Ext.{e₁} X Y n →+ Ext.{e₂} X' Y' n where
  toFun x := ((Ext.mk₀ a).comp (x.mapExactFunctor T) (Nat.zero_add n)).comp
    (Ext.mk₀ b) (Nat.add_zero n)
  map_zero' := by simp
  map_add' x y := by simp [Ext.mapExactFunctor_add, Ext.comp_add, Ext.add_comp]

/-- A source square for exact functors induces the corresponding square on Ext.
The homological calculation is performed abstractly, before site specialization. -/
theorem extRestrictionCompatibility (τ : R ⋙ T ⟶ S)
    {X Y F : A} {Z : B} {W : D} (q : W ⟶ T.obj Z)
    (a : Z ⟶ R.obj X) (b : W ⟶ S.obj Y) (g : Y ⟶ X)
    (h : q ≫ T.map a ≫ τ.app X = b ≫ S.map g)
    {n : ℕ} (x : Ext X F n) :
    ((Ext.mk₀ q).comp
      (((Ext.mk₀ a).comp (x.mapExactFunctor R) (Nat.zero_add n)).mapExactFunctor T)
      (Nat.zero_add n)).comp (Ext.mk₀ (τ.app F)) (Nat.add_zero n) =
    (Ext.mk₀ b).comp
      (((Ext.mk₀ g).comp x (Nat.zero_add n)).mapExactFunctor S) (Nat.zero_add n) := by
  simp only [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]
  rw [← Ext.comp_mapExactFunctor]
  simp only [Ext.comp_assoc_of_third_deg_zero]
  rw [Ext.mapExactFunctor_comp_mk₀_natTransApp x τ]
  simp only [Ext.mk₀_comp_mk₀_assoc]
  rw [h]

end ExtNaturality

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {V U : C} (f : V ⟶ U)
  [HasSheafify J AddCommGrpCat.{max v t}]
  [HasSheafify (J.over U) AddCommGrpCat.{max v t}]
  [HasSheafify (J.over V) AddCommGrpCat.{max v t}]

/-- The native iterated restriction isomorphisms, bundled naturally in coefficients. -/
def overMapRestrictionIso :
    J.overPullback AddCommGrpCat.{max v t} U ⋙ overMapRestriction J f ≅
      J.overPullback AddCommGrpCat.{max v t} V :=
  NatIso.ofComponents (fun F => F.pushforwardOverMapIso f) (by
    intro F G g
    ext W x
    rfl)

omit [HasSheafify (J.over U) AddCommGrpCat.{max v t}]
  [HasSheafify (J.over V) AddCommGrpCat.{max v t}] in
set_option backward.isDefEq.respectTransparency false in
/-- The representing equivalence is natural in the original representing object. -/
theorem freeSections_naturality (F : Sheaf J AddCommGrpCat.{max v t})
    (a : Hypercohomology.freeAbelianSheaf J U ⟶ F) :
    Hypercohomology.sectionsAddEquiv J V F
      ((Hypercohomology.freeAbelianSheafFunctor J).map f ≫ a) =
      F.obj.map f.op (Hypercohomology.sectionsAddEquiv J U F a) := by
  change uliftYonedaEquiv.{t}
    (((AddCommGrpCat.adj.{max v t}.whiskerRight Cᵒᵖ).homEquiv _ F.obj)
      (((sheafificationAdjunction J AddCommGrpCat.{max v t}).homEquiv _ F)
        ((presheafToSheaf J AddCommGrpCat.{max v t}).map _ ≫ a))) = _
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_left]
  exact (uliftYonedaEquiv_naturality.{t} _ f.op).symm

/-- Constant integer source maps are evaluated at the genuine terminal object. -/
def sliceSectionsAddEquiv (F : Sheaf (J.over U) AddCommGrpCat.{max v t}) :
    (sliceIntegers J U ⟶ F) ≃+ F.obj.obj (op (Over.mk (𝟙 U))) :=
  ((constantSheafAdj (J.over U) AddCommGrpCat.{max v t} Over.mkIdTerminal).homAddEquiv
    (AddCommGrpCat.of (ULift.{max v t} ℤ)) F).trans
    (AddCommGrpCat.uliftZMultiplesAddEquiv.{max v t} _)

omit [HasSheafify J AddCommGrpCat.{max v t}] in
/-- Evaluation commutes with actual coefficient maps. -/
theorem sliceSections_postcomp {F G : Sheaf (J.over U) AddCommGrpCat.{max v t}}
    (a : sliceIntegers J U ⟶ F) (g : F ⟶ G) :
    sliceSectionsAddEquiv J G (a ≫ g) =
      g.hom.app (op (Over.mk (𝟙 U))) (sliceSectionsAddEquiv J F a) := by
  dsimp only [sliceSectionsAddEquiv, AddEquiv.trans_apply, Adjunction.homAddEquiv_apply]
  rw [Adjunction.homEquiv_naturality_right]
  rfl

omit [HasSheafify J AddCommGrpCat.{max v t}] in
set_option backward.isDefEq.respectTransparency false in
/-- The actual slice restriction acts on constant-source sections by `F.map f.op`. -/
theorem sliceSections_restriction (F : Sheaf J AddCommGrpCat.{max v t})
    (a : sliceIntegers J U ⟶ F.over U) :
    sliceSectionsAddEquiv J (F.over V)
      (constantOverMap J f (AddCommGrpCat.of (ULift.{max v t} ℤ)) ≫
        (overMapRestriction J f).map a ≫ (F.pushforwardOverMapIso f).hom) =
      F.obj.map f.op (sliceSectionsAddEquiv J (F.over U) a) := by
  rw [← Category.assoc, sliceSections_postcomp]
  dsimp only [sliceSectionsAddEquiv, AddEquiv.trans_apply, Adjunction.homAddEquiv_apply]
  rw [constantOverMap_sections]
  change F.obj.map (Over.mkIdTerminal.from
    ((Over.map f).obj (Over.mk (𝟙 V)))).left.op _ = F.obj.map f.op _
  simp only [Over.mkIdTerminal_from_left, Over.map_obj_hom]
  rw [show (Over.mk (𝟙 V)).hom = 𝟙 V from rfl]
  exact congrArg (fun k : V ⟶ U =>
    F.obj.map k.op (sliceSectionsAddEquiv J (F.over U) a)) (Category.id_comp f)

set_option backward.isDefEq.respectTransparency false in
/-- The native constant comparison and native iterated restriction identify the
source unit with the actual map of free representable sheaves. -/
theorem sliceComparisonUnit_naturality :
    constantOverMap J f (AddCommGrpCat.of (ULift.{max v t} ℤ)) ≫
      (overMapRestriction J f).map (sliceComparisonUnit J U) ≫
        ((Hypercohomology.freeAbelianSheaf J U).pushforwardOverMapIso f).hom =
    sliceComparisonUnit J V ≫ (J.overPullback AddCommGrpCat.{max v t} V).map
      ((Hypercohomology.freeAbelianSheafFunctor J).map f) := by
  apply (sliceSectionsAddEquiv J _).injective
  rw [sliceSections_restriction, sliceSections_postcomp]
  have hU : sliceSectionsAddEquiv J _ (sliceComparisonUnit J U) =
      Hypercohomology.sectionsAddEquiv J U _ (𝟙 _) := sliceComparisonUnit_generator J U
  have hV : sliceSectionsAddEquiv J _ (sliceComparisonUnit J V) =
      Hypercohomology.sectionsAddEquiv J V _ (𝟙 _) := sliceComparisonUnit_generator J V
  rw [hU, hV]
  change (Hypercohomology.freeAbelianSheaf J U).obj.map f.op
      (Hypercohomology.sectionsEquiv J U _ (𝟙 _)) =
    ((Hypercohomology.freeAbelianSheafFunctor J).map f).hom.app (op V)
      (Hypercohomology.sectionsEquiv J V _ (𝟙 _))
  rw [← Hypercohomology.sectionsEquiv_naturality, Category.id_comp]
  exact (freeSections_naturality J f (Hypercohomology.freeAbelianSheaf J U) (𝟙 _)).symm

variable
  [J.WEqualsLocallyBijective AddCommGrpCat.{max v t}]
  [J.HasSheafCompose (forget AddCommGrpCat.{max v t})]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max v t}]
  [(J.over U).HasSheafCompose (forget AddCommGrpCat.{max v t})]
  [(J.over V).WEqualsLocallyBijective AddCommGrpCat.{max v t}]
  [(J.over V).HasSheafCompose (forget AddCommGrpCat.{max v t})]

variable [HasExt.{w₀} (Sheaf J AddCommGrpCat.{max v t})]
  [HasExt.{w₁} (Sheaf (J.over U) AddCommGrpCat.{max v t})]
  [HasExt.{w₂} (Sheaf (J.over V) AddCommGrpCat.{max v t})]

/-- Restriction on original slice cohomology, defined by the exact functor, its
constant-source comparison, and the native coefficient isomorphism. -/
def sliceRestriction (F : Sheaf J AddCommGrpCat.{max v t}) (n : ℕ) :
    Sheaf.H.{w₁} (F.over U) n →+ Sheaf.H.{w₂} (F.over V) n :=
  extRestrictionMap (overMapRestriction J f)
    (constantOverMap J f (AddCommGrpCat.of (ULift.{max v t} ℤ)))
    ((overMapRestrictionIso J f).hom.app F) n

omit [HasSheafify J AddCommGrpCat.{max v t}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max v t}]
  [J.HasSheafCompose (forget AddCommGrpCat.{max v t})]
  [HasExt.{w₀} (Sheaf J AddCommGrpCat.{max v t})] in
/-- The actual functor and endpoint maps defining restriction on slice cohomology. -/
theorem sliceRestriction_apply (F : Sheaf J AddCommGrpCat.{max v t}) (n : ℕ)
    (x : Sheaf.H.{w₁} (F.over U) n) :
    sliceRestriction.{w₁, w₂, t, v, u} J f F n x =
      ((Ext.mk₀ (constantOverMap J f (AddCommGrpCat.of (ULift.{max v t} ℤ)))).comp
        (x.mapExactFunctor (overMapRestriction J f)) (Nat.zero_add n)).comp
          (Ext.mk₀ ((overMapRestrictionIso J f).hom.app F)) (Nat.add_zero n) := rfl

/-- The slice comparison commutes with the original presheaf restriction map. -/
theorem sliceComparison_restriction (F : Sheaf J AddCommGrpCat.{max v t})
    (n : ℕ) (x : LargeCohomology.H.{w₀} J F n U) :
    sliceRestriction.{w₁, w₂, t, v, u} J f F n (sliceComparison.{w₀, w₁, t, v, u} J U F n x) =
      sliceComparison.{w₀, w₂, t, v, u} J V F n ((LargeCohomology.presheaf J F n).map f.op x) := by
  change Ext.{w₀} (Hypercohomology.freeAbelianSheaf.{t} J U) F n at x
  let g := (Hypercohomology.freeAbelianSheafFunctor J).map f
  let y := (Ext.mk₀ g).comp x (Nat.zero_add n)
  have h := extRestrictionCompatibility
    (J.overPullback AddCommGrpCat.{max v t} U) (J.overPullback AddCommGrpCat.{max v t} V)
    (overMapRestriction J f) (overMapRestrictionIso J f).hom
    (constantOverMap J f (AddCommGrpCat.of (ULift.{max v t} ℤ)))
    (sliceComparisonUnit J U) (sliceComparisonUnit J V) g
    (sliceComparisonUnit_naturality J f) x
  exact (congrArg (sliceRestriction.{w₁, w₂, t, v, u} J f F n)
    (sliceComparison_apply J U F n x)).trans
    ((sliceRestriction_apply J f F n _).trans
      (h.trans ((sliceComparison_apply J V F n y).symm.trans
        (congrArg (sliceComparison.{w₀, w₂, t, v, u} J V F n)
          (LargeCohomology.restriction_apply J F n f x).symm))))

end CategoryTheory.Sheaf.SliceCohomology

namespace CategoryTheory.Sheaf.SliceCohomology

universe w

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max v t}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max v t}]
  [J.HasSheafCompose (forget AddCommGrpCat.{max v t})]
  [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{max v t}]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max v t}]
  [∀ U : C, (J.over U).HasSheafCompose (forget AddCommGrpCat.{max v t})]
  [HasExt.{w₀} (Sheaf J AddCommGrpCat.{max v t})]
  [∀ U : C, HasExt.{w} (Sheaf (J.over U) AddCommGrpCat.{max v t})]

/-- The original slice restriction preserves identities. -/
theorem sliceRestriction_id (U : C) (F : Sheaf J AddCommGrpCat.{max v t})
    (n : ℕ) (x : Sheaf.H.{w} (F.over U) n) :
    sliceRestriction.{w, w, t, v, u} J (𝟙 U) F n x = x := by
  obtain ⟨y, rfl⟩ := (sliceComparison.{w₀, w, t, v, u} J U F n).surjective x
  rw [sliceComparison_restriction]
  simp

/-- The original slice restriction preserves composition contravariantly. -/
theorem sliceRestriction_comp {W V U : C} (f : W ⟶ V) (g : V ⟶ U)
    (F : Sheaf J AddCommGrpCat.{max v t}) (n : ℕ) (x : Sheaf.H.{w} (F.over U) n) :
    sliceRestriction.{w, w, t, v, u} J (f ≫ g) F n x =
      sliceRestriction.{w, w, t, v, u} J f F n (sliceRestriction.{w, w, t, v, u} J g F n x) := by
  obtain ⟨y, rfl⟩ := (sliceComparison.{w₀, w, t, v, u} J U F n).surjective x
  rw [sliceComparison_restriction, sliceComparison_restriction, sliceComparison_restriction]
  simp

end CategoryTheory.Sheaf.SliceCohomology

namespace CategoryTheory.Sheaf.SliceCohomology

section SourceExtTransfer

universe uA vA uB vB uD vD eA eB eD

variable {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
  {D : Type uD} [Category.{vD} D] [Abelian A] [Abelian B] [Abelian D]
  [HasExt.{eA} A] [HasExt.{eB} B] [HasExt.{eD} D]
  (R : A ⥤ B) (S : A ⥤ D) (T : B ⥤ D)
  [R.Additive] [S.Additive] [T.Additive]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  [PreservesFiniteLimits S] [PreservesFiniteColimits S]
  [PreservesFiniteLimits T] [PreservesFiniteColimits T]
  {L : D ⥤ B} [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]

/-- The complete original adjunction-source comparison carries an exact-functor
source square to the corresponding Ext square, with the actual coefficient iso. -/
theorem sourceExtComparison_compatibility (adj : L ⊣ T)
    {X Y F : A} {Z : B} {W : D} (e : L.obj W ≅ Z) (τ : R ⋙ T ≅ S)
    (a : Z ⟶ R.obj X) (b : W ⟶ S.obj Y) (g : Y ⟶ X)
    (hsource : (adj.unit.app W ≫ T.map e.hom) ≫ T.map a ≫ τ.hom.app X =
      b ≫ S.map g) {n : ℕ} (x : Ext.{eA} X F n) :
    (adj.sourceExtComparison e (R.obj F) n
      ((Ext.mk₀ a).comp (x.mapExactFunctor R) (Nat.zero_add n))).comp
        (Ext.mk₀ (τ.hom.app F)) (Nat.add_zero n) =
      (Ext.mk₀ b).comp
        (((Ext.mk₀ g).comp x (Nat.zero_add n)).mapExactFunctor S) (Nat.zero_add n) := by
  rw [Adjunction.sourceExtComparison_apply]
  exact extRestrictionCompatibility R S T τ.hom
    (adj.unit.app W ≫ T.map e.hom) a b g hsource x

omit [HasExt.{eD} D] in
/-- A zero under the original source precomposition transfers through the full
actual adjunction/source comparison. Only its intermediate Ext size is selected
internally; the source and target Ext worlds stay independent. -/
theorem extPrecomp_eq_zero_of_precomp_eq_zero (adj : L ⊣ T)
    {X Y F : A} {Z : B} {W : D} (e : L.obj W ≅ Z) (τ : R ⋙ T ≅ S)
    (a : Z ⟶ R.obj X) (b : W ⟶ S.obj Y) (g : Y ⟶ X)
    (hsource : (adj.unit.app W ≫ T.map e.hom) ≫ T.map a ≫ τ.hom.app X =
      b ≫ S.map g) {n : ℕ} (x : Ext.{eA} X F n)
    (hx : (Ext.mk₀ g).comp x (Nat.zero_add n) = 0) :
    (Ext.mk₀ a).comp (x.mapExactFunctor R) (Nat.zero_add n) = 0 := by
  let : HasExt.{max uD vD} D := HasExt.standard D
  let c := (adj.sourceExtComparison e (R.obj F) n).trans
    (((extFunctorObj W n).mapIso (τ.app F)).addCommGroupIsoToAddEquiv)
  apply c.injective
  rw [map_zero]
  have h := sourceExtComparison_compatibility R S T adj e τ a b g hsource x
  exact h.trans (by
    rw [hx, Ext.mapExactFunctor_zero, Ext.comp_zero]
    rfl)

end SourceExtTransfer

end CategoryTheory.Sheaf.SliceCohomology
