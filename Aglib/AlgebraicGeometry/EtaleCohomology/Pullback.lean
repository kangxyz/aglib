/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.DegreeZeroPullback
public import Aglib.Algebra.Homology.DerivedCategory.Ext.AcyclicComparison
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.ExactFunctor
public import Aglib.Algebra.Homology.DerivedCategory.ExtRightDerived
public import Aglib.AlgebraicGeometry.EtaleCohomology.DirectImage
public import Aglib.CategoryTheory.Abelian.Injective.ExactFunctor

/-!
# Pullback on original étale cohomology in every degree

The existing exact inverse image and its constant-integer transport induce the
original Ext map in every natural degree. Its degree-zero and degree-one maps
are the existing maps, including the chosen terminal-section normalization.
The bounded-below comparison retains the actual derived unit and single
comparison. Ext and derived-category universes remain independent.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u w w' d d'

attribute [local instance] hasSheafifyLarge

variable {X S : Scheme.{u}}
variable [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{w'} (AbelianSheaf.{u, u + 1} S)]

/-- Pullback on original sheaf cohomology, through the exact inverse image and
its original constant-integer transport. -/
def cohomologyPullback (f : S ⟶ X) (L : AbelianSheaf.{u, u + 1} X) (n : ℕ) :
    Sheaf.H.{w} L n →+ Sheaf.H.{w'} ((inverseImage f).obj L) n :=
  (inverseImage f).extPrecompMap
    (((inverseImageConstantIso f).app (AddCommGrpCat.of (ULift.{u + 1} ℤ))).inv) L n

/-- The map is the original exact-functor Ext map followed by source transport. -/
theorem cohomologyPullback_apply (f : S ⟶ X) (L : AbelianSheaf.{u, u + 1} X)
    (n : ℕ) (a : Sheaf.H.{w} L n) :
    cohomologyPullback f L n a =
      (Abelian.Ext.mk₀
        (((inverseImageConstantIso f).app (AddCommGrpCat.of (ULift.{u + 1} ℤ))).inv)).comp
          (a.mapExactFunctor (inverseImage f)) (zero_add n) := rfl

/-- In degree zero this is the previously normalized map. -/
@[simp]
theorem cohomologyPullback_zero (f : S ⟶ X) (L : AbelianSheaf.{u, u + 1} X) :
    cohomologyPullback f L 0 = h0Pullback f L := rfl

/-- In degree one this is the original H¹ pullback, not a replacement map. -/
@[simp]
theorem cohomologyPullback_one (f : S ⟶ X) (L : AbelianSheaf.{u, u + 1} X) :
    cohomologyPullback f L 1 = h1Pullback f L := rfl

/-- Pullback commutes with every coefficient morphism in every degree. -/
theorem cohomologyPullback_coefficientMap (f : S ⟶ X)
    {L M : AbelianSheaf.{u, u + 1} X} (q : L ⟶ M) (n : ℕ)
    (a : Sheaf.H.{w} L n) :
    cohomologyPullback f M n (Sheaf.H.map q n a) =
      Sheaf.H.map ((inverseImage f).map q) n (cohomologyPullback f L n a) := by
  change (inverseImage f).extPrecompMap _ M n
      (a.comp (Abelian.Ext.mk₀ q) (add_zero n)) =
    ((inverseImage f).extPrecompMap _ L n a).comp
      (Abelian.Ext.mk₀ ((inverseImage f).map q)) (add_zero n)
  rw [Functor.extPrecompMap_comp, Abelian.Ext.mapExactFunctor_mk₀]

/-- Degree-zero pullback is pullback of ordinary terminal-object sections under
exactly the existing sheaf-cohomology equivalence. -/
theorem cohomologyPullback_equiv₀ (f : S ⟶ X) (L : AbelianSheaf.{u, u + 1} X)
    (a : Sheaf.H.{w} L 0) :
    Sheaf.H.equiv₀ ((inverseImage f).obj L) (etaleTerminalIsTerminal S)
        (cohomologyPullback f L 0 a) =
      globalSectionsPullback f L (Sheaf.H.equiv₀ L (etaleTerminalIsTerminal X) a) :=
  h0Pullback_equiv₀ f L a

/-- The same normalization in the direction from actual sections to cohomology. -/
theorem cohomologyPullback_equiv₀_symm (f : S ⟶ X)
    (L : AbelianSheaf.{u, u + 1} X) (z : (globalSections X).obj L) :
    cohomologyPullback f L 0 ((Sheaf.H.equiv₀ L (etaleTerminalIsTerminal X)).symm z) =
      (Sheaf.H.equiv₀ ((inverseImage f).obj L) (etaleTerminalIsTerminal S)).symm
        (globalSectionsPullback f L z) :=
  h0Pullback_equiv₀_symm f L z

/-- Pullback commutes with the original connecting map of any short exact
coefficient sequence in every degree. -/
theorem connecting_cohomologyPullback (f : S ⟶ X)
    (T : ShortComplex (AbelianSheaf.{u, u + 1} X)) (hT : T.ShortExact)
    (i j : ℕ) (h : i + 1 = j) (a : Sheaf.H.{w} T.X₃ i) :
    cohomologyPullback f T.X₁ j (Sheaf.H.δ hT i j h a) =
      Sheaf.H.δ (hT.map_of_exact (inverseImage f)) i j h
        (cohomologyPullback f T.X₃ i a) := by
  change (Abelian.Ext.mk₀ _).comp
      ((a.comp hT.extClass h).mapExactFunctor (inverseImage f)) (zero_add j) =
    ((Abelian.Ext.mk₀ _).comp (a.mapExactFunctor (inverseImage f)) (zero_add i)).comp
      (hT.map_of_exact (inverseImage f)).extClass h
  rw [Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_extClass]
  exact (Abelian.Ext.comp_assoc _ _ _ (zero_add i) h (by omega)).symm

section Derived

variable [HasDerivedCategory.{d} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{d'} (AbelianSheaf.{u, u + 1} S)]
  [EnoughInjectives (AbelianSheaf.{u, u + 1} X)]

/-- Original cohomological pullback agrees with the actual bounded-below derived
map on shifted Hom, using the native exact-single comparison and constant transport. -/
theorem cohomologyPullback_homPlus (f : S ⟶ X)
    (L : AbelianSheaf.{u, u + 1} X) (n : ℕ) (a : Sheaf.H.{w} L n) :
    (cohomologyPullback f L n a).homPlus =
      (DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} S) 0).map
          (((inverseImageConstantIso f).app (AddCommGrpCat.of (ULift.{u + 1} ℤ))).inv) ≫
        (((inverseImage f).rightDerivedFunctorPlusSingleIso 0).inv.app
            ((constantSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}).obj
              (AddCommGrpCat.of (ULift.{u + 1} ℤ))) ≫
          a.homPlus.map (inverseImage f).rightDerivedFunctorPlus ≫
          (((inverseImage f).rightDerivedFunctorPlusSingleIso 0).hom.app L)⟦(n : ℤ)⟧') := by
  rw [Functor.rightDerivedFunctorPlusSingleIso_map_homPlus,
    cohomologyPullback_apply, Abelian.Ext.homPlus_comp, Abelian.Ext.homPlus_mk₀]
  exact ShiftedHom.mk₀_comp (0 : ℤ) rfl _ _

end Derived

section GlobalSections

/-- The existing terminal-object sections functor is the actual right adjoint
of the constant-sheaf functor. -/
instance globalSections_isRightAdjoint (X : Scheme.{u}) :
    (globalSections X).IsRightAdjoint := (constantAdjunction X).isRightAdjoint

instance globalSections_preservesFiniteLimits (X : Scheme.{u}) :
    PreservesFiniteLimits (globalSections X) := by infer_instance

instance globalSections_additive (X : Scheme.{u}) : (globalSections X).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Additive Hom from the original constant-integer sheaf is actual global
sections, using the same adjunction and integer evaluation as `Sheaf.H.equiv₀`. -/
def constantIntegerHomGlobalSectionsIso (X : Scheme.{u}) :
    preadditiveCoyoneda.obj (Opposite.op
      ((constantSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)))) ≅ globalSections X :=
  NatIso.ofComponents
    (fun L => (((constantAdjunction X).homAddEquiv
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)) L).trans
        (AddCommGrpCat.uliftZMultiplesAddEquiv ((globalSections X).obj L))).toAddCommGrpIso)
    (by
      intro L M q
      ext a
      change AddCommGrpCat.uliftZMultiplesAddEquiv ((globalSections X).obj M)
          ((constantAdjunction X).homEquiv _ M (a ≫ q)) =
        (globalSections X).map q
          (AddCommGrpCat.uliftZMultiplesAddEquiv ((globalSections X).obj L)
            ((constantAdjunction X).homEquiv _ L a))
      rw [Adjunction.homEquiv_naturality_right]
      rfl)

/-- Deriving the original Hom-to-sections comparison retains the actual maps
of the native natural-degree right-derived functors. -/
def constantIntegerHomRightDerivedGlobalSectionsIso (X : Scheme.{u}) (n : ℕ) :
    (preadditiveCoyoneda.obj (Opposite.op
      ((constantSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ))))).rightDerived n ≅
      (globalSections X).rightDerived n where
  hom := (constantIntegerHomGlobalSectionsIso X).hom.rightDerived n
  inv := (constantIntegerHomGlobalSectionsIso X).inv.rightDerived n
  hom_inv_id := by
    rw [← NatTrans.rightDerived_comp, Iso.hom_inv_id, NatTrans.rightDerived_id]
  inv_hom_id := by
    rw [← NatTrans.rightDerived_comp, Iso.inv_hom_id, NatTrans.rightDerived_id]

/-- A supplied original injective resolution compares original sheaf cohomology
with the actual right-derived global-sections functor. The Ext universe need
not equal the value universe of global sections. -/
def cohomologyRightDerivedAddEquivOfResolution
    {L : AbelianSheaf.{u, u + 1} X} (I : InjectiveResolution L) (n : ℕ) :
    Sheaf.H.{w} L n ≃+ ((globalSections X).rightDerived n).obj L :=
  (I.extRightDerivedAddEquiv
    ((constantSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))) n).trans
    ((constantIntegerHomRightDerivedGlobalSectionsIso X n).app L).addCommGroupIsoToAddEquiv

/-- The forward map is the original Ext comparison followed by the actual
component of the derived Hom-to-sections isomorphism. -/
theorem cohomologyRightDerivedAddEquivOfResolution_apply
    {L : AbelianSheaf.{u, u + 1} X} (I : InjectiveResolution L) (n : ℕ)
    (a : Sheaf.H.{w} L n) :
    cohomologyRightDerivedAddEquivOfResolution I n a =
      (constantIntegerHomRightDerivedGlobalSectionsIso X n).hom.app L
        (I.extRightDerivedAddEquiv
          ((constantSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}).obj
            (AddCommGrpCat.of (ULift.{u + 1} ℤ))) n a) := rfl

/-- Every supplied coefficient-resolution lift gives the actual coefficient map
under the original cohomology-to-derived-sections comparison. -/
theorem cohomologyRightDerivedAddEquivOfResolution_naturality
    {L M : AbelianSheaf.{u, u + 1} X}
    {I : InjectiveResolution L} {J : InjectiveResolution M} {q : L ⟶ M}
    (φ : InjectiveResolution.Hom I J q) (n : ℕ) (a : Sheaf.H.{w} L n) :
    cohomologyRightDerivedAddEquivOfResolution J n (Sheaf.H.map q n a) =
      ((globalSections X).rightDerived n).map q
        (cohomologyRightDerivedAddEquivOfResolution I n a) := by
  exact InjectiveResolution.extRightDerivedAddEquiv_trans_naturality
    ((constantSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))) n
    (constantIntegerHomRightDerivedGlobalSectionsIso X n) φ a

/-- Original sheaf cohomology computes the original right-derived global
sections, using the canonical native injective resolution. -/
def cohomologyRightDerivedAddEquiv (L : AbelianSheaf.{u, u + 1} X) (n : ℕ) :
    Sheaf.H.{w} L n ≃+ ((globalSections X).rightDerived n).obj L :=
  cohomologyRightDerivedAddEquivOfResolution (injectiveResolution L) n

/-- The comparison is independent of the supplied resolution, while keeping
its original Ext and right-derived forward maps. -/
theorem cohomologyRightDerivedAddEquiv_eq_ofResolution
    {L : AbelianSheaf.{u, u + 1} X} (I : InjectiveResolution L) (n : ℕ) :
    cohomologyRightDerivedAddEquiv L n = cohomologyRightDerivedAddEquivOfResolution I n := by
  exact InjectiveResolution.extRightDerivedAddEquiv_trans_eq
    ((constantSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))) n
    (constantIntegerHomRightDerivedGlobalSectionsIso X n) (injectiveResolution L) I

/-- Coefficient naturality of the actual global-sections derived comparison. -/
theorem cohomologyRightDerivedAddEquiv_naturality
    {L M : AbelianSheaf.{u, u + 1} X} (q : L ⟶ M) (n : ℕ) (a : Sheaf.H.{w} L n) :
    cohomologyRightDerivedAddEquiv M n (Sheaf.H.map q n a) =
      ((globalSections X).rightDerived n).map q (cohomologyRightDerivedAddEquiv L n a) := by
  let φ : InjectiveResolution.Hom (injectiveResolution L) (injectiveResolution M) q :=
    ⟨InjectiveResolution.desc q _ _, by
      simpa only [CochainComplex.single₀_map_f_zero] using
        InjectiveResolution.desc_commutes_zero q (injectiveResolution M)
          (injectiveResolution L)⟩
  exact cohomologyRightDerivedAddEquivOfResolution_naturality φ n a

end GlobalSections

end AlgebraicGeometry.Scheme.EtaleCohomology

/- The original Gamma bridge and the canonical global-sections comparison.
The comparison retains the actual injective-resolution maps and original
constant-integer transport. -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u w w'

attribute [local instance] hasSheafifyLarge

variable {X S : Scheme.{u}}

/-- The existing ordinary pullback on sections is natural in the coefficient. -/
@[reassoc]
theorem globalSectionsPullback_naturality (f : S ⟶ X)
    {L M : AbelianSheaf.{u, u + 1} X} (q : L ⟶ M) :
    (globalSections X).map q ≫ globalSectionsPullback f M =
      globalSectionsPullback f L ≫ (globalSections S).map ((inverseImage f).map q) := by
  have hη := (inverseImageAdjunction f).unit.naturality q
  change q ≫ (inverseImageAdjunction f).unit.app M =
    (inverseImageAdjunction f).unit.app L ≫
      (directImage f).map ((inverseImage f).map q) at hη
  have he := (directImageGlobalSectionsIso f).hom.naturality ((inverseImage f).map q)
  change (globalSections X).map ((directImage f).map ((inverseImage f).map q)) ≫
      (directImageGlobalSectionsIso f).hom.app ((inverseImage f).obj M) =
    (directImageGlobalSectionsIso f).hom.app ((inverseImage f).obj L) ≫
      (globalSections S).map ((inverseImage f).map q) at he
  dsimp only [globalSectionsPullback]
  rw [← CategoryTheory.Functor.map_comp_assoc, hη, CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]
  rw [he]

/-- Natural-transformation packaging of the existing section pullback. -/
def globalSectionsPullbackNatTrans (f : S ⟶ X) :
    globalSections X ⟶ inverseImage f ⋙ globalSections S where
  app := globalSectionsPullback f
  naturality _ _ q := globalSectionsPullback_naturality f q

/-- The original Hom-to-sections comparison identifies the original constant
transport with ordinary pullback of sections. -/
theorem constantIntegerHomGlobalSectionsIso_pullback (f : S ⟶ X)
    {L : AbelianSheaf.{u, u + 1} X}
    (a : (constantSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶ L) :
    (constantIntegerHomGlobalSectionsIso S).hom.app ((inverseImage f).obj L)
        (((inverseImageConstantIso f).app (AddCommGrpCat.of (ULift.{u + 1} ℤ))).inv ≫
          (inverseImage f).map a) =
      globalSectionsPullback f L ((constantIntegerHomGlobalSectionsIso X).hom.app L a) := by
  change AddCommGrpCat.uliftZMultiplesAddEquiv
      ((globalSections S).obj ((inverseImage f).obj L))
      ((constantAdjunction S).homEquiv _ ((inverseImage f).obj L)
        (((inverseImageConstantIso f).app (AddCommGrpCat.of (ULift.{u + 1} ℤ))).inv ≫
          (inverseImage f).map a)) =
    globalSectionsPullback f L
      (AddCommGrpCat.uliftZMultiplesAddEquiv ((globalSections X).obj L)
        ((constantAdjunction X).homEquiv _ L a))
  rw [constantTransport_homEquiv]
  rfl

/-- The actual section-complex map from a supplied exact-functor resolution
lift, without claiming that inverse image preserves injectives. -/
def globalSectionsResolutionPullback (f : S ⟶ X)
    {L : AbelianSheaf.{u, u + 1} X} (I : InjectiveResolution L)
    (J : InjectiveResolution ((inverseImage f).obj L))
    (φ : InjectiveResolution.ExactFunctor.mappedResolution (inverseImage f) I ⟶
      J.cocomplex) :
    ((globalSections X).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex ⟶
      ((globalSections S).mapHomologicalComplex (.up ℤ)).obj J.cochainComplex :=
  (NatTrans.mapHomologicalComplex (globalSectionsPullbackNatTrans f) (.up ℤ)).app
      I.cochainComplex ≫
    ((globalSections S).mapHomologicalComplex (.up ℤ)).map
      (InjectiveResolution.ExactFunctor.extendedLift (inverseImage f) I J φ)

/-- Higher pullback computed by the actual section-complex map and the native
resolution comparisons, independently of Ext. -/
def rightDerivedGlobalSectionsPullbackOfLift (f : S ⟶ X)
    {L : AbelianSheaf.{u, u + 1} X} (I : InjectiveResolution L)
    (J : InjectiveResolution ((inverseImage f).obj L))
    (φ : InjectiveResolution.ExactFunctor.mappedResolution (inverseImage f) I ⟶
      J.cocomplex) (n : ℕ) :
    ((globalSections X).rightDerived n).obj L ⟶
      ((globalSections S).rightDerived n).obj ((inverseImage f).obj L) :=
  (I.isoRightDerivedObjCochain (globalSections X) n).hom ≫
    homologyMap (globalSectionsResolutionPullback f I J φ) (n : ℤ) ≫
    (J.isoRightDerivedObjCochain (globalSections S) n).inv

section Ext

variable [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{w'} (AbelianSheaf.{u, u + 1} S)]

/-- Original pullback carries every original resolution representative to the
cycle determined by the supplied augmentation-compatible exact-functor lift. -/
theorem cohomologyPullback_extMk_ofLift (f : S ⟶ X)
    {L : AbelianSheaf.{u, u + 1} X} (I : InjectiveResolution L)
    (J : InjectiveResolution ((inverseImage f).obj L))
    (φ : InjectiveResolution.ExactFunctor.mappedResolution (inverseImage f) I ⟶
      J.cocomplex)
    (hφ : (inverseImage f).map (I.ι.f 0) ≫ φ.f 0 = J.ι.f 0)
    (n : ℕ)
    (a : (constantSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶ I.cocomplex.X n)
    (ha : a ≫ I.cocomplex.d n (n + 1) = 0) :
    cohomologyPullback f L n (I.extMk a (n + 1) rfl ha) =
      J.extMk
        (((inverseImageConstantIso f).app (AddCommGrpCat.of (ULift.{u + 1} ℤ))).inv ≫
          (inverseImage f).map a ≫ φ.f n)
        (n + 1) rfl (by
          simpa only [Category.assoc, comp_zero] using
            congrArg
              (fun z => ((inverseImageConstantIso f).app
                (AddCommGrpCat.of (ULift.{u + 1} ℤ))).inv ≫ z)
              (InjectiveResolution.ExactFunctor.mappedCycle_comp_d φ n a ha)) := by
  have h := InjectiveResolution.ExactFunctor.mk₀_comp_extMk_mapExactFunctor_comp_mk₀
    (inverseImage f) I J (𝟙 _) φ (by simpa only [Category.id_comp] using hφ) a ha
    (((inverseImageConstantIso f).app (AddCommGrpCat.of (ULift.{u + 1} ℤ))).inv)
  rw [cohomologyPullback_apply]
  simpa only [Abelian.Ext.comp_mk₀_id] using h

end Ext

end AlgebraicGeometry.Scheme.EtaleCohomology
