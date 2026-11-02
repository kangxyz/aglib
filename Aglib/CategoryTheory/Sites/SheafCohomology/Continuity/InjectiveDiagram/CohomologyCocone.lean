/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Abelian.Ext.SourceTransfer
public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.RepresentedDiagram
public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.InjectiveDiagram.CoefficientSquares

/-! # Original represented cohomology transfers and apex cocones

Exact image, original source transport and the given coefficient morphism
define the transfer. Its composition is proved on those same maps. A single
cartesian source system supplies the source coherence. No continuity or
invertibility of the cohomology comparison is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits CategoryTheory.Abelian



namespace CategoryTheory.InjectiveSystem

universe uJ vJ uA vA uI vI e

variable {J : Type uJ} [Category.{vJ} J]
  {A : J → Type uA} [∀ j, Category.{vA} (A j)] (D : AdjunctionData A)

/-- Equality transport of the original right-side transition. -/
theorem System.map_transport (U : System D) {i j : J} (a a' : i ⟶ j) (h : a' = a) :
    U.map a' ≫ (eqToIso (congrArg D.right h)).hom.app (U.obj j) = U.map a := by
  cases h
  simp only [eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.comp_id]

/-- The actual inverse source maps retain the original whole triangle comparison. -/
theorem System.leftMap_inv_triangle (U : System D)
    [∀ {i j : J} (a : i ⟶ j), IsIso (U.leftMap D a)]
    {i j t : J} (a : i ⟶ j) (p : i ⟶ t) (q : j ⟶ t) (h : a ≫ q = p) :
    inv (U.leftMap D p) ≫ (D.triangleIso p a q h).hom.app (U.obj i) =
      inv (U.leftMap D q) ≫ (D.left q).map (inv (U.leftMap D a)) := by
  cases h
  simpa only [AdjunctionData.triangleIso, eqToIso_refl, Iso.refl_trans] using
    System.leftMap_inv_comp D U a q

variable {I : Type uI} [Category.{vI} I] (X : I ⥤ J)

/-- Restrict the one actual system, retaining its literal objects and right maps. -/
def System.reindex (U : System D) : System (D.reindex X) where
  obj i := U.obj (X.obj i)
  map a := U.map (X.map a)
  map_id i := by
    have h := congrArg (fun f => f ≫ (D.idIso (X.obj i)).hom.app (U.obj (X.obj i)))
      (U.map_transport D (𝟙 (X.obj i)) (X.map (𝟙 i)) (X.map_id i))
    have hfinal := h.trans (U.map_id (X.obj i))
    simpa only [AdjunctionData.reindex, Iso.trans_hom, NatTrans.comp_app,
      Category.assoc] using hfinal
  map_comp {i j k} a b := by
    have h := congrArg
      (fun f => f ≫ (D.compIso (X.map a) (X.map b)).hom.app (U.obj (X.obj k)))
      (U.map_transport D (X.map a ≫ X.map b) (X.map (a ≫ b)) (X.map_comp a b))
    have hfinal := h.trans (U.map_comp (X.map a) (X.map b))
    simpa only [AdjunctionData.reindex, Iso.trans_hom, NatTrans.comp_app,
      Category.assoc] using hfinal

/-- Restriction retains the original source object itself. -/
theorem System.reindex_obj (U : System D) (i : I) :
    (U.reindex D X).obj i = U.obj (X.obj i) := rfl

/-- Restriction retains the original transition itself. -/
theorem System.reindex_map (U : System D) {i j : I} (a : i ⟶ j) :
    (U.reindex D X).map a = U.map (X.map a) := rfl

/-- The actual reindexed adjunction gives the same original left transition. -/
theorem System.reindex_leftMap (U : System D) {i j : I} (a : i ⟶ j) :
    (U.reindex D X).leftMap (D.reindex X) a = U.leftMap D (X.map a) := rfl

instance System.reindex_leftMap_isIso (U : System D)
    [∀ {i j : J} (a : i ⟶ j), IsIso (U.leftMap D a)] {i j : I} (a : i ⟶ j) :
    IsIso ((U.reindex D X).leftMap (D.reindex X) a) := by
  change IsIso (U.leftMap D (X.map a))
  infer_instance

section Transfers

variable (U : System D) [∀ {i j : J} (a : i ⟶ j), IsIso (U.leftMap D a)]
  [∀ j, Abelian (A j)]
  [∀ {i j : J} (a : i ⟶ j), (D.left a).Additive]
  [∀ {i j : J} (a : i ⟶ j), PreservesFiniteLimits (D.left a)]
  [∀ {i j : J} (a : i ⟶ j), PreservesFiniteColimits (D.left a)]

/-- The original source system and coefficient arrow define the actual transfer. -/
def System.extTransfer {i j : J} [HasExt.{e} (A i)] [HasExt.{e} (A j)]
    (a : i ⟶ j) {F : A i} {G : A j}
    (φ : (D.left a).obj F ⟶ G) (n : ℕ) :
    AddCommGrpCat.of (Ext.{e} (U.obj i) F n) ⟶
      AddCommGrpCat.of (Ext.{e} (U.obj j) G n) :=
  AddCommGrpCat.ofHom ((D.left a).extCoefficientTransfer (inv (U.leftMap D a)) φ n)

/-- Actual source-system composition supplies the complete transfer law. -/
theorem System.extTransfer_comp {i j k : J}
    [HasExt.{e} (A i)] [HasExt.{e} (A j)] [HasExt.{e} (A k)]
    (a : i ⟶ j) (b : j ⟶ k)
    {F : A i} {G : A j} {H : A k}
    (φ : (D.left a).obj F ⟶ G) (ψ : (D.left b).obj G ⟶ H) (n : ℕ) :
    U.extTransfer D a φ n ≫ U.extTransfer D b ψ n =
      U.extTransfer D (a ≫ b)
        ((D.leftCompIso a b).hom.app F ≫ (D.left b).map φ ≫ ψ) n := by
  ext x
  exact DFunLike.congr_fun
    (Functor.extCoefficientTransfer_comp (D.left a) (D.left b) (D.left (a ≫ b))
      (D.leftCompIso a b) (inv (U.leftMap D a)) (inv (U.leftMap D b))
      (inv (U.leftMap D (a ≫ b))) (System.leftMap_inv_comp D U a b) φ ψ n) x

/-- The same original source unit gives the identity transfer. -/
theorem System.extTransfer_id (i : J) [HasExt.{e} (A i)] (F : A i) (n : ℕ) :
    U.extTransfer D (𝟙 i) ((D.leftIdIso i).hom.app F) n = 𝟙 _ := by
  ext x
  have hs : inv (U.leftMap D (𝟙 i)) ≫ (D.leftIdIso i).hom.app (U.obj i) = 𝟙 _ := by
    rw [← System.leftMap_id D U i, IsIso.inv_hom_id]
  exact DFunLike.congr_fun
    (Functor.extCoefficientTransfer_id (D.left (𝟙 i)) (D.leftIdIso i)
      (inv (U.leftMap D (𝟙 i))) hs F n) x

/-- Coefficient naturality retains the actual system transfer itself. -/
theorem System.extTransfer_naturality {i j : J} [HasExt.{e} (A i)] [HasExt.{e} (A j)]
    (a : i ⟶ j)
    {F F' : A i} {G G' : A j} (φ : (D.left a).obj F ⟶ G)
    (ψ : (D.left a).obj F' ⟶ G') (r : F ⟶ F') (s : G ⟶ G')
    (h : (D.left a).map r ≫ ψ = φ ≫ s) (n : ℕ) :
    U.extTransfer D a φ n ≫ AddCommGrpCat.ofHom ((Ext.mk₀ s).postcomp (U.obj j) (add_zero n)) =
      AddCommGrpCat.ofHom ((Ext.mk₀ r).postcomp (U.obj i) (add_zero n)) ≫
        U.extTransfer D a ψ n := by
  ext x
  exact DFunLike.congr_fun
    (Functor.extCoefficientTransfer_naturality (D.left a) (inv (U.leftMap D a))
      φ ψ r s h n) x

/-- Transfer through the original triangle, including its coefficient map. -/
theorem System.extTransfer_triangle {i j t : J}
    [HasExt.{e} (A i)] [HasExt.{e} (A j)] [HasExt.{e} (A t)]
    (a : i ⟶ j) (p : i ⟶ t) (q : j ⟶ t) (h : a ≫ q = p)
    {F : A i} {G : A j} {H : A t}
    (φ : (D.left a).obj F ⟶ G) (ψ : (D.left q).obj G ⟶ H) (n : ℕ) :
    U.extTransfer D a φ n ≫ U.extTransfer D q ψ n =
      U.extTransfer D p (D.triangleCoefficientMap a p q h φ ≫ ψ) n := by
  ext x
  exact DFunLike.congr_fun
    (Functor.extCoefficientTransfer_comp_of_eq (D.left a) (D.left q) (D.left p)
      (D.triangleIso p a q h) (inv (U.leftMap D a)) (inv (U.leftMap D q))
      (inv (U.leftMap D p)) (System.leftMap_inv_triangle D U a p q h)
      φ ψ (D.triangleCoefficientMap a p q h φ ≫ ψ)
      (by
        dsimp only [AdjunctionData.triangleCoefficientMap]
        exact (Category.assoc _ _ _).symm) n) x

/-- The existing represented diagram uses the same complete transfer map. -/
theorem representedCohomologyMap_eq_extTransfer [∀ j, HasExt.{e} (A j)]
    (F : System D) (n : ℕ)
    {i j : J} (a : i ⟶ j) :
    representedCohomologyMap D U F n a = U.extTransfer D a (F.leftMap D a) n := rfl

section Cocone

variable [∀ i : I, HasExt.{e} (A (X.obj i))]

local instance reindexLeftAdditive :
    ∀ {i j : I} (a : i ⟶ j), ((D.reindex X).left a).Additive := by
  intro i j a
  change (D.left (X.map a)).Additive
  infer_instance

local instance reindexLeftLimits :
    ∀ {i j : I} (a : i ⟶ j), PreservesFiniteLimits ((D.reindex X).left a) := by
  intro i j a
  change PreservesFiniteLimits (D.left (X.map a))
  infer_instance

local instance reindexLeftColimits :
    ∀ {i j : I} (a : i ⟶ j), PreservesFiniteColimits ((D.reindex X).left a) := by
  intro i j a
  change PreservesFiniteColimits (D.left (X.map a))
  infer_instance

local instance reindexSourceCartesian :
    ∀ {i j : I} (a : i ⟶ j), IsIso ((U.reindex D X).leftMap (D.reindex X) a) := by
  intro i j a
  change IsIso (U.leftMap D (X.map a))
  infer_instance

/-- Reindexing preserves the literal whole represented transition. -/
theorem representedCohomologyMap_reindex_eq_extTransfer
    (F : System (D.reindex X)) (n : ℕ) {i j : I} (a : i ⟶ j) :
    representedCohomologyMap (D.reindex X) (U.reindex D X) F n a =
      U.extTransfer D (X.map a) (F.leftMap (D.reindex X) a) n := rfl

variable (c : Cocone X) [HasExt.{e} (A c.pt)]
  (F : System (D.reindex X)) (K : I ⥤ A c.pt)
  (hobj : ∀ i, K.obj i = (D.left (c.ι.app i)).obj (F.obj i))
  (hmap : ∀ {i j : I} (a : i ⟶ j), K.map a =
    eqToHom (hobj i) ≫
      D.triangleCoefficientMap (X.map a) (c.ι.app i) (c.ι.app j) (c.w a)
        (F.leftMap (D.reindex X) a) ≫ eqToHom (hobj j).symm)
  [HasColimit K] (n : ℕ)

include hobj in
/-- The actual coefficient-colimit injection after the original apex transfer. -/
def System.cohomologyLeg (i : I) :
    representedCohomologyObj (D.reindex X) (U.reindex D X) F n i ⟶
      AddCommGrpCat.of (Ext.{e} (U.obj c.pt) (colimit K) n) :=
  U.extTransfer D (show X.obj i ⟶ c.pt from c.ι.app i)
    (eqToHom (hobj i).symm ≫ colimit.ι K i) n

include hmap in
/-- Triangle composition and the original coefficient colimit prove full naturality. -/
theorem System.cohomologyLeg_naturality {i j : I} (a : i ⟶ j) :
    representedCohomologyMap (D.reindex X) (U.reindex D X) F n a ≫
        U.cohomologyLeg D X c F K hobj n j = U.cohomologyLeg D X c F K hobj n i := by
  rw [representedCohomologyMap_reindex_eq_extTransfer]
  let p : X.obj i ⟶ c.pt := c.ι.app i
  let q : X.obj j ⟶ c.pt := c.ι.app j
  have ht := U.extTransfer_triangle D (X.map a) p q (c.w a)
    (F.leftMap (D.reindex X) a) (eqToHom (hobj j).symm ≫ colimit.ι K j) n
  have hw := colimit.w K a
  rw [hmap a] at hw
  have he := congrArg (fun f => eqToHom (hobj i).symm ≫ f) hw
  have hc : D.triangleCoefficientMap (X.map a) (c.ι.app i) (c.ι.app j) (c.w a)
      (F.leftMap (D.reindex X) a) ≫ (eqToHom (hobj j).symm ≫ colimit.ι K j) =
        eqToHom (hobj i).symm ≫ colimit.ι K i := by
    simpa only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp] using he
  exact ht.trans (congrArg (fun f => U.extTransfer D p f n) hc)

variable
  (leg : ∀ i, representedCohomologyObj (D.reindex X) (U.reindex D X) F n i ⟶
    AddCommGrpCat.of (Ext.{e} (U.obj c.pt) (colimit K) n))
  (hleg : ∀ i, leg i = U.cohomologyLeg D X c F K hobj n i)

include hobj hmap hleg in
/-- The complete cocone stores the original legs, identified with the derived
transfer value. Final cohomology naturality is proved, not supplied. -/
def System.cohomologyCocone :
    Cocone (representedCohomologyFunctor (D.reindex X) (U.reindex D X) F n) where
  pt := AddCommGrpCat.of (Ext.{e} (U.obj c.pt) (colimit K) n)
  ι :=
    { app := leg
      naturality i j a := by
        change representedCohomologyMap (D.reindex X) (U.reindex D X) F n a ≫
          leg j = leg i ≫ 𝟙 _
        simp only [hleg]
        exact (U.cohomologyLeg_naturality D X c F K hobj hmap n a).trans
          (Category.comp_id _).symm }

variable [HasColimit (representedCohomologyFunctor (D.reindex X) (U.reindex D X) F n)]

include hobj hmap hleg in
/-- The literal colimit map induced by those same original legs and actual apex. -/
def System.cohomologyComparison :
    colimit (representedCohomologyFunctor (D.reindex X) (U.reindex D X) F n) ⟶
      AddCommGrpCat.of (Ext.{e} (U.obj c.pt) (colimit K) n) :=
  colimit.desc _ (U.cohomologyCocone D X c F K hobj hmap n leg hleg)

@[reassoc]
theorem System.ι_cohomologyComparison (i : I) :
    colimit.ι (representedCohomologyFunctor (D.reindex X) (U.reindex D X) F n) i ≫
      U.cohomologyComparison D X c F K hobj hmap n leg hleg = leg i :=
  colimit.ι_desc _ i

end Cocone
end Transfers

end CategoryTheory.InjectiveSystem
