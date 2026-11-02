/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.GlobalFinitePureDescent
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.PurelyInseparablePoints
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.GaloisBaseChange
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.BaseChange.Isomorphism
public import Aglib.CategoryTheory.Galois.FiberCompatibleReflection
public import Aglib.CategoryTheory.Galois.Iso
public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.FinitePureZeroDetection
public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.BoundedClassFiniteConstant
public import Aglib.AlgebraicGeometry.EtaleCohomology.PullbackComposition
public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.TwoFieldEffacement.FiniteSource
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-! # Separable refinement of the original two-field cover and class

The source and coefficient separable subfields are literal intermediate
fields. The cover, its marked point and the common embeddings are transported
together; finite-pure zero reflection retains the original class and map.
No arithmetic normalization finiteness is asserted.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.Scheme.EtaleCohomology.TwoFieldEffacement

universe u

section Fields

variable (k F L E : Type u) [Field k] [Field F] [Field L] [Field E]
  [Algebra k F] [Algebra k L] [Algebra k E] [Algebra L E] [IsScalarTower k L E]
  (a : F →ₐ[k] E)

/-- The original common embedding restricted to the two actual separable parts. -/
def separableSourceMap : separableClosure k F →ₐ[k] separableClosure L E where
  toFun x := ⟨a x, mem_separableClosure_iff.mpr
    (IsSeparable.tower_top L ((map_mem_separableClosure_iff a).mpr x.property))⟩
  map_zero' := Subtype.ext (map_zero a)
  map_one' := Subtype.ext (map_one a)
  map_add' x y := Subtype.ext (map_add a (x : F) (y : F))
  map_mul' x y := Subtype.ext (map_mul a (x : F) (y : F))
  commutes' r := Subtype.ext (a.commutes r)

/-- The source triangle is the original embedding, not a newly chosen field map. -/
theorem separableSourceMap_ambient (x : separableClosure k F) :
    algebraMap (separableClosure L E) E (separableSourceMap k F L E a x) =
      a (algebraMap (separableClosure k F) F x) := rfl

/-- The two original base embeddings agree after restriction. -/
theorem separableSourceMap_spec_square :
    Spec.map (CommRingCat.ofHom (separableSourceMap k F L E a).toRingHom) ≫
        Spec.algebraMap k (separableClosure k F) =
      Spec.algebraMap L (separableClosure L E) ≫ Spec.algebraMap k L := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  exact ((separableSourceMap k F L E a).commutes x).trans
    (IsScalarTower.algebraMap_apply k L (separableClosure L E) x)

/-- The ambient field square commutes for the original common embedding. -/
theorem separableSourceMap_spec_ambient :
    Spec.algebraMap (separableClosure L E) E ≫
        Spec.map (CommRingCat.ofHom (separableSourceMap k F L E a).toRingHom) =
      Spec.map (CommRingCat.ofHom a.toRingHom) ≫
        Spec.algebraMap (separableClosure k F) F := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1

/-- The original common-field map on schemes, with no independently chosen
embedding after passing to the two separable subfields. -/
def separableCommonProjection {X : Scheme.{u}}
    (p : X ⟶ Spec (.of (separableClosure k F))) :
    pullback (pullback.snd p
      (Spec.map (CommRingCat.ofHom (separableSourceMap k F L E a).toRingHom)))
        (Spec.algebraMap (separableClosure L E) E) ⟶
      pullback p (Spec.algebraMap (separableClosure k F) F) :=
  pullback.lift
    (pullback.fst _ _ ≫ pullback.fst _ _)
    (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom a.toRingHom)) (by
      rw [Category.assoc, pullback.condition, ← Category.assoc,
        pullback.condition, Category.assoc, separableSourceMap_spec_ambient,
        ← Category.assoc])

@[reassoc] theorem separableCommonProjection_fst {X : Scheme.{u}}
    (p : X ⟶ Spec (.of (separableClosure k F))) :
    separableCommonProjection k F L E a p ≫
        pullback.fst p (Spec.algebraMap (separableClosure k F) F) =
      pullback.fst _ _ ≫ pullback.fst _ _ := pullback.lift_fst _ _ _

@[reassoc] theorem separableCommonProjection_snd {X : Scheme.{u}}
    (p : X ⟶ Spec (.of (separableClosure k F))) :
    separableCommonProjection k F L E a p ≫
        pullback.snd p (Spec.algebraMap (separableClosure k F) F) =
      pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom a.toRingHom) :=
  pullback.lift_snd _ _ _

end Fields

section SourceModel

variable (k F : Type u) [Field k] [Field F] [Algebra k F]
  {U : Scheme.{u}} (p : U ⟶ Spec (.of k))

/-- The literal field tower equality used in the original source model. -/
theorem separableSourceTower_spec :
    Spec.algebraMap (separableClosure k F) F ≫
        Spec.algebraMap k (separableClosure k F) = Spec.algebraMap k F := by
  rw [← Spec.map_comp]
  congr 1

/-- The actual original U_F, not a replacement source, is the second
pullback of U_{k0}. This canonical isomorphism retains both projections. -/
def separableSourceTowerIso :
    pullback (pullback.snd p (Spec.algebraMap k (separableClosure k F)))
        (Spec.algebraMap (separableClosure k F) F) ≅
      pullback p (Spec.algebraMap k F) :=
  pullbackLeftPullbackSndIso p (Spec.algebraMap k (separableClosure k F))
      (Spec.algebraMap (separableClosure k F) F) ≪≫
    pullback.congrHom rfl (separableSourceTower_spec k F)

@[reassoc] theorem separableSourceTowerIso_hom_original :
    (separableSourceTowerIso k F p).hom ≫ pullback.fst p (Spec.algebraMap k F) =
      pullback.fst _ _ ≫ pullback.fst p (Spec.algebraMap k (separableClosure k F)) := by
  simp only [separableSourceTowerIso, Iso.trans_hom, Category.assoc,
    pullback.congrHom_hom, pullback.map, pullback.lift_fst, Category.comp_id,
    pullbackLeftPullbackSndIso_hom_fst]

@[reassoc] theorem separableSourceTowerIso_hom_field :
    (separableSourceTowerIso k F p).hom ≫ pullback.snd p (Spec.algebraMap k F) =
      pullback.snd _ _ := by
  simp only [separableSourceTowerIso, Iso.trans_hom, Category.assoc,
    pullback.congrHom_hom, pullback.map, pullback.lift_snd, Category.comp_id,
    pullbackLeftPullbackSndIso_hom_snd]

/-- The original finite field source projects to its actual separable stage. -/
def separableSourceProjection : pullback p (Spec.algebraMap k F) ⟶
    pullback p (Spec.algebraMap k (separableClosure k F)) :=
  (separableSourceTowerIso k F p).inv ≫ pullback.fst _ _

@[reassoc] theorem separableSourceProjection_original :
    separableSourceProjection k F p ≫
        pullback.fst p (Spec.algebraMap k (separableClosure k F)) =
      pullback.fst p (Spec.algebraMap k F) := by
  dsimp only [separableSourceProjection]
  rw [Category.assoc, ← separableSourceTowerIso_hom_original, Iso.inv_hom_id_assoc]

@[reassoc] theorem separableSourceProjection_field :
    separableSourceProjection k F p ≫
        pullback.snd p (Spec.algebraMap k (separableClosure k F)) =
      pullback.snd p (Spec.algebraMap k F) ≫ Spec.algebraMap (separableClosure k F) F := by
  dsimp only [separableSourceProjection]
  rw [Category.assoc, pullback.condition, ← Category.assoc]
  have h := congrArg (fun z => (separableSourceTowerIso k F p).inv ≫ z)
    (separableSourceTowerIso_hom_field k F p)
  simpa only [Iso.inv_hom_id_assoc] using congrArg
    (fun z => z ≫ Spec.algebraMap (separableClosure k F) F) h.symm

/-- The original source point after the literal separable base change. -/
def separableSourcePoint (x : Spec (.of k) ⟶ U) (hx : x ≫ p = 𝟙 _) :
    Spec (.of (separableClosure k F)) ⟶
      pullback p (Spec.algebraMap k (separableClosure k F)) :=
  pullback.lift (Spec.algebraMap k (separableClosure k F) ≫ x) (𝟙 _) (by
    rw [Category.assoc, hx, Category.comp_id, Category.id_comp])

/-- The original two projections determine the full mark after the separable
source projection. This value law is shared by canonical and cartesian sources. -/
theorem separableSourceProjection_point
    (x : Spec (.of k) ⟶ U) (hx : x ≫ p = 𝟙 _)
    (z : Spec (.of F) ⟶ pullback p (Spec.algebraMap k F))
    (hz₁ : z ≫ pullback.fst p (Spec.algebraMap k F) = Spec.algebraMap k F ≫ x)
    (hz₂ : z ≫ pullback.snd p (Spec.algebraMap k F) = 𝟙 _) :
    z ≫ separableSourceProjection k F p =
      Spec.algebraMap (separableClosure k F) F ≫ separableSourcePoint k F p x hx := by
  apply pullback.hom_ext
  · rw [Category.assoc, separableSourceProjection_original, hz₁, Category.assoc]
    change Spec.algebraMap k F ≫ x = Spec.algebraMap (separableClosure k F) F ≫
      (pullback.lift _ _ _ ≫ pullback.fst p (Spec.algebraMap k (separableClosure k F)))
    rw [pullback.lift_fst, ← Category.assoc, separableSourceTower_spec]
  · rw [Category.assoc, separableSourceProjection_field, ← Category.assoc,
      hz₂, Category.id_comp, Category.assoc]
    change Spec.algebraMap (separableClosure k F) F =
      Spec.algebraMap (separableClosure k F) F ≫ (pullback.lift _ _ _ ≫ _)
    rw [pullback.lift_snd, Category.comp_id]

end SourceModel

section Cover

/-- Descend one original cover through the supplied actual base-change
equivalence. The only point descent is across the given finite-pure fields. -/
private theorem exists_pointed_galois_cover_of_baseChange_equivalence
    (k F : Type u) [Field k] [Field F] [Algebra k F] [IsPurelyInseparable k F]
    {X X' : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] [ConnectedSpace X]
    [CompactSpace X'] [QuasiSeparatedSpace X'] [ConnectedSpace X']
    (b : X' ⟶ X) [Surjective b] [(FiniteEtale.baseChange b).IsEquivalence]
    (x : Spec (.of k) ⟶ X) (Y : FiniteEtale X') [IsGalois Y]
    (z : Spec (.of F) ⟶ Y.obj.left)
    (hz : z ≫ Y.obj.hom ≫ b = Spec.algebraMap k F ≫ x) :
    ∃ (Z : FiniteEtale X) (e : (FiniteEtale.baseChange b).obj Z ≅ Y),
      IsGalois Z ∧ Nat.card (Aut Z) = Nat.card (Aut Y) ∧
      ∃ (z₀ : Spec (.of k) ⟶ Z.obj.left), z₀ ≫ Z.obj.hom = x ∧
        Spec.algebraMap k F ≫ z₀ = z ≫ e.inv.hom.left ≫ pullback.fst Z.obj.hom b := by
  classical
  let Q := (FiniteEtale.baseChange b).asEquivalence
  let Z := Q.inverse.obj Y
  let e : (FiniteEtale.baseChange b).obj Z ≅ Y := Q.counitIso.app Y
  let : ConnectedSpace Y.obj.left :=
    FiniteEtale.Connectedness.connectedSpace_of_categoricalConnected Y
  let eX : ((FiniteEtale.baseChange b).obj Z).obj.left ≅ Y.obj.left :=
    (FiniteEtale.forgetToScheme X').mapIso e
  let : ConnectedSpace ((FiniteEtale.baseChange b).obj Z).obj.left :=
    eX.inv.surjective.connectedSpace eX.inv.continuous
  let : ConnectedSpace (pullback Z.obj.hom b : Scheme.{u}) :=
    inferInstanceAs (ConnectedSpace ((FiniteEtale.baseChange b).obj Z).obj.left)
  let : ConnectedSpace Z.obj.left :=
    (pullback.fst Z.obj.hom b).surjective.connectedSpace (pullback.fst Z.obj.hom b).continuous
  let s := FiniteEtale.algebraicClosureResiduePoint X'
    (Classical.choice (inferInstance : Nonempty X'))
  let : IsGalois ((FiniteEtale.baseChange b).obj Z) :=
    isGalois_of_iso (FiniteEtale.fiberToFinite s) e.symm
  let : IsConnected Z := FiniteEtale.Connectedness.categoricalConnected_of_connectedSpace Z
  let : IsGalois Z := isGalois_of_fiberCompatible_of_fullyFaithful
    (FiniteEtale.fiberToFinite (s ≫ b)) (FiniteEtale.fiberToFinite s)
    (FiniteEtale.baseChange b) (FiniteEtale.fiberToFiniteBaseChangeIso b s) Z
  have hcard : Nat.card (Aut Z) = Nat.card (Aut Y) :=
    (FiniteEtale.baseChange_card_aut_of_connected b Z).symm.trans
      (Nat.card_congr (Aut.autMulEquivOfIso e).toEquiv)
  let r := z ≫ e.inv.hom.left ≫ pullback.fst Z.obj.hom b
  have hr : r ≫ Z.obj.hom = Spec.algebraMap k F ≫ x := by
    have hp : (e.inv.hom.left ≫ pullback.fst Z.obj.hom b) ≫ Z.obj.hom =
        Y.obj.hom ≫ b :=
      (Category.assoc e.inv.hom.left (pullback.fst Z.obj.hom b) Z.obj.hom).trans
        ((congrArg (fun w => e.inv.hom.left ≫ w)
          (pullback.condition (f := Z.obj.hom) (g := b))).trans
          ((Category.assoc e.inv.hom.left (pullback.snd Z.obj.hom b) b).symm.trans
            (congrArg (fun w => w ≫ b) (Over.w e.inv.hom))))
    exact (Category.assoc z (e.inv.hom.left ≫ pullback.fst Z.obj.hom b) Z.obj.hom).trans
      ((congrArg (fun w => z ≫ w) hp).trans hz)
  let zr : FiniteEtale.Fiber (Spec.algebraMap k F ≫ x) Z := Over.homMk r hr
  obtain ⟨z₀, hz₀⟩ := FiniteEtale.PurelyInseparable.extendFiber_surjective k F x Z zr
  refine ⟨Z, e, inferInstance, hcard, z₀.left, Over.w z₀, ?_⟩
  exact congrArg (fun t => t.left) hz₀


variable (k F : Type u) [Field k] [Field F] [Algebra k F]
  [IsPurelyInseparable k F] [Module.Finite k F]
  {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
  (p : X ⟶ Spec (.of k)) [GeometricallyConnected p]

local instance : ConnectedSpace (pullback p (Spec.algebraMap k F) : Scheme.{u}) :=
  GeometricallyConnected.connectedSpace_of_subsingleton (pullback.snd p (Spec.algebraMap k F))

/-- The original finite-pure field pullback is a thin instance of the complete
actual-cover descent. Its original reconstruction and point are unchanged. -/
theorem exists_pointed_galois_cover_of_finitePure
    (x : Spec (.of k) ⟶ X) (hx : x ≫ p = 𝟙 _)
    (Y : FiniteEtale (pullback p (Spec.algebraMap k F))) [IsGalois Y]
    (z : Spec (.of F) ⟶ Y.obj.left)
    (hz₁ : z ≫ Y.obj.hom ≫ pullback.fst p (Spec.algebraMap k F) = Spec.algebraMap k F ≫ x)
    (hz₂ : z ≫ Y.obj.hom ≫ pullback.snd p (Spec.algebraMap k F) = 𝟙 _) :
    letI : ConnectedSpace X := GeometricallyConnected.connectedSpace_of_subsingleton p
    ∃ (Z : FiniteEtale X) (e : (FiniteEtale.baseChange
      (pullback.fst p (Spec.algebraMap k F))).obj Z ≅ Y),
      IsGalois Z ∧ Nat.card (Aut Z) = Nat.card (Aut Y) ∧
      ∃ (z₀ : Spec (.of k) ⟶ Z.obj.left), z₀ ≫ Z.obj.hom = x ∧
        Spec.algebraMap k F ≫ z₀ = z ≫ e.inv.hom.left ≫
          pullback.fst Z.obj.hom (pullback.fst p (Spec.algebraMap k F)) := by
  let : ConnectedSpace X := GeometricallyConnected.connectedSpace_of_subsingleton p
  let : QuasiSeparatedSpace (pullback p (Spec.algebraMap k F) : Scheme.{u}) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.fst p (Spec.algebraMap k F))
  let : (FiniteEtale.baseChange (pullback.fst p (Spec.algebraMap k F))).IsEquivalence :=
    FiniteEtale.PurelyInseparable.Global.finitePureBaseChange_isEquivalence k F p
  let xF := pullback.lift (Spec.algebraMap k F ≫ x) (𝟙 _) (by
    rw [Category.assoc, hx, Category.comp_id, Category.id_comp])
  have hz : z ≫ Y.obj.hom = xF := by
    apply pullback.hom_ext
    · exact (Category.assoc z Y.obj.hom (pullback.fst p (Spec.algebraMap k F))).trans
        (hz₁.trans (pullback.lift_fst _ _ _).symm)
    · exact (Category.assoc z Y.obj.hom (pullback.snd p (Spec.algebraMap k F))).trans
        (hz₂.trans (pullback.lift_snd _ _ _).symm)
  have hmark : z ≫ Y.obj.hom ≫ pullback.fst p (Spec.algebraMap k F) =
      Spec.algebraMap k F ≫ x :=
    (Category.assoc z Y.obj.hom (pullback.fst p (Spec.algebraMap k F))).symm.trans
      ((congrArg (fun w => w ≫ pullback.fst p (Spec.algebraMap k F)) hz).trans
        (pullback.lift_fst _ _ _))
  exact exists_pointed_galois_cover_of_baseChange_equivalence k F
    (pullback.fst p (Spec.algebraMap k F)) x Y z hmark

end Cover

section Zero

attribute [local instance] hasSheafifyLarge HasExt.standard

/-- The complete original coefficient-image and composite-pullback zero
transport is proved before instantiating any field or cover model. -/
private theorem constantRestriction_zero_coefficient_composite
    {S T T₀ : Scheme.{u}} (v : S ⟶ T) (f : T ⟶ T₀)
    (M : AbelianSheaf.{u, u + 1} T₀)
    (A : Type u) [AddCommGroup A] (q : ℕ)
    (c : Sheaf.H.{u + 2} M q)
    (d : Sheaf.H.{u + 2} (ConstantFinite.coefficient A T) q)
    (β : ConstantFinite.coefficient A T ⟶ (inverseImage f).obj M)
    (hd : Sheaf.H.map β q d = cohomologyPullback f M q c)
    (hz : Curves.constantRestriction A v q d = 0) :
    cohomologyPullback (v ≫ f) M q c = 0 := by
  have hd0 : cohomologyPullback v (ConstantFinite.coefficient A T) q d = 0 := by
    apply (cohomologyMapIso_bijective
      ((inverseImageConstantIso v).app (ConstantFinite.value A)) q).injective
    exact (Curves.constantRestriction_apply A v q d).symm.trans
      (hz.trans (map_zero _).symm)
  have hc0 := Fields.cohomologyPullback_eq_zero_of_coefficient_class v β q d
    (cohomologyPullback f M q c) hd hd0
  apply (cohomologyMapIso_bijective ((inverseImageComp f v).app M) q).injective
  exact (cohomologyPullback_comp f v M q c).trans (hc0.trans (map_zero _).symm)

/-- Cover reconstruction and a finite-pure coefficient square reflect the
literal original composite zero. The smaller cover is not assumed to kill
the class: this is deduced from its original reconstructed cover. -/
theorem constantRestriction_zero_of_finitePure_cover_square
    (E₀ E : Type u) [Field E₀] [Field E] [Algebra E₀ E]
    [IsPurelyInseparable E₀ E] [Module.Finite E₀ E]
    {X X' W T : Scheme.{u}} (b : X' ⟶ X)
    (Z : FiniteEtale X) (Y : FiniteEtale X')
    (e : (FiniteEtale.baseChange b).obj Z ≅ Y)
    (p : W ⟶ Spec (.of E₀)) (g₀ : W ⟶ X) (h : W ⟶ T)
    (g : pullback p (Spec.algebraMap E₀ E) ⟶ X')
    (hg : g ≫ b = pullback.fst p (Spec.algebraMap E₀ E) ≫ g₀)
    (A : Type u) [AddCommGroup A] [Finite A] (q : ℕ)
    (c : Sheaf.H.{u + 2} (ConstantFinite.coefficient A T) q)
    (hc : Curves.constantRestriction A
      (((FiniteEtale.baseChange g).obj Y).obj.hom ≫
        pullback.fst p (Spec.algebraMap E₀ E) ≫ h) q c = 0) :
    Curves.constantRestriction A (((FiniteEtale.baseChange g₀).obj Z).obj.hom ≫ h) q c = 0 := by
  let V := (FiniteEtale.baseChange g₀).obj Z
  let v := V.obj.hom
  let a := Spec.algebraMap E₀ E
  let W' := pullback p a
  have hz : Curves.constantRestriction A
      (((FiniteEtale.baseChange (g ≫ b)).obj Z).obj.hom ≫ pullback.fst p a ≫ h) q c = 0 :=
    constantRestriction_zero_of_cover_reconstruction b g (pullback.fst p a ≫ h)
      Z Y e A q c hc
  let d : pullback (v ≫ p) a ⟶ W' :=
    pullback.lift (pullback.fst (v ≫ p) a ≫ v) (pullback.snd (v ≫ p) a)
      ((Category.assoc _ _ _).trans pullback.condition)
  have hd : d ≫ pullback.fst p a = pullback.fst (v ≫ p) a ≫ v := pullback.lift_fst _ _ _
  let t : pullback (v ≫ p) a ⟶ ((FiniteEtale.baseChange (g ≫ b)).obj Z).obj.left :=
    pullback.lift (pullback.fst (v ≫ p) a ≫ pullback.fst Z.obj.hom g₀) d (by
      have HZ : pullback.fst Z.obj.hom g₀ ≫ Z.obj.hom = v ≫ g₀ := pullback.condition
      exact (Category.assoc (pullback.fst (v ≫ p) a) (pullback.fst Z.obj.hom g₀)
        Z.obj.hom).trans
        ((congrArg (fun z => pullback.fst (v ≫ p) a ≫ z) HZ).trans
          ((Category.assoc (pullback.fst (v ≫ p) a) v g₀).symm.trans
            ((congrArg (fun z => z ≫ g₀) hd.symm).trans
              ((Category.assoc d (pullback.fst p a) g₀).trans
                (congrArg (fun z => d ≫ z) hg.symm))))))
  have ht : t ≫ ((FiniteEtale.baseChange (g ≫ b)).obj Z).obj.hom = d :=
    pullback.lift_snd _ _ _
  have H : t ≫ (((FiniteEtale.baseChange (g ≫ b)).obj Z).obj.hom ≫
      pullback.fst p a ≫ h) = pullback.fst (v ≫ p) a ≫ (v ≫ h) := by
    rw [← Category.assoc t, ht, ← Category.assoc d, hd, Category.assoc]
  have hz' : Curves.constantRestriction A (pullback.fst (v ≫ p) a ≫ (v ≫ h)) q c = 0 := by
    rw [← H, Curves.constantRestriction_comp, hz, map_zero]
  exact ConstantFinite.constantRestriction_eq_zero_of_finitePure E₀ E
    (v ≫ p) (v ≫ h) A q c hz'

end Zero

section Refinement

attribute [local instance] hasSheafifyLarge HasExt.standard

variable (k F L E : Type u) [Field k] [Field F] [Field L] [Field E]
  [Algebra k F] [Module.Finite k F] [Algebra k L] [Algebra k E]
  [Algebra L E] [IsScalarTower k L E] [Module.Finite L E]
  (a : F →ₐ[k] E)
  {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
  (p : X ⟶ Spec (.of (separableClosure k F))) [GeometricallyConnected p]

local notation "k₀" => separableClosure k F
local notation "E₀" => separableClosure L E
local notation "b" => Spec.algebraMap k₀ F
local notation "a₀" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (separableSourceMap k F L E a)))

local instance : ConnectedSpace (pullback p b : Scheme.{u}) :=
  GeometricallyConnected.connectedSpace_of_subsingleton (pullback.snd p b)

/-- Simultaneous cover, mark, common-embedding and original class-zero descent
to the actual separable source and coefficient subfields. The common square is
constructed by `separableCommonProjection`, not assumed as a missing input.
The prior finite Galois coefficient stage may be retained as L in this theorem. -/
theorem exists_separable_pointed_cover_and_composite_zero
    (x : Spec (.of k₀) ⟶ X) (hx : x ≫ p = 𝟙 _)
    (Y : FiniteEtale (pullback p b)) [IsGalois Y]
    (z : Spec (.of F) ⟶ Y.obj.left)
    (hz₁ : z ≫ Y.obj.hom ≫ pullback.fst p b = b ≫ x)
    (hz₂ : z ≫ Y.obj.hom ≫ pullback.snd p b = 𝟙 _)
    {T : Scheme.{u}} (h : pullback p a₀ ⟶ T)
    (A : Type u) [AddCommGroup A] [Finite A] (q : ℕ)
    (c : Sheaf.H.{u + 2} (ConstantFinite.coefficient A T) q)
    (hc : Curves.constantRestriction A
      (((FiniteEtale.baseChange (separableCommonProjection k F L E a p)).obj Y).obj.hom ≫
        pullback.fst (pullback.snd p a₀) (Spec.algebraMap E₀ E) ≫ h) q c = 0) :
    letI : ConnectedSpace X := GeometricallyConnected.connectedSpace_of_subsingleton p
    ∃ (Z : FiniteEtale X) (e : (FiniteEtale.baseChange (pullback.fst p b)).obj Z ≅ Y),
      IsGalois Z ∧ Nat.card (Aut Z) = Nat.card (Aut Y) ∧
      ∃ (z₀ : Spec (.of k₀) ⟶ Z.obj.left), z₀ ≫ Z.obj.hom = x ∧
        b ≫ z₀ = z ≫ e.inv.hom.left ≫ pullback.fst Z.obj.hom (pullback.fst p b) ∧
        Curves.constantRestriction A
          (((FiniteEtale.baseChange (pullback.fst p a₀)).obj Z).obj.hom ≫ h) q c = 0 := by
  let : ConnectedSpace X := GeometricallyConnected.connectedSpace_of_subsingleton p
  obtain ⟨Z, e, hG, hcard, z₀, hz₀, hzrec⟩ :=
    exists_pointed_galois_cover_of_finitePure k₀ F p x hx Y z hz₁ hz₂
  refine ⟨Z, e, hG, hcard, z₀, hz₀, hzrec, ?_⟩
  exact constantRestriction_zero_of_finitePure_cover_square E₀ E
    (pullback.fst p b) Z Y e (pullback.snd p a₀) (pullback.fst p a₀) h
    (separableCommonProjection k F L E a p)
    (separableCommonProjection_fst k F L E a p) A q c hc

/-- Consume exactly the coefficient-image equation supplied by the original
finite-Galois constant-class producer. Both the Galois-stage map f and the
subsequent separable common-field map remain in the final literal composite. -/
theorem exists_separable_pointed_cover_killing_coefficient_class
    (x : Spec (.of k₀) ⟶ X) (hx : x ≫ p = 𝟙 _)
    (Y : FiniteEtale (pullback p b)) [IsGalois Y]
    (z : Spec (.of F) ⟶ Y.obj.left)
    (hz₁ : z ≫ Y.obj.hom ≫ pullback.fst p b = b ≫ x)
    (hz₂ : z ≫ Y.obj.hom ≫ pullback.snd p b = 𝟙 _)
    {T T₀ : Scheme.{u}} (h : pullback p a₀ ⟶ T) (f : T ⟶ T₀)
    (M : AbelianSheaf.{u, u + 1} T₀)
    (A : Type u) [AddCommGroup A] [Finite A] (q : ℕ)
    (c : Sheaf.H.{u + 2} M q)
    (d : Sheaf.H.{u + 2} (ConstantFinite.coefficient A T) q)
    (β : ConstantFinite.coefficient A T ⟶ (inverseImage f).obj M)
    (hd : Sheaf.H.map β q d = cohomologyPullback f M q c)
    (hzero : Curves.constantRestriction A
      (((FiniteEtale.baseChange (separableCommonProjection k F L E a p)).obj Y).obj.hom ≫
        pullback.fst (pullback.snd p a₀) (Spec.algebraMap E₀ E) ≫ h) q d = 0) :
    letI : ConnectedSpace X := GeometricallyConnected.connectedSpace_of_subsingleton p
    ∃ (Z : FiniteEtale X) (e : (FiniteEtale.baseChange (pullback.fst p b)).obj Z ≅ Y),
      IsGalois Z ∧ Nat.card (Aut Z) = Nat.card (Aut Y) ∧
      ∃ (z₀ : Spec (.of k₀) ⟶ Z.obj.left), z₀ ≫ Z.obj.hom = x ∧
        b ≫ z₀ = z ≫ e.inv.hom.left ≫ pullback.fst Z.obj.hom (pullback.fst p b) ∧
        cohomologyPullback
          ((((FiniteEtale.baseChange (pullback.fst p a₀)).obj Z).obj.hom ≫ h) ≫ f)
          M q c = 0 := by
  let : ConnectedSpace X := GeometricallyConnected.connectedSpace_of_subsingleton p
  obtain ⟨Z, e, hG, hcard, z₀, hz₀, hzrec, hz⟩ :=
    exists_separable_pointed_cover_and_composite_zero k F L E a p x hx Y z hz₁ hz₂ h A q d hzero
  refine ⟨Z, e, hG, hcard, z₀, hz₀, hzrec, ?_⟩
  exact constantRestriction_zero_coefficient_composite
    (((FiniteEtale.baseChange (pullback.fst p a₀)).obj Z).obj.hom ≫ h) f M A q c d β hd hz

end Refinement

/-- The original iso base-change functor, with its actual inverse-object
witness, is an equivalence; no cover model is replaced in this construction. -/
private theorem baseChange_invIso_isEquivalence {X Y : Scheme.{u}} (i : X ≅ Y) :
    (FiniteEtale.baseChange i.inv).IsEquivalence := by
  let : (FiniteEtale.baseChange i.inv).Full := FiniteEtale.baseChange_full_of_isIso i.inv
  let : (FiniteEtale.baseChange i.inv).Faithful := FiniteEtale.baseChange_faithful_of_isIso i.inv
  let e : FiniteEtale.baseChange i.hom ⋙ FiniteEtale.baseChange i.inv ≅
      𝟭 (FiniteEtale Y) :=
    (FiniteEtale.baseChangeComp i.hom i.inv).symm ≪≫
      eqToIso (congrArg FiniteEtale.baseChange i.inv_hom_id) ≪≫ FiniteEtale.baseChangeId Y
  let : (FiniteEtale.baseChange i.inv).EssSurj :=
    ⟨fun Z => ⟨(FiniteEtale.baseChange i.hom).obj Z, ⟨e.app Z⟩⟩⟩
  exact { }

/-- One shared equivalence for the original separable-source projection. -/
private theorem separableSourceProjection_isEquivalence
    (k F : Type u) [Field k] [Field F] [Algebra k F] [Module.Finite k F]
    {U : Scheme.{u}} (p : U ⟶ Spec (.of k)) :
    (FiniteEtale.baseChange (separableSourceProjection k F p)).IsEquivalence := by
  let p₀ := pullback.snd p (Spec.algebraMap k (separableClosure k F))
  let b := Spec.algebraMap (separableClosure k F) F
  let i := separableSourceTowerIso k F p
  let : (FiniteEtale.baseChange (pullback.fst p₀ b)).IsEquivalence :=
    FiniteEtale.PurelyInseparable.Global.finitePureBaseChange_isEquivalence
      (separableClosure k F) F p₀
  let : (FiniteEtale.baseChange i.inv).IsEquivalence := baseChange_invIso_isEquivalence i
  exact Functor.isEquivalence_of_iso
    (FiniteEtale.baseChangeComp (pullback.fst p₀ b) i.inv).symm

section OriginalSource

attribute [local instance] hasSheafifyLarge HasExt.standard

variable (k F L E : Type u) [Field k] [Field F] [Field L] [Field E]
  [Algebra k F] [Module.Finite k F] [Algebra k L] [Algebra k E]
  [Algebra L E] [IsScalarTower k L E] [Module.Finite L E]
  (a : F →ₐ[k] E)
  {U : Scheme.{u}} [CompactSpace U] [QuasiSeparatedSpace U]
  (p : U ⟶ Spec (.of k)) [GeometricallyConnected p]

local notation "k₀" => separableClosure k F
local notation "E₀" => separableClosure L E
local notation "b₀" => Spec.algebraMap k k₀
local notation "b" => Spec.algebraMap k₀ F
local notation "p₀" => pullback.snd p b₀
local notation "ι" => separableSourceTowerIso k F p
local notation "a₀" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (separableSourceMap k F L E a)))
local notation "g" => separableCommonProjection k F L E a p₀

local instance : ConnectedSpace (pullback p b₀ : Scheme.{u}) :=
  GeometricallyConnected.connectedSpace_of_subsingleton p₀

local instance : ConnectedSpace (pullback p (Spec.algebraMap k F) : Scheme.{u}) :=
  GeometricallyConnected.connectedSpace_of_subsingleton (pullback.snd p (Spec.algebraMap k F))

/-- Descend the original cover on an actual cartesian source, retaining its
full mark and order. The chosen pullback comparison changes maps, not covers. -/
theorem exists_cartesian_source_separable_cover_and_zero
    (x : Spec (.of k) ⟶ U) (hx : x ≫ p = 𝟙 _)
    {V : Scheme.{u}} (aV : V ⟶ U) (qV : V ⟶ Spec (.of F))
    (H : IsPullback aV qV p (Spec.algebraMap k F)) :
    letI : QuasiSeparatedSpace (pullback p (Spec.algebraMap k F) : Scheme.{u}) :=
      quasiSeparatedSpace_of_quasiSeparated (pullback.fst p (Spec.algebraMap k F))
    letI : CompactSpace V := H.isoPullback.inv.homeomorph.compactSpace
    letI : QuasiSeparatedSpace V :=
      (quasiSeparatedSpace_congr H.isoPullback.hom.homeomorph).mpr inferInstance
    letI : ConnectedSpace V :=
      H.isoPullback.hom.homeomorph.connectedSpace_iff.mpr inferInstance
    ∀ (Y : FiniteEtale V) [IsGalois Y]
    (z : Spec (.of F) ⟶ Y.obj.left)
    (_ : z ≫ Y.obj.hom ≫ aV = Spec.algebraMap k F ≫ x)
    (_ : z ≫ Y.obj.hom ≫ qV = 𝟙 _)
    {T : Scheme.{u}} (h : pullback p₀ a₀ ⟶ T)
    (A : Type u) [AddCommGroup A] [Finite A] (q : ℕ)
    (c : Sheaf.H.{u + 2} (ConstantFinite.coefficient A T) q)
    (_ : Curves.constantRestriction A
      (((FiniteEtale.baseChange (g ≫ (ι).hom ≫ H.isoPullback.inv)).obj Y).obj.hom ≫
        pullback.fst (pullback.snd p₀ a₀) (Spec.algebraMap E₀ E) ≫ h) q c = 0),
    ∃ (Z : FiniteEtale (pullback p b₀))
      (e : (FiniteEtale.baseChange
        (H.isoPullback.hom ≫ separableSourceProjection k F p)).obj Z ≅ Y),
      IsGalois Z ∧ Nat.card (Aut Z) = Nat.card (Aut Y) ∧
      ∃ (z₀ : Spec (.of k₀) ⟶ Z.obj.left),
        z₀ ≫ Z.obj.hom = separableSourcePoint k F p x hx ∧
        b ≫ z₀ = z ≫ e.inv.hom.left ≫ pullback.fst Z.obj.hom
          (H.isoPullback.hom ≫ separableSourceProjection k F p) ∧
        Curves.constantRestriction A
          (((FiniteEtale.baseChange (pullback.fst p₀ a₀)).obj Z).obj.hom ≫ h) q c = 0 := by
  let : QuasiSeparatedSpace (pullback p (Spec.algebraMap k F) : Scheme.{u}) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.fst p (Spec.algebraMap k F))
  let : CompactSpace V := H.isoPullback.inv.homeomorph.compactSpace
  let : QuasiSeparatedSpace V :=
    (quasiSeparatedSpace_congr H.isoPullback.hom.homeomorph).mpr inferInstance
  let : ConnectedSpace V :=
    H.isoPullback.hom.homeomorph.connectedSpace_iff.mpr inferInstance
  intro Y hY z hz₁ hz₂ T h A _ _ q c hc
  let i := H.isoPullback
  let v := i.hom ≫ separableSourceProjection k F p
  let x₀ := separableSourcePoint k F p x hx
  let : QuasiSeparatedSpace (pullback p b₀ : Scheme.{u}) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.fst p b₀)
  let : (FiniteEtale.baseChange (separableSourceProjection k F p)).IsEquivalence :=
    separableSourceProjection_isEquivalence k F p
  let : (FiniteEtale.baseChange i.hom).IsEquivalence := baseChange_invIso_isEquivalence i.symm
  let : (FiniteEtale.baseChange v).IsEquivalence :=
    Functor.isEquivalence_of_iso
      (FiniteEtale.baseChangeComp (separableSourceProjection k F p) i.hom).symm
  let : Surjective (separableSourceProjection k F p) :=
    inferInstanceAs (Surjective ((ι).inv ≫ pullback.fst p₀ b))
  let : Surjective v := inferInstanceAs (Surjective (i.hom ≫ separableSourceProjection k F p))
  have hz₁' : (z ≫ Y.obj.hom ≫ i.hom) ≫
      pullback.fst p (Spec.algebraMap k F) = Spec.algebraMap k F ≫ x := by
    have hi₁ : i.hom ≫ pullback.fst p (Spec.algebraMap k F) = aV :=
      H.isoPullback_hom_fst
    calc
      _ = z ≫ Y.obj.hom ≫ (i.hom ≫ pullback.fst p (Spec.algebraMap k F)) := by
        simp only [Category.assoc]
      _ = z ≫ Y.obj.hom ≫ aV := congrArg (fun w => z ≫ Y.obj.hom ≫ w) hi₁
      _ = _ := hz₁
  have hz₂' : (z ≫ Y.obj.hom ≫ i.hom) ≫
      pullback.snd p (Spec.algebraMap k F) = 𝟙 _ := by
    have hi₂ : i.hom ≫ pullback.snd p (Spec.algebraMap k F) = qV :=
      H.isoPullback_hom_snd
    calc
      _ = z ≫ Y.obj.hom ≫ (i.hom ≫ pullback.snd p (Spec.algebraMap k F)) := by
        simp only [Category.assoc]
      _ = z ≫ Y.obj.hom ≫ qV := congrArg (fun w => z ≫ Y.obj.hom ≫ w) hi₂
      _ = _ := hz₂
  have hm : z ≫ Y.obj.hom ≫ v = b ≫ x₀ := by
    simpa only [Category.assoc] using
      separableSourceProjection_point k F p x hx (z ≫ Y.obj.hom ≫ i.hom) hz₁' hz₂'
  obtain ⟨Z, e, hG, hcard, z₀, hz₀, hzrec⟩ :=
    exists_pointed_galois_cover_of_baseChange_equivalence k₀ F v x₀ Y z hm
  have hi : i.inv ≫ v = separableSourceProjection k F p := by
    exact i.inv_hom_id_assoc _
  have ht : (ι).hom ≫ i.inv ≫ v = pullback.fst p₀ b := by
    rw [hi]
    exact (ι).hom_inv_id_assoc _
  have hg : (g ≫ (ι).hom ≫ i.inv) ≫ v =
      pullback.fst (pullback.snd p₀ a₀) (Spec.algebraMap E₀ E) ≫ pullback.fst p₀ a₀ := by
    rw [Category.assoc, Category.assoc, ht]
    exact separableCommonProjection_fst k F L E a p₀
  refine ⟨Z, e, hG, hcard, z₀, hz₀, hzrec, ?_⟩
  exact constantRestriction_zero_of_finitePure_cover_square E₀ E v Z Y e
    (pullback.snd p₀ a₀) (pullback.fst p₀ a₀) h (g ≫ (ι).hom ≫ i.inv) hg A q c hc

/-- The original U_F cover is descended directly. No second cover Y' or
base-change associator is introduced to transport its original zero. -/
theorem exists_original_source_separable_cover_and_zero
    (x : Spec (.of k) ⟶ U) (hx : x ≫ p = 𝟙 _)
    (Y : FiniteEtale (pullback p (Spec.algebraMap k F))) [IsGalois Y]
    (z : Spec (.of F) ⟶ Y.obj.left)
    (hz₁ : z ≫ Y.obj.hom ≫ pullback.fst p (Spec.algebraMap k F) = Spec.algebraMap k F ≫ x)
    (hz₂ : z ≫ Y.obj.hom ≫ pullback.snd p (Spec.algebraMap k F) = 𝟙 _)
    {T : Scheme.{u}} (h : pullback p₀ a₀ ⟶ T)
    (A : Type u) [AddCommGroup A] [Finite A] (q : ℕ)
    (c : Sheaf.H.{u + 2} (ConstantFinite.coefficient A T) q)
    (hc : Curves.constantRestriction A
      (((FiniteEtale.baseChange (g ≫ (ι).hom)).obj Y).obj.hom ≫
        pullback.fst (pullback.snd p₀ a₀) (Spec.algebraMap E₀ E) ≫ h) q c = 0) :
    ∃ (Z : FiniteEtale (pullback p b₀))
      (e : (FiniteEtale.baseChange (separableSourceProjection k F p)).obj Z ≅ Y),
      IsGalois Z ∧ Nat.card (Aut Z) = Nat.card (Aut Y) ∧
      ∃ (z₀ : Spec (.of k₀) ⟶ Z.obj.left),
        z₀ ≫ Z.obj.hom = separableSourcePoint k F p x hx ∧
        b ≫ z₀ = z ≫ e.inv.hom.left ≫ pullback.fst Z.obj.hom
          (separableSourceProjection k F p) ∧
        Curves.constantRestriction A
          (((FiniteEtale.baseChange (pullback.fst p₀ a₀)).obj Z).obj.hom ≫ h) q c = 0 := by
  let v := separableSourceProjection k F p
  let x₀ := separableSourcePoint k F p x hx
  let : QuasiSeparatedSpace (pullback p b₀ : Scheme.{u}) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.fst p b₀)
  let : QuasiSeparatedSpace (pullback p (Spec.algebraMap k F) : Scheme.{u}) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.fst p (Spec.algebraMap k F))
  let : (FiniteEtale.baseChange v).IsEquivalence :=
    separableSourceProjection_isEquivalence k F p
  let : Surjective v := inferInstanceAs (Surjective ((ι).inv ≫ pullback.fst p₀ b))
  have hm : z ≫ Y.obj.hom ≫ v = b ≫ x₀ := by
    simpa only [Category.assoc] using
      separableSourceProjection_point k F p x hx (z ≫ Y.obj.hom)
        ((Category.assoc _ _ _).trans hz₁) ((Category.assoc _ _ _).trans hz₂)
  obtain ⟨Z, e, hG, hcard, z₀, hz₀, hzrec⟩ :=
    exists_pointed_galois_cover_of_baseChange_equivalence k₀ F v x₀ Y z hm
  have ht : (ι).hom ≫ v = pullback.fst p₀ b :=
    (Category.assoc (ι).hom (ι).inv (pullback.fst p₀ b)).symm.trans
      ((congrArg (fun w => w ≫ pullback.fst p₀ b) (ι).hom_inv_id).trans (Category.id_comp _))
  have hg : (g ≫ (ι).hom) ≫ v =
      pullback.fst (pullback.snd p₀ a₀) (Spec.algebraMap E₀ E) ≫ pullback.fst p₀ a₀ :=
    (Category.assoc g (ι).hom v).trans
      ((congrArg (fun w => g ≫ w) ht).trans (separableCommonProjection_fst k F L E a p₀))
  refine ⟨Z, e, hG, hcard, z₀, hz₀, hzrec, ?_⟩
  exact constantRestriction_zero_of_finitePure_cover_square E₀ E v Z Y e
    (pullback.snd p₀ a₀) (pullback.fst p₀ a₀) h (g ≫ (ι).hom) hg A q c hc

end OriginalSource

end AlgebraicGeometry.Scheme.EtaleCohomology.TwoFieldEffacement
