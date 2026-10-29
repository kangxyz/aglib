/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Topos.AdditiveCoefficientAction
public import Aglib.CategoryTheory.Sites.Torsor.Classification
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # Actual torsor images through native additive coefficient actions

Integer transport is determined by the original constant-integer generator
and the actual adjunctions. The image extension retains its literal right-end
projection and contravariant integer inverse in Ext.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits Opposite

namespace CategoryTheory.Sheaf

universe u v w
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {A : Sheaf J AddCommGrpCat.{w}}

/-- The original integer presheaf map determined by a genuine global point. -/
def constantIntegerLiftPresheaf (s : Topos.GlobalPoint (underlyingSetSheaf A)) :
    (Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{w} ℤ)) ⟶ A.obj where
  app U := AddCommGrpCat.ofHom
    (uliftZMultiplesHom (A.obj.obj U)
      (show A.obj.obj U from s.hom.app U PUnit.unit))
  naturality {U V} f := by
    ext n
    change n.down • (show A.obj.obj V from s.hom.app V PUnit.unit) =
      (A.obj.map f).hom (n.down • (show A.obj.obj U from s.hom.app U PUnit.unit))
    rw [map_zsmul]
    have h := ConcreteCategory.congr_hom (s.hom.naturality f) PUnit.unit
    change (show A.obj.obj V from s.hom.app V PUnit.unit) =
      (A.obj.map f).hom (show A.obj.obj U from s.hom.app U PUnit.unit) at h
    exact congrArg (fun t : A.obj.obj V => n.down • t) h

/-- The generating integer one has exactly the prescribed component value. -/
theorem constantIntegerLiftPresheaf_one
    (s : Topos.GlobalPoint (underlyingSetSheaf A)) (U : Cᵒᵖ) :
    (constantIntegerLiftPresheaf s).app U (ULift.up 1) = s.hom.app U PUnit.unit := by
  change (1 : ℤ) • (show A.obj.obj U from s.hom.app U PUnit.unit) = _
  exact one_zsmul (show A.obj.obj U from s.hom.app U PUnit.unit)

/-- Maps out of the same constant integer presheaf are determined by one. -/
theorem constantIntegerPresheaf_hom_ext
    {a b : (Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{w} ℤ)) ⟶ A.obj}
    (h : ∀ U, a.app U (ULift.up 1) = b.app U (ULift.up 1)) : a = b := by
  apply NatTrans.ext
  funext U
  apply (AddCommGrpCat.uliftZMultiplesAddEquiv (A.obj.obj U)).injective
  change a.app U (ULift.up 1) = b.app U (ULift.up 1)
  exact h U

variable [HasSheafify J AddCommGrpCat.{w}]

/-- Extend the original integer presheaf map by the selected sheafification adjunction. -/
def constantIntegerLift (s : Topos.GlobalPoint (underlyingSetSheaf A)) :
    constantIntegerSheaf J ⟶ A :=
  ((sheafificationAdjunction J AddCommGrpCat.{w}).homEquiv _ A).symm
    (constantIntegerLiftPresheaf s)

/-- The extension retains the original sheafification-unit values. -/
theorem constantIntegerLift_unit (s : Topos.GlobalPoint (underlyingSetSheaf A)) :
    toSheafify J ((Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{w} ℤ))) ≫
      (constantIntegerLift s).hom = constantIntegerLiftPresheaf s := by
  exact ((sheafificationAdjunction J AddCommGrpCat.{w}).homEquiv _ A).apply_symm_apply _

/-- The actual constant-integer sheaf represents intrinsic underlying global points. -/
def constantIntegerHomGlobalPointEquiv (A : Sheaf J AddCommGrpCat.{w}) :
    (constantIntegerSheaf J ⟶ A) ≃ Topos.GlobalPoint (underlyingSetSheaf A) where
  toFun q := constantIntegerOne J ≫ (Topos.AdditiveCoefficientAction.observation J).map q
  invFun := constantIntegerLift
  left_inv q := by
    let adj := sheafificationAdjunction J AddCommGrpCat.{w}
    apply (adj.homEquiv _ A).injective
    change adj.homEquiv _ _ ((adj.homEquiv _ _).symm
      (constantIntegerLiftPresheaf
        (constantIntegerOne J ≫ (Topos.AdditiveCoefficientAction.observation J).map q))) = _
    rw [Equiv.apply_symm_apply]
    apply constantIntegerPresheaf_hom_ext
    intro U
    rw [constantIntegerLiftPresheaf_one]
    rfl
  right_inv s := by
    ext U x
    have h := congrArg (fun q => q.app U (ULift.up 1)) (constantIntegerLift_unit s)
    have hx : x = PUnit.unit := by
      change (PUnit : Type w) at x
      cases x
      rfl
    exact h.trans ((constantIntegerLiftPresheaf_one s U).trans
      (congrArg (s.hom.app U) hx.symm))

/-- The generator comparison uses exactly the original underlying coefficient map. -/
theorem constantIntegerHomGlobalPointEquiv_naturality
    {B : Sheaf J AddCommGrpCat.{w}} (q : constantIntegerSheaf J ⟶ A) (g : A ⟶ B) :
    constantIntegerHomGlobalPointEquiv B (q ≫ g) =
      constantIntegerHomGlobalPointEquiv A q ≫
        (Topos.AdditiveCoefficientAction.observation J).map g := by
  change constantIntegerOne J ≫ (Topos.AdditiveCoefficientAction.observation J).map (q ≫ g) =
    (constantIntegerOne J ≫ (Topos.AdditiveCoefficientAction.observation J).map q) ≫
      (Topos.AdditiveCoefficientAction.observation J).map g
  rw [Functor.map_comp, Category.assoc]

/-- The identity on the selected integer sheaf is its original one global point. -/
theorem constantIntegerHomGlobalPointEquiv_id :
    constantIntegerHomGlobalPointEquiv (constantIntegerSheaf J) (𝟙 _) =
      constantIntegerOne J := by
  change constantIntegerOne J ≫ (Topos.AdditiveCoefficientAction.observation J).map (𝟙 _) = _
  rw [Functor.map_id, Category.comp_id]

end CategoryTheory.Sheaf

namespace CategoryTheory.Topos.AdditiveCoefficientAction

universe uC vC uD vD w
variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {f : Topos.GeometricMorphism (Sheaf K (Type w)) (Sheaf J (Type w))}
  {a : LeftExactAdjunction (Sheaf J AddCommGrpCat.{w}) (Sheaf K AddCommGrpCat.{w})}
  (s : Topos.AdditiveCoefficientAction f a)

/-- Transposition through the original units identifies the underlying left comparison. -/
theorem leftComparison_homEquiv {A : Sheaf J AddCommGrpCat.{w}}
    {B : Sheaf K AddCommGrpCat.{w}} (q : a.left.obj.obj A ⟶ B) :
    f.adj.homEquiv _ _ (s.leftComparison.app A ≫ (observation K).map q) =
      (observation J).map (a.adj.homEquiv _ _ q) ≫ s.abSetComparison.hom.app B := by
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
  rw [← leftComparison_unit_assoc s A]
  have h := s.abSetComparison.hom.naturality q
  change (observation J).map (a.right.map q) ≫ s.abSetComparison.hom.app B =
    s.abSetComparison.hom.app (a.left.obj.obj A) ≫ f.right.map ((observation K).map q) at h
  rw [← h]

variable [HasSheafify J AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}]

/-- The original adjunctions and integer generators compare the two represented Hom functors. -/
def integerHomEquiv (B : Sheaf K AddCommGrpCat.{w}) :
    (a.left.obj.obj (Sheaf.constantIntegerSheaf J) ⟶ B) ≃
      (Sheaf.constantIntegerSheaf K ⟶ B) :=
  (a.adj.homEquiv _ B).trans
    ((Sheaf.constantIntegerHomGlobalPointEquiv (a.right.obj B)).trans
      ((Iso.homCongr (Iso.refl (Topos.terminalSheaf J)) (s.abSetComparison.app B)).trans
        ((Topos.SheafMorphism.directImageGlobalPointEquiv f ((observation K).obj B)).trans
          (Sheaf.constantIntegerHomGlobalPointEquiv B).symm)))

/-- The represented-Hom comparison is exactly its original global-point composite. -/
theorem integerHomEquiv_point {B : Sheaf K AddCommGrpCat.{w}}
    (q : a.left.obj.obj (Sheaf.constantIntegerSheaf J) ⟶ B) :
    Sheaf.constantIntegerHomGlobalPointEquiv B (s.integerHomEquiv B q) =
      Topos.SheafMorphism.directImageGlobalPointEquiv f ((observation K).obj B)
        (Sheaf.constantIntegerHomGlobalPointEquiv (a.right.obj B) (a.adj.homEquiv _ _ q) ≫
          s.abSetComparison.hom.app B) := by
  simp only [integerHomEquiv, Equiv.trans_apply, Equiv.apply_symm_apply,
    Iso.homCongr_apply, Iso.refl_inv, Category.id_comp]
  rfl

/-- The same comparison preserves postcomposition by every actual coefficient morphism. -/
theorem integerHomEquiv_naturality {B B' : Sheaf K AddCommGrpCat.{w}}
    (q : a.left.obj.obj (Sheaf.constantIntegerSheaf J) ⟶ B) (g : B ⟶ B') :
    s.integerHomEquiv B' (q ≫ g) = s.integerHomEquiv B q ≫ g := by
  apply (Sheaf.constantIntegerHomGlobalPointEquiv B').injective
  rw [Sheaf.constantIntegerHomGlobalPointEquiv_naturality]
  simp only [integerHomEquiv_point]
  rw [Adjunction.homEquiv_naturality_right,
    Sheaf.constantIntegerHomGlobalPointEquiv_naturality]
  let p := Sheaf.constantIntegerHomGlobalPointEquiv (a.right.obj B)
    (a.adj.homEquiv _ _ q)
  have hd := s.abSetComparison.hom.naturality g
  change (observation J).map (a.right.map g) ≫ s.abSetComparison.hom.app B' =
    s.abSetComparison.hom.app B ≫ f.right.map ((observation K).map g) at hd
  have hp :
      (p ≫ (observation J).map (a.right.map g)) ≫ s.abSetComparison.hom.app B' =
        (p ≫ s.abSetComparison.hom.app B) ≫ f.right.map ((observation K).map g) := by
    rw [Category.assoc, hd, Category.assoc]
  exact (congrArg
    (Topos.SheafMorphism.directImageGlobalPointEquiv f ((observation K).obj B')) hp).trans
      (f.terminalHomEquiv_naturality (Topos.terminalSheafIsTerminal J)
        (Topos.terminalSheafIsTerminal K) (p ≫ s.abSetComparison.hom.app B)
        ((observation K).map g))

/-- The actual integer image Iso is uniquely fixed by the original global generator. -/
def integerIso :
    a.left.obj.obj (Sheaf.constantIntegerSheaf J) ≅ Sheaf.constantIntegerSheaf K := by
  let toMap : a.left.obj.obj (Sheaf.constantIntegerSheaf J) ⟶ Sheaf.constantIntegerSheaf K :=
    (s.integerHomEquiv (Sheaf.constantIntegerSheaf K)).symm (𝟙 _)
  let fromMap : Sheaf.constantIntegerSheaf K ⟶ a.left.obj.obj (Sheaf.constantIntegerSheaf J) :=
    s.integerHomEquiv (a.left.obj.obj (Sheaf.constantIntegerSheaf J)) (𝟙 _)
  refine ⟨toMap, fromMap, ?_, ?_⟩
  · apply (s.integerHomEquiv (a.left.obj.obj (Sheaf.constantIntegerSheaf J))).injective
    rw [integerHomEquiv_naturality]
    change s.integerHomEquiv (Sheaf.constantIntegerSheaf K)
      ((s.integerHomEquiv (Sheaf.constantIntegerSheaf K)).symm (𝟙 _)) ≫ fromMap = fromMap
    rw [Equiv.apply_symm_apply, Category.id_comp]
  · have h := integerHomEquiv_naturality s
      (𝟙 (a.left.obj.obj (Sheaf.constantIntegerSheaf J))) toMap
    change s.integerHomEquiv (Sheaf.constantIntegerSheaf K) (𝟙 _ ≫ toMap) = fromMap ≫ toMap at h
    rw [Category.id_comp] at h
    exact h.symm.trans ((s.integerHomEquiv (Sheaf.constantIntegerSheaf K)).apply_symm_apply _)

/-- The Iso's hom has precisely the identity target-generator image. -/
theorem integerHomEquiv_integerIso_hom :
    s.integerHomEquiv (Sheaf.constantIntegerSheaf K) s.integerIso.hom = 𝟙 _ :=
  (s.integerHomEquiv (Sheaf.constantIntegerSheaf K)).apply_symm_apply _

/-- The original adjoint transpose of this fixed integer transport. -/
def integerAdjunctionMap :
    Sheaf.constantIntegerSheaf J ⟶ a.right.obj (Sheaf.constantIntegerSheaf K) :=
  a.adj.homEquiv _ _ s.integerIso.hom

/-- The adjoint integer map sends the actual one generator through the native point comparison. -/
theorem integerAdjunctionMap_one :
    (Sheaf.constantIntegerOne J ≫ (observation J).map s.integerAdjunctionMap) ≫
        s.abSetComparison.hom.app (Sheaf.constantIntegerSheaf K) =
      (Topos.SheafMorphism.directImageGlobalPointEquiv f
        ((observation K).obj (Sheaf.constantIntegerSheaf K))).symm
          (Sheaf.constantIntegerOne K) := by
  apply (Topos.SheafMorphism.directImageGlobalPointEquiv f
    ((observation K).obj (Sheaf.constantIntegerSheaf K))).injective
  have h := integerHomEquiv_point s s.integerIso.hom
  rw [integerHomEquiv_integerIso_hom, Sheaf.constantIntegerHomGlobalPointEquiv_id] at h
  exact h.symm.trans
    ((Topos.SheafMorphism.directImageGlobalPointEquiv f
      ((observation K).obj (Sheaf.constantIntegerSheaf K))).apply_symm_apply _).symm

/-- Left-exact Set image carries the actual integer-one arrow to the same target one. -/
theorem integerOne_image :
    f.left.obj.map (Sheaf.constantIntegerOne J) ≫
        s.leftComparison.app (Sheaf.constantIntegerSheaf J) ≫
          (observation K).map s.integerIso.hom =
      (Topos.terminalSheafIsTerminal K).from (f.left.obj.obj (Topos.terminalSheaf J)) ≫
        Sheaf.constantIntegerOne K := by
  apply (f.adj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, leftComparison_homEquiv]
  change Sheaf.constantIntegerOne J ≫ (observation J).map s.integerAdjunctionMap ≫
      s.abSetComparison.hom.app (Sheaf.constantIntegerSheaf K) = _
  rw [← Category.assoc]
  refine (integerAdjunctionMap_one s).trans ?_
  change (f.terminalHomEquiv (Topos.terminalSheafIsTerminal J)
      (Topos.terminalSheafIsTerminal K)
      ((observation K).obj (Sheaf.constantIntegerSheaf K))).symm
        (Sheaf.constantIntegerOne K) = _
  rw [LeftExactAdjunction.terminalHomEquiv_symm_apply, Adjunction.homEquiv_unit]
  exact congrArg
    (fun q : f.left.obj.obj (Topos.terminalSheaf J) ⟶ Topos.terminalSheaf K =>
      f.adj.unit.app (Topos.terminalSheaf J) ≫ f.right.map (q ≫ Sheaf.constantIntegerOne K))
    ((Topos.terminalSheafIsTerminal K).hom_ext _ _)

end CategoryTheory.Topos.AdditiveCoefficientAction

namespace CategoryTheory.Sheaf

universe uC vC uD vD w eJ eK
variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [HasSheafify J AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}]
  {f : Topos.GeometricMorphism (Sheaf K (Type w)) (Sheaf J (Type w))}
  {a : LeftExactAdjunction (Sheaf J AddCommGrpCat.{w}) (Sheaf K AddCommGrpCat.{w})}
  (s : Topos.AdditiveCoefficientAction f a)
  {L : Sheaf J AddCommGrpCat.{w}} (P : Torsor L)

local instance : a.left.obj.IsLeftAdjoint := a.adj.isLeftAdjoint
local instance : a.left.obj.Additive := Functor.additive_of_preserves_binary_products _

/-- The image projection is the original image of the projection followed by integer transport. -/
def torsorInverseImageProjection :
    a.left.obj.obj (torsorExtension P).X₂ ⟶ constantIntegerSheaf K :=
  a.left.obj.map (torsorExtension P).g ≫ s.integerIso.hom

/-- The actual image maps preserve the original augmentation relation. -/
theorem torsorInverseImage_zero :
    a.left.obj.map (torsorExtension P).f ≫ torsorInverseImageProjection s P = 0 := by
  let i : L ⟶ (torsorExtension P).X₂ := (torsorExtension P).f
  let p : (torsorExtension P).X₂ ⟶ constantIntegerSheaf J := (torsorExtension P).g
  have hz : i ≫ p = 0 := (torsorExtension P).zero
  change a.left.obj.map i ≫ a.left.obj.map p ≫ s.integerIso.hom = 0
  calc
    _ = a.left.obj.map (i ≫ p) ≫ s.integerIso.hom :=
      (Functor.map_comp_assoc a.left.obj i p s.integerIso.hom).symm
    _ = a.left.obj.map (0 : L ⟶ constantIntegerSheaf J) ≫ s.integerIso.hom :=
      congrArg (fun q : L ⟶ constantIntegerSheaf J =>
        a.left.obj.map q ≫ s.integerIso.hom) hz
    _ = 0 := by rw [Functor.map_zero, zero_comp]

/-- The exact image extension with the fixed native integer transport. -/
def torsorInverseImageExtension : ShortComplex (Sheaf K AddCommGrpCat.{w}) :=
  ShortComplex.mk (a.left.obj.map (torsorExtension P).f)
    (torsorInverseImageProjection s P) (torsorInverseImage_zero s P)

/-- The same right-endpoint transport gives the actual short-complex Iso. -/
def torsorInverseImageExtensionIso :
    (torsorExtension P).map a.left.obj ≅ torsorInverseImageExtension s P :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) s.integerIso
    (by simp [torsorInverseImageExtension])
    (by simp [torsorInverseImageExtension, torsorInverseImageProjection])

variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The actual coefficient inverse image preserves short exactness. -/
theorem torsorInverseImageExtension_shortExact :
    (torsorInverseImageExtension s P).ShortExact :=
  ShortComplex.shortExact_of_iso (torsorInverseImageExtensionIso s P)
    ((torsorExtension_shortExact P).map_of_exact a.left.obj)

section ExtClass
variable [HasExt.{eJ} (Sheaf J AddCommGrpCat.{w})]
  [HasExt.{eK} (Sheaf K AddCommGrpCat.{w})]

/-- The original intrinsic H1 image map, retaining the inverse integer transport. -/
def torsorH1InverseImageMap (L : Sheaf J AddCommGrpCat.{w}) :
    H L 1 →+ H (a.left.obj.obj L) 1 :=
  ((Abelian.Ext.mk₀ s.integerIso.inv).precomp _ (zero_add 1)).comp
    (a.left.obj.mapExtAddHom (constantIntegerSheaf J) L 1)

/-- The image extension has exactly that native contravariant Ext class. -/
theorem torsorInverseImageExtension_extClass :
    (torsorInverseImageExtension_shortExact s P).extClass =
      torsorH1InverseImageMap s L (torsorExtClass P) := by
  have h := ShortComplex.ShortExact.extClass_naturality
    (torsorInverseImageExtension_shortExact s P)
    ((torsorExtension_shortExact P).map_of_exact a.left.obj)
    (torsorInverseImageExtensionIso s P).inv
  change (torsorInverseImageExtension_shortExact s P).extClass.comp
      (Abelian.Ext.mk₀ (𝟙 _)) (add_zero 1) =
    (Abelian.Ext.mk₀ s.integerIso.inv).comp
      ((torsorExtension_shortExact P).map_of_exact a.left.obj).extClass (zero_add 1) at h
  rw [Abelian.Ext.comp_mk₀_id, ← Abelian.Ext.mapExactFunctor_extClass] at h
  exact h

end ExtClass

variable [K.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The original explicit one-fibre of the actual image extension. -/
def torsorInverseImageFiber : Torsor (a.left.obj.obj L) :=
  extensionFiberTorsor (torsorInverseImageExtension s P) (constantIntegerOne K)
    (torsorInverseImageExtension_shortExact s P)

section ExtClass
variable [HasExt.{eJ} (Sheaf J AddCommGrpCat.{w})]
  [HasExt.{eK} (Sheaf K AddCommGrpCat.{w})]

/-- The constructed extension fibre has the actual native H1 image class. -/
theorem torsorExtClass_inverseImageFiber :
    torsorExtClass (torsorInverseImageFiber s P) =
      torsorH1InverseImageMap s L (torsorExtClass P) := by
  rw [torsorInverseImageFiber]
  exact (torsorExtClass_extensionFiber _ _ _
    (torsorInverseImageExtension_shortExact s P)).trans (torsorInverseImageExtension_extClass s P)

end ExtClass
end CategoryTheory.Sheaf


namespace CategoryTheory.Sheaf.Torsor

universe u v w
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {L : Sheaf J AddCommGrpCat.{w}} (P : Torsor L) {T : Sheaf J (Type w)}

/-- Transport the original action along an actual carrier Iso. -/
def transportCarrier (e : T ≅ P.carrier) : Torsor L where
  carrier := T
  action U a t := e.inv.hom.app U (P.action U a (e.hom.hom.app U t))
  zero_action U t := by
    have hz : P.action U (0 : L.obj.obj U) (e.hom.hom.app U t) =
        e.hom.hom.app U t := P.zero_action U (e.hom.hom.app U t)
    have he : e.inv.hom.app U (e.hom.hom.app U t) = t :=
      congrArg (fun r => r.hom.app U t) e.hom_inv_id
    exact (congrArg (fun s : P.carrier.obj.obj U => e.inv.hom.app U s) hz).trans he
  add_action U a b t := by
    have h : e.hom.hom.app U (e.inv.hom.app U (P.action U b (e.hom.hom.app U t))) =
        P.action U b (e.hom.hom.app U t) :=
      congrArg (fun r => r.hom.app U (P.action U b (e.hom.hom.app U t))) e.inv_hom_id
    have ha : P.action U (a + b) (e.hom.hom.app U t) =
        P.action U a (P.action U b (e.hom.hom.app U t)) :=
      P.add_action U a b (e.hom.hom.app U t)
    exact congrArg (fun s : P.carrier.obj.obj U => e.inv.hom.app U s)
      (ha.trans (congrArg (P.action U a) h.symm))
  naturality {U V} g a t := by
    have he := ConcreteCategory.congr_hom (e.inv.hom.naturality g)
      (P.action U a (e.hom.hom.app U t))
    have hh := ConcreteCategory.congr_hom (e.hom.hom.naturality g) t
    exact he.symm.trans (congrArg (e.inv.hom.app V)
      ((P.naturality g a _).trans (congrArg (P.action V (L.obj.map g a)) hh.symm)))
  unique_transport U s t := by
    obtain ⟨a, ha, hu⟩ := P.unique_transport U (e.hom.hom.app U s) (e.hom.hom.app U t)
    refine ⟨a, ?_, ?_⟩
    · exact (congrArg (e.inv.hom.app U) ha).trans
        (congrArg (fun r => r.hom.app U t) e.hom_inv_id)
    · intro b hb
      apply hu b
      exact (congrArg (fun r => r.hom.app U (P.action U b (e.hom.hom.app U s)))
        e.inv_hom_id).symm.trans (congrArg (e.hom.hom.app U) hb)
  locally_nonempty U := by
    refine J.superset_covering ?_ (P.locally_nonempty U)
    intro V g ht
    exact ht.map (e.inv.hom.app (op V))

/-- Carrier transport is the original equivariant Iso. -/
def transportCarrierIso (e : T ≅ P.carrier) : Iso (P.transportCarrier e) P where
  carrierIso := e
  equivariant U a t := congrArg (fun r => r.hom.app U
    (P.action U a (e.hom.hom.app U t))) e.inv_hom_id

end CategoryTheory.Sheaf.Torsor

namespace CategoryTheory.Sheaf

universe uC vC uD vD w eJ eK
variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [HasSheafify J AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}]
  {f : Topos.GeometricMorphism (Sheaf K (Type w)) (Sheaf J (Type w))}
  {a : LeftExactAdjunction (Sheaf J AddCommGrpCat.{w}) (Sheaf K AddCommGrpCat.{w})}
  (s : Topos.AdditiveCoefficientAction f a)

open Topos.AdditiveCoefficientAction

/-- The actual coefficient comparison, when its native mate is invertible. -/
def setInverseImageAbelianIso [IsIso s.leftComparison] (A : Sheaf J AddCommGrpCat.{w}) :
    f.left.obj.obj (underlyingSetSheaf A) ≅ underlyingSetSheaf (a.left.obj.obj A) :=
  asIso (s.leftComparison.app A)

/-- The same underlying comparison followed by canonical integer transport. -/
def setInverseImageIntegerIso [IsIso s.leftComparison] :
    f.left.obj.obj (underlyingSetSheaf (constantIntegerSheaf J)) ≅
      underlyingSetSheaf (constantIntegerSheaf K) :=
  setInverseImageAbelianIso s (constantIntegerSheaf J) ≪≫
    (observation K).mapIso s.integerIso

variable {L : Sheaf J AddCommGrpCat.{w}} (P : Torsor L)

/-- The projection of the actual image of the original fibre carrier. -/
def inverseImageFiberSetInclusion :
    f.left.obj.obj (extensionFiberSheaf (torsorExtension P) (constantIntegerOne J)) ⟶
      underlyingSetSheaf (a.left.obj.obj (torsorExtension P).X₂) :=
  f.left.obj.map (extensionFiberInclusion (torsorExtension P) (constantIntegerOne J)) ≫
    s.leftComparison.app (torsorExtension P).X₂

/-- The image of the literal fibre square is the transported extension's fibre square. -/
theorem inverseImageFiberSetIsPullback [IsIso s.leftComparison] :
    IsPullback (inverseImageFiberSetInclusion s P)
      ((Topos.terminalSheafIsTerminal K).from
        (f.left.obj.obj (extensionFiberSheaf (torsorExtension P) (constantIntegerOne J))))
      ((observation K).map (torsorInverseImageExtension s P).g) (constantIntegerOne K) := by
  have h := f.left.obj.map_isPullback
    (IsPullback.of_isLimit (extensionFiberPullbackIsLimit
      (torsorExtension P) (constantIntegerOne J)))
  apply h.of_iso (Iso.refl _) (setInverseImageAbelianIso s (torsorExtension P).X₂)
    (f.terminalIso (Topos.terminalSheafIsTerminal J) (Topos.terminalSheafIsTerminal K))
    (setInverseImageIntegerIso s)
  · exact (Category.id_comp _).symm
  · exact (Topos.terminalSheafIsTerminal K).hom_ext _ _
  · let p : (torsorExtension P).X₂ ⟶ constantIntegerSheaf J := (torsorExtension P).g
    change f.left.obj.map ((observation J).map p) ≫
        s.leftComparison.app (constantIntegerSheaf J) ≫ (observation K).map s.integerIso.hom =
      s.leftComparison.app (torsorExtension P).X₂ ≫
        (observation K).map (a.left.obj.map p ≫ s.integerIso.hom)
    rw [Functor.map_comp, ← Category.assoc, ← Category.assoc]
    exact congrArg (fun q => q ≫ (observation K).map s.integerIso.hom)
      (s.leftComparison.naturality p)
  · exact (s.integerOne_image).trans
      (congrArg (fun q => q ≫ constantIntegerOne K)
        ((Topos.terminalSheafIsTerminal K).hom_ext _ _))

variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}] [IsIso s.leftComparison]

/-- The universal property identifies the two actual fibre carriers. -/
def inverseImageExtensionFiberIso :
    f.left.obj.obj (extensionFiberSheaf (torsorExtension P) (constantIntegerOne J)) ≅
      (torsorInverseImageFiber s P).carrier :=
  (inverseImageFiberSetIsPullback s P).isoIsPullback _ _
    (IsPullback.of_isLimit (extensionFiberPullbackIsLimit
      (torsorInverseImageExtension s P) (constantIntegerOne K)))

/-- The comparison preserves the literal subtype projection. -/
theorem inverseImageExtensionFiberIso_hom_inclusion :
    (inverseImageExtensionFiberIso s P).hom ≫
      extensionFiberInclusion (torsorInverseImageExtension s P) (constantIntegerOne K) =
        inverseImageFiberSetInclusion s P :=
  IsPullback.isoIsPullback_hom_fst _ _ _ _

/-- The original carrier's actual inverse image is the canonical extension fibre. -/
def torsorSetInverseImageIso :
    f.left.obj.obj P.carrier ≅ (torsorInverseImageFiber s P).carrier :=
  f.left.obj.mapIso (torsorCanonicalExtensionIso P).carrierIso ≪≫
    inverseImageExtensionFiberIso s P

omit [HasSheafify K AddCommGrpCat.{w}] [K.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [IsIso s.leftComparison] in
/-- The original canonical inclusion into the same extension middle sheaf. -/
def torsorCanonicalSetInclusion : P.carrier ⟶ underlyingSetSheaf (torsorExtension P).X₂ :=
  (torsorCanonicalExtensionIso P).carrierIso.hom ≫
    extensionFiberInclusion (torsorExtension P) (constantIntegerOne J)

omit [HasSheafify K AddCommGrpCat.{w}] [K.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [IsIso s.leftComparison] in
/-- The canonical inclusion retains the original positive coefficient action. -/
theorem torsorCanonicalSetInclusion_action (U : Cᵒᵖ) (b : L.obj.obj U)
    (t : P.carrier.obj.obj U) :
    (torsorCanonicalSetInclusion P).hom.app U (P.action U b t) =
      (torsorExtension P).f.hom.app U b +
        (show (torsorExtension P).X₂.obj.obj U from
          (torsorCanonicalSetInclusion P).hom.app U t) :=
  congrArg Subtype.val ((torsorCanonicalExtensionIso P).equivariant U b t)

/-- The comparison's middle projection is the image of the original generator map. -/
theorem torsorSetInverseImageIso_hom_inclusion :
    (torsorSetInverseImageIso s P).hom ≫
      extensionFiberInclusion (torsorInverseImageExtension s P) (constantIntegerOne K) =
        f.left.obj.map (torsorCanonicalSetInclusion P) ≫
          s.leftComparison.app (torsorExtension P).X₂ := by
  let T : Sheaf J (Type w) :=
    extensionFiberSheaf (torsorExtension P) (constantIntegerOne J)
  let T' : Sheaf K (Type w) :=
    extensionFiberSheaf (torsorInverseImageExtension s P) (constantIntegerOne K)
  let e : P.carrier ⟶ T := (torsorCanonicalExtensionIso P).carrierIso.hom
  let h : f.left.obj.obj T ⟶ T' := (inverseImageExtensionFiberIso s P).hom
  let j : T' ⟶ underlyingSetSheaf (a.left.obj.obj (torsorExtension P).X₂) :=
    extensionFiberInclusion (torsorInverseImageExtension s P) (constantIntegerOne K)
  let k : T ⟶ underlyingSetSheaf (torsorExtension P).X₂ :=
    extensionFiberInclusion (torsorExtension P) (constantIntegerOne J)
  let c : f.left.obj.obj (underlyingSetSheaf (torsorExtension P).X₂) ⟶
      underlyingSetSheaf (a.left.obj.obj (torsorExtension P).X₂) :=
    s.leftComparison.app (torsorExtension P).X₂
  have hh : h ≫ j = f.left.obj.map k ≫ c := inverseImageExtensionFiberIso_hom_inclusion s P
  change (f.left.obj.map e ≫ h) ≫ j = f.left.obj.map (e ≫ k) ≫ c
  rw [Category.assoc, hh]
  exact (Functor.map_comp_assoc _ e k c).symm

/-- The same native units and coefficient comparison give the literal inclusion square. -/
theorem torsorSetInverseImageIso_unit_inclusion :
    f.adj.unit.app P.carrier ≫ f.right.map ((torsorSetInverseImageIso s P).hom ≫
      extensionFiberInclusion (torsorInverseImageExtension s P) (constantIntegerOne K)) =
        torsorCanonicalSetInclusion P ≫
          (observation J).map (a.adj.unit.app (torsorExtension P).X₂) ≫
            s.abSetComparison.hom.app (a.left.obj.obj (torsorExtension P).X₂) := by
  let k : P.carrier ⟶ underlyingSetSheaf (torsorExtension P).X₂ :=
    torsorCanonicalSetInclusion P
  let c : f.left.obj.obj (underlyingSetSheaf (torsorExtension P).X₂) ⟶
      underlyingSetSheaf (a.left.obj.obj (torsorExtension P).X₂) :=
    s.leftComparison.app (torsorExtension P).X₂
  let q : f.left.obj.obj P.carrier ⟶
      underlyingSetSheaf (a.left.obj.obj (torsorExtension P).X₂) :=
    (torsorSetInverseImageIso s P).hom ≫
      extensionFiberInclusion (torsorInverseImageExtension s P) (constantIntegerOne K)
  have hq : q = f.left.obj.map k ≫ c := torsorSetInverseImageIso_hom_inclusion s P
  change f.adj.unit.app P.carrier ≫ f.right.map q =
    k ≫ (observation J).map (a.adj.unit.app (torsorExtension P).X₂) ≫
      s.abSetComparison.hom.app (a.left.obj.obj (torsorExtension P).X₂)
  rw [hq, Functor.map_comp, ← Category.assoc]
  have hn := f.adj.unit.naturality k
  change _ = f.adj.unit.app P.carrier ≫ f.right.map (f.left.obj.map k) at hn
  rw [← hn, Category.assoc]
  exact congrArg (fun q => k ≫ q) (s.leftComparison_unit (torsorExtension P).X₂).symm

/-- Actual torsor inverse image: its carrier is definitionally the original Set inverse image. -/
def torsorInverseImage : Torsor (a.left.obj.obj L) :=
  (torsorInverseImageFiber s P).transportCarrier (torsorSetInverseImageIso s P)

/-- The original transported action gives an actual equivariant fibre Iso. -/
def torsorInverseImageFiberIso :
    Torsor.Iso (torsorInverseImage s P) (torsorInverseImageFiber s P) :=
  (torsorInverseImageFiber s P).transportCarrierIso (torsorSetInverseImageIso s P)

/-- The inclusion has the literal positive image-kernel action on the same carrier. -/
theorem torsorInverseImage_inclusion_action (U : Dᵒᵖ)
    (b : (a.left.obj.obj L).obj.obj U) (t : (torsorInverseImage s P).carrier.obj.obj U) :
    ((torsorSetInverseImageIso s P).hom.hom.app U
        ((torsorInverseImage s P).action U b t)).val =
      (a.left.obj.map (torsorExtension P).f).hom.app U b +
        (show (a.left.obj.obj (torsorExtension P).X₂).obj.obj U from
          ((torsorSetInverseImageIso s P).hom.hom.app U t).val) :=
  congrArg Subtype.val ((torsorInverseImageFiberIso s P).equivariant U b t)

section ExtClass
variable [HasExt.{eJ} (Sheaf J AddCommGrpCat.{w})]
  [HasExt.{eK} (Sheaf K AddCommGrpCat.{w})]

/-- The actual Set image torsor has exactly the original contravariant H1 image class. -/
theorem torsorExtClass_inverseImage :
    torsorExtClass (torsorInverseImage s P) =
      torsorH1InverseImageMap s L (torsorExtClass P) := by
  rw [torsorExtClass_iso (torsorInverseImageFiberIso s P), torsorExtClass_inverseImageFiber]

end ExtClass
end CategoryTheory.Sheaf


namespace CategoryTheory.Topos.AdditiveCoefficientAction

universe uC vC uD vD w
variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  (F : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [F.IsContinuous J K]
  [(F.sheafPushforwardContinuous (Type w) J K).IsRightAdjoint]
  [PreservesFiniteLimits (F.sheafPullback (Type w) J K)]

/-- In the native site presentation, global-point transport has the original component value. -/
theorem directImageGlobalPointEquiv_symm_app {B : Sheaf K (Type w)}
    (z : Topos.GlobalPoint B) (U : Cᵒᵖ) :
    ((Topos.SheafMorphism.directImageGlobalPointEquiv
      (Topos.SheafMorphism.ofSiteFunctor F J K) B).symm z).hom.app U PUnit.unit =
        z.hom.app (F.op.obj U) PUnit.unit := by
  rw [Topos.SheafMorphism.directImageGlobalPointEquiv,
    LeftExactAdjunction.terminalHomEquiv_symm_apply]
  change z.hom.app (F.op.obj U) _ = z.hom.app (F.op.obj U) PUnit.unit
  have hp (t : (PUnit : Type w)) : t = PUnit.unit := Subsingleton.elim _ _
  exact congrArg (z.hom.app (F.op.obj U)) (hp _)

variable [(F.sheafPushforwardContinuous AddCommGrpCat.{w} J K).IsRightAdjoint]
  [PreservesFiniteLimits (F.sheafPullback AddCommGrpCat.{w} J K)]
  [HasSheafify J AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}]

/-- The actual native integer transpose sends one to one on every original test object. -/
theorem ofSiteFunctor_integerAdjunctionMap_one (U : Cᵒᵖ) :
    ((ofSiteFunctor F J K).integerAdjunctionMap).hom.app U
        ((Sheaf.constantIntegerOne J).hom.app U PUnit.unit) =
      (Sheaf.constantIntegerOne K).hom.app (F.op.obj U) PUnit.unit := by
  have h := congrArg (fun q => q.hom.app U PUnit.unit)
    (integerAdjunctionMap_one (ofSiteFunctor F J K))
  exact h.trans (directImageGlobalPointEquiv_symm_app F J K (Sheaf.constantIntegerOne K) U)

end CategoryTheory.Topos.AdditiveCoefficientAction

namespace CategoryTheory.Sheaf

universe uC vC uD vD w
variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  (F : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [F.IsContinuous J K]
  [(F.sheafPushforwardContinuous (Type w) J K).IsRightAdjoint]
  [PreservesFiniteLimits (F.sheafPullback (Type w) J K)]
  [(F.sheafPushforwardContinuous AddCommGrpCat.{w} J K).IsRightAdjoint]
  [PreservesFiniteLimits (F.sheafPullback AddCommGrpCat.{w} J K)]
  [HasSheafify J AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [IsIso (Topos.AdditiveCoefficientAction.ofSiteFunctor F J K).leftComparison]
  {L : Sheaf J AddCommGrpCat.{w}} (P : Torsor L)


/-- The actual native image unit retains the original coefficient action and positive sign. -/
theorem torsorInverseImage_unit_equivariant (U : Cᵒᵖ)
    (b : L.obj.obj U) (t : P.carrier.obj.obj U) :
    ((F.sheafAdjunctionContinuous (Type w) J K).unit.app P.carrier).hom.app U (P.action U b t) =
      (torsorInverseImage (Topos.AdditiveCoefficientAction.ofSiteFunctor F J K) P).action
        (F.op.obj U)
        (((F.sheafAdjunctionContinuous AddCommGrpCat.{w} J K).unit.app L).hom.app U b)
        (((F.sheafAdjunctionContinuous (Type w) J K).unit.app P.carrier).hom.app U t) := by
  let V := F.op.obj U
  let e := torsorSetInverseImageIso (Topos.AdditiveCoefficientAction.ofSiteFunctor F J K) P
  let b' : ((F.sheafPullback AddCommGrpCat.{w} J K).obj L).obj.obj V :=
    ((F.sheafAdjunctionContinuous AddCommGrpCat.{w} J K).unit.app L).hom.app U b
  let t' : (torsorInverseImage (Topos.AdditiveCoefficientAction.ofSiteFunctor F J K)
    P).carrier.obj.obj V :=
    (show ((F.sheafPullback (Type w) J K).obj P.carrier).obj.obj V from
      ((F.sheafAdjunctionContinuous (Type w) J K).unit.app P.carrier).hom.app U t)
  let s' : (torsorInverseImage (Topos.AdditiveCoefficientAction.ofSiteFunctor F J K)
    P).carrier.obj.obj V :=
    (show ((F.sheafPullback (Type w) J K).obj P.carrier).obj.obj V from
      ((F.sheafAdjunctionContinuous (Type w) J K).unit.app P.carrier).hom.app U (P.action U b t))
  have heq : e.hom.hom.app V ((torsorInverseImage (Topos.AdditiveCoefficientAction.ofSiteFunctor F
    J K) P).action V b' t') =
      (torsorInverseImageFiber (Topos.AdditiveCoefficientAction.ofSiteFunctor F J K) P).action V
        b' (e.hom.hom.app V t') :=
    (torsorInverseImageFiberIso (Topos.AdditiveCoefficientAction.ofSiteFunctor F J K)
      P).equivariant V b' t'
  change s' = (torsorInverseImage (Topos.AdditiveCoefficientAction.ofSiteFunctor F J K) P).action
    V b' t'
  apply (ConcreteCategory.bijective_of_isIso (e.hom.hom.app V)).injective
  refine (show e.hom.hom.app V s' =
    (torsorInverseImageFiber (Topos.AdditiveCoefficientAction.ofSiteFunctor F J K) P).action V b'
      (e.hom.hom.app V t') from ?_).trans
      heq.symm
  apply Subtype.ext
  have hu (x : P.carrier.obj.obj U) := congrArg (fun q => q.hom.app U x)
    (torsorSetInverseImageIso_unit_inclusion (Topos.AdditiveCoefficientAction.ofSiteFunctor F J K)
      P)
  have hn := congrArg (fun q => q.hom.app U b)
    ((F.sheafAdjunctionContinuous AddCommGrpCat.{w} J K).unit.naturality (torsorExtension P).f)
  change ((F.sheafAdjunctionContinuous AddCommGrpCat.{w} J K).unit.app (torsorExtension
    P).X₂).hom.app U
      ((torsorExtension P).f.hom.app U b) =
    ((F.sheafPullback AddCommGrpCat.{w} J K).map (torsorExtension P).f).hom.app V
      (((F.sheafAdjunctionContinuous AddCommGrpCat.{w} J K).unit.app L).hom.app U b) at hn
  change (e.hom.hom.app V
    (((F.sheafAdjunctionContinuous (Type w) J K).unit.app P.carrier).hom.app U (P.action U b
      t))).val =
      ((F.sheafPullback AddCommGrpCat.{w} J K).map (torsorExtension P).f).hom.app V
        (((F.sheafAdjunctionContinuous AddCommGrpCat.{w} J K).unit.app L).hom.app U b) +
      (show ((F.sheafPullback AddCommGrpCat.{w} J K).obj (torsorExtension P).X₂).obj.obj V from
        (e.hom.hom.app V (((F.sheafAdjunctionContinuous (Type w) J K).unit.app P.carrier).hom.app
          U t)).val)
  refine (hu (P.action U b t)).trans ?_
  change ((F.sheafAdjunctionContinuous AddCommGrpCat.{w} J K).unit.app (torsorExtension
    P).X₂).hom.app U
    ((torsorCanonicalSetInclusion P).hom.app U (P.action U b t)) = _
  rw [torsorCanonicalSetInclusion_action, map_add, hn]
  exact congrArg
    (fun v : ((F.sheafPullback AddCommGrpCat.{w} J K).obj (torsorExtension P).X₂).obj.obj V =>
      ((F.sheafPullback AddCommGrpCat.{w} J K).map (torsorExtension P).f).hom.app V
        (((F.sheafAdjunctionContinuous AddCommGrpCat.{w} J K).unit.app L).hom.app U b) + v) (hu
          t).symm

end CategoryTheory.Sheaf
