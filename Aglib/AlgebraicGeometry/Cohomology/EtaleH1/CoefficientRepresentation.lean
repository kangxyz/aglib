/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

/- Current interface basis: 46f53465aaf3b0167049e9c8e9e2294111bb4281.
Original construction and mathematical provenance are retained below. -/
public import Aglib.AlgebraicGeometry.Cohomology.EtaleH1.RepresentedTorsor
public import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_

/-!
# Actual finite commutative group schemes representing finite coefficient sheaves

Construction for `K2-018#eq:k2018-pointed-character`, mathematical basis
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`, frozen engineering basis
`7f86e4a1763cc4ec35e9b0a8acd659750355a0de`.

The only representability input is the previously isolated Stacks 03RV
existence direction for finite locally constant set sheaves. Restricting the
actual coefficient presheaf to finite etale covers constructs its commutative
group object through Yoneda; finite-product preservation then yields the real
group scheme. Evaluation on the universal product proves additivity on every
small-etale test object. The resulting isomorphism is an additive sheaf
isomorphism, not just a bijection of sets. No GC+FF hypothesis is used here.

Full faithfulness on coefficients is also proved: small-site Yoneda recovers
an actual scheme morphism, and the zero and addition formulas on the terminal
and universal product test objects prove its group laws. No group structure,
coefficient map, or cohomology comparison is supplied by 03RV.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (forget toEtale)
namespace AlgebraicGeometry.Scheme.EtaleH1
universe u
variable {X : Scheme.{u}}
attribute [local instance] Over.cartesianMonoidalCategory
  Scheme.FiniteEtale.GroupDescent.coverCartesian
attribute [local instance] BraidedCategory.ofCartesianMonoidalCategory
namespace CoefficientRepresentation
variable (L : AbelianSheaf.{u, u + 1} X)

/-- The actual coefficient presheaf restricted to finite etale tests. -/
def coverPresheaf : (Scheme.FiniteEtale X)ᵒᵖ ⥤ CommGrpCat.{u + 1} :=
  (toEtale X).op ⋙ L.obj ⋙ AddCommGrpCat.toCommGrp

variable (Y : Scheme.FiniteEtale X) (e : finiteRepresentedSetSheaf Y ≅ underlyingSetSheaf L)

/-- The underlying representing isomorphism evaluated on any etale test scheme. -/
def sectionEquiv (U : X.Etale) :
    ((Scheme.Etale.forget X).obj U ⟶ Y.obj) ≃ L.obj.obj (op U) where
  toFun f := e.hom.hom.app (op U) (ULift.up f)
  invFun a := (e.inv.hom.app (op U) a).down
  left_inv f := congrArg (fun q : finiteRepresentedSetSheaf Y ⟶ finiteRepresentedSetSheaf Y =>
    (q.hom.app (op U) (ULift.up f)).down) e.hom_inv_id
  right_inv a := congrArg (fun q : underlyingSetSheaf L ⟶ underlyingSetSheaf L =>
    q.hom.app (op U) a) e.inv_hom_id

theorem sectionEquiv_naturality {U V : X.Etale} (f : U ⟶ V)
    (g : (Scheme.Etale.forget X).obj V ⟶ Y.obj) :
    sectionEquiv L Y e U ((Scheme.Etale.forget X).map f ≫ g) =
      L.obj.map f.op (sectionEquiv L Y e V g) :=
  congrFun (congrArg (fun k => k.hom) (e.hom.hom.naturality f.op)) (ULift.up g)

/-- Yoneda representability of the commutative-group-valued cover presheaf. -/
def representable : ((coverPresheaf L) ⋙ CategoryTheory.forget _).RepresentableBy Y where
  homEquiv {U} :=
    { toFun f := Multiplicative.ofAdd (sectionEquiv L Y e ((toEtale X).obj U) f.hom)
      invFun a := ObjectProperty.homMk ((sectionEquiv L Y e ((toEtale X).obj U)).symm a.toAdd)
      left_inv f := by apply ObjectProperty.hom_ext; exact (sectionEquiv L Y e _).left_inv _
      right_inv a := (sectionEquiv L Y e _).right_inv _ }
  homEquiv_comp f g := sectionEquiv_naturality L Y e ((toEtale X).map f) g.hom

/-- The commutative group object on the representing cover, transported from the coefficient
presheaf. -/
abbrev coverGroup : CommGrpObj Y := CommGrpObj.ofRepresentableBy Y (coverPresheaf L)
  (representable L Y e)

instance coverForgetMonoidal : (_root_.AlgebraicGeometry.Scheme.FiniteEtale.forget
  X).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso := fun _ _ => Iso.refl _
      left_unitality := by
        intro Z
        simp only [Iso.refl_hom, id_whiskerRight, Category.id_comp]
        rfl
      right_unitality := by
        intro Z
        simp only [Iso.refl_hom, whiskerLeft_id, Category.id_comp]
        rfl }

/-- The actual finite group scheme obtained by finite-product-compatible inclusion. -/
def groupScheme : Grp (Over X) := by
  letI := coverGroup L Y e
  exact (_root_.AlgebraicGeometry.Scheme.FiniteEtale.forget X).mapGrp.obj { X := Y }

instance group_comm : IsCommMonObj (groupScheme L Y e).X := by
  let := coverGroup L Y e
  constructor
  have h := congrArg (fun f : Y ⊗ Y ⟶ Y => f.hom) (IsCommMonObj.mul_comm (X := Y))
  change (β_ Y.obj Y.obj).hom ≫ (μ[Y]).hom = (μ[Y]).hom
  exact h

theorem sectionEquiv_mul (U : X.Etale)
    (f g : (Scheme.Etale.forget X).obj U ⟶ (groupScheme L Y e).X) :
    sectionEquiv L Y e U (f * g) =
      sectionEquiv L Y e U f + sectionEquiv L Y e U g := by
  let := coverGroup L Y e
  let V : X.Etale := (toEtale X).obj (Y ⊗ Y)
  let q : U ⟶ V := MorphismProperty.Over.homMk (lift f g).left (Over.w (lift f g)) (by trivial)
  have hm : sectionEquiv L Y e V (μ[Y]).hom =
      sectionEquiv L Y e V (fst Y Y).hom + sectionEquiv L Y e V (snd Y Y).hom := by
    exact (sectionEquiv L Y e V).apply_symm_apply _
  change sectionEquiv L Y e U ((Scheme.Etale.forget X).map q ≫ (μ[Y]).hom) = _
  rw [sectionEquiv_naturality, hm, map_add]
  rw [← sectionEquiv_naturality, ← sectionEquiv_naturality]
  congr 1
  · apply congrArg (sectionEquiv L Y e U)
    change lift f g ≫ fst _ _ = f
    exact lift_fst f g
  · apply congrArg (sectionEquiv L Y e U)
    change lift f g ≫ snd _ _ = g
    exact lift_snd f g

/-- The actual additive sheaf isomorphism, including nonfinite etale test schemes. -/
def sheafIso : representedSheaf (groupScheme L Y e) ≅ L :=
  ObjectProperty.isoMk _ (NatIso.ofComponents
    (fun U => AddEquiv.toAddCommGrpIso
      { toEquiv := (Equiv.ulift.trans Additive.toMul).trans (sectionEquiv L Y e U.unop)
        map_add' f g := sectionEquiv_mul L Y e U.unop f.down.toMul g.down.toMul })
    (fun {U V} f => by
      ext a
      exact sectionEquiv_naturality L Y e f.unop a.down.toMul))

instance group_finite : IsFinite (groupScheme L Y e).X.hom := Y.property.1
instance group_etale : Etale (groupScheme L Y e).X.hom := Y.property.2

end CoefficientRepresentation

/-- An actual finite commutative étale group scheme representing the given additive sheaf. -/
structure CoefficientRepresentation (L : AbelianSheaf.{u, u + 1} X) where
  /-- The group object over `X` underlying the coefficient representation. -/
  group : Grp (Over X)
  finite : IsFinite group.X.hom
  etale : Etale group.X.hom
  commutative : IsCommMonObj group.X
  /-- The isomorphism from the sheaf represented by the commutative group object to `L`. -/
  iso : @representedSheaf _ group commutative ≅ L

namespace CoefficientRepresentation

attribute [instance] finite etale commutative

/-- Construct the group-scheme representative using precisely the existing set-sheaf existence
input. -/
def ofFiniteLocallyConstant (L : AbelianSheaf.{u, u + 1} X)
    (h : Stacks03RV X) (hL : IsFiniteLocallyConstant L) : CoefficientRepresentation L := by
  let Y := (trivialTorsor L).finiteEtaleRepresentative h hL
  let e := (trivialTorsor L).finiteEtaleRepresentativeIso h hL
  exact ⟨groupScheme L Y e, inferInstance, inferInstance, inferInstance, sheafIso L Y e⟩

end CoefficientRepresentation

variable {H K : Grp (Over X)} [IsCommMonObj H.X] [IsCommMonObj K.X]
variable [IsFinite H.X.hom] [Etale H.X.hom] [IsFinite K.X.hom] [Etale K.X.hom]

/-- Recover the actual underlying scheme morphism by evaluation at its identity section. -/
def representedSheafPreimage (q : representedSheaf H ⟶ representedSheaf K) : H.X ⟶ K.X :=
  finiteRepresentedSetSheafPreimage
    (Y := _root_.AlgebraicGeometry.Scheme.FiniteEtale.mk H.X.hom)
    (Z := _root_.AlgebraicGeometry.Scheme.FiniteEtale.mk K.X.hom)
    ((underlyingSetFunctor X).map q)

theorem representedSheafPreimage_app (q : representedSheaf H ⟶ representedSheaf K)
    (U : X.Etale) (f : (Scheme.Etale.forget X).obj U ⟶ H.X) :
    ULift.up (Additive.ofMul (f ≫ representedSheafPreimage q)) =
      q.hom.app (op U) (ULift.up (Additive.ofMul f)) :=
  finiteRepresentedSetSheafPreimage_app
    (Y := _root_.AlgebraicGeometry.Scheme.FiniteEtale.mk H.X.hom)
    (Z := _root_.AlgebraicGeometry.Scheme.FiniteEtale.mk K.X.hom)
    ((underlyingSetFunctor X).map q) U f

instance representedSheafPreimage_isMonHom (q : representedSheaf H ⟶ representedSheaf K) :
    IsMonHom (representedSheafPreimage q) where
  one_hom := by
    have h := representedSheafPreimage_app q (etaleTerminal X) (η[H.X])
    have hz : (ULift.up (Additive.ofMul (η[H.X])) :
        RepresentedSections H ((Scheme.Etale.forget X).obj (etaleTerminal X))) = 0 := by
      apply ULift.ext
      change η[H.X] = toUnit (𝟙_ (Over X)) ≫ η[H.X]
      rw [show toUnit (𝟙_ (Over X)) = 𝟙 _ from toUnit_unique _ _]
      exact (Category.id_comp _).symm
    rw [hz, map_zero] at h
    have h' := congrArg (fun a => a.down.toMul) h
    change η[H.X] ≫ representedSheafPreimage q = toUnit (𝟙_ (Over X)) ≫ η[K.X] at h'
    rw [show toUnit (𝟙_ (Over X)) = 𝟙 _ from toUnit_unique _ _, Category.id_comp] at h'
    exact h'
  mul_hom := by
    let HC := _root_.AlgebraicGeometry.Scheme.FiniteEtale.mk H.X.hom
    let U := (toEtale X).obj (HC ⊗ HC)
    let a : RepresentedSections H ((Scheme.Etale.forget X).obj U) := ⟨Additive.ofMul (fst H.X H.X)⟩
    let b : RepresentedSections H ((Scheme.Etale.forget X).obj U) := ⟨Additive.ofMul (snd H.X H.X)⟩
    have h := (q.hom.app (op U)).hom.map_add a b
    change q.hom.app (op U) (ULift.up (Additive.ofMul ((fst H.X H.X) * (snd H.X H.X)))) =
      q.hom.app (op U) a + q.hom.app (op U) b at h
    rw [← representedSheafPreimage_app q U, ← representedSheafPreimage_app q U,
      ← representedSheafPreimage_app q U] at h
    have h' := congrArg (fun a => a.down.toMul) h
    change (lift (fst H.X H.X) (snd H.X H.X) ≫ μ[H.X]) ≫ representedSheafPreimage q =
      lift (fst H.X H.X ≫ representedSheafPreimage q)
        (snd H.X H.X ≫ representedSheafPreimage q) ≫ μ[K.X] at h'
    simpa only [lift_fst_snd, Category.id_comp, lift_fst_comp_snd_comp] using h'

/-- The recovered actual coefficient group-scheme morphism. -/
def representedSheafGroupPreimage (q : representedSheaf H ⟶ representedSheaf K) : H ⟶ K :=
  Grp.homMk (representedSheafPreimage q)

theorem representedSheafMap_preimage (q : representedSheaf H ⟶ representedSheaf K) :
    representedSheafMap (representedSheafGroupPreimage q) = q := by
  ext U a
  exact representedSheafPreimage_app q U.unop a.down.toMul

theorem representedSheafPreimage_map (q : H ⟶ K) :
    representedSheafGroupPreimage (representedSheafMap q) = q := by
  apply Grp.hom_ext
  exact finiteRepresentedSetSheafPreimage_map
    (Y := _root_.AlgebraicGeometry.Scheme.FiniteEtale.mk H.X.hom)
    (Z := _root_.AlgebraicGeometry.Scheme.FiniteEtale.mk K.X.hom) q.hom.hom

/-- Full faithfulness on actual finite commutative étale group schemes. -/
def representedSheafHomEquiv (H K : Grp (Over X))
    [IsCommMonObj H.X] [IsCommMonObj K.X]
    [IsFinite H.X.hom] [Etale H.X.hom] [IsFinite K.X.hom] [Etale K.X.hom] :
    (H ⟶ K) ≃ (representedSheaf H ⟶ representedSheaf K) where
  toFun := representedSheafMap
  invFun := representedSheafGroupPreimage
  left_inv := representedSheafPreimage_map
  right_inv := representedSheafMap_preimage

end AlgebraicGeometry.Scheme.EtaleH1

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 7d9cbc4facae0986d39c1fbca2a00cbc5f5e7eb82456cd16f6f25f5a21ab812f.
Definitions, hypotheses and universes are retained modulo native names. -/
