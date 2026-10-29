/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

/- Current interface basis: 46f53465aaf3b0167049e9c8e9e2294111bb4281.
Original construction and mathematical provenance are retained below. -/
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.RepresentedTorsor
public import Aglib.CategoryTheory.Monoidal.Cartesian.RepresentedGroupReflection
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
namespace AlgebraicGeometry.Scheme.EtaleCohomology
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
  let : (_root_.AlgebraicGeometry.Scheme.FiniteEtale.forget X).Monoidal :=
    coverForgetMonoidal (X := X)
  let β : (toEtale X) ⋙ Scheme.Etale.forget X ≅
      _root_.AlgebraicGeometry.Scheme.FiniteEtale.forget X :=
    NatIso.ofComponents (fun _ => Iso.refl _) (by
      intro Z W a
      simpa only [Iso.refl_hom, Category.comp_id, Category.id_comp] using
        (show ((toEtale X) ⋙ Scheme.Etale.forget X).map a =
          (_root_.AlgebraicGeometry.Scheme.FiniteEtale.forget X).map a from rfl))
  exact (CommutativeGroupSections.sectionEquiv_mul_of_original_representation.{u + 1}
    (T := Scheme.Etale.forget X) (I := toEtale X)
    (J := _root_.AlgebraicGeometry.Scheme.FiniteEtale.forget X) (β := β)
    (hT := Functor.FullyFaithful.ofFullyFaithful (Scheme.Etale.forget X))
    (A := L.obj) (Y := Y) (α := representable L Y e)
    (ξ := fun U => sectionEquiv L Y e U)
    (hξ := by
      intro U V a b
      exact sectionEquiv_naturality L Y e a b)
    (hα := by
      intro Z a
      change sectionEquiv L Y e ((toEtale X).obj Z) a.hom =
        sectionEquiv L Y e ((toEtale X).obj Z) (𝟙 _ ≫ a.hom)
      rw [Category.id_comp])) U f g

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
    IsMonHom (representedSheafPreimage q) := by
  let T := Scheme.Etale.forget X
  let Q (U : X.Etale) : AddCommGrpCat.of (RepresentedSections H (T.obj U)) ⟶
      AddCommGrpCat.of (RepresentedSections K (T.obj U)) := q.hom.app (op U)
  let HC := _root_.AlgebraicGeometry.Scheme.FiniteEtale.mk H.X.hom
  let U₂ := (toEtale X).obj (HC ⊗ HC)
  let κ₀ : T.obj (etaleTerminal X) ≅ 𝟙_ (Over X) := Iso.refl _
  let : (_root_.AlgebraicGeometry.Scheme.FiniteEtale.forget X).Monoidal :=
    CoefficientRepresentation.coverForgetMonoidal (X := X)
  let κ₂ : T.obj U₂ ≅ H.X ⊗ H.X :=
    (Functor.Monoidal.μIso (_root_.AlgebraicGeometry.Scheme.FiniteEtale.forget X) HC HC).symm
  exact CommutativeGroupSections.isMonHom_of_original_test_sections.{u + 1, u + 1}
    (T := T) (H := H) (K := K) (U₀ := etaleTerminal X) (U₂ := U₂)
    (κ₀ := κ₀) (κ₂ := κ₂) (Q := fun U => (Q U).hom) (r := representedSheafPreimage q)
    (hr := by
      intro U f
      exact representedSheafPreimage_app q U f)

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

end AlgebraicGeometry.Scheme.EtaleCohomology

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 7d9cbc4facae0986d39c1fbca2a00cbc5f5e7eb82456cd16f6f25f5a21ab812f.
Definitions, hypotheses and universes are retained modulo native names. -/
