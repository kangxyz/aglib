/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.EtaleH1.CoefficientStalkBaseChange
public import Aglib.AlgebraicGeometry.Cohomology.Kummer.FieldNaturality
public import Aglib.AlgebraicGeometry.Group.BaseChange.PointTransport
public import Aglib.AlgebraicGeometry.Cohomology.EtaleH1.Kummer.CoefficientBaseChange
public import Aglib.AlgebraicGeometry.Cohomology.EtaleH1.Kummer.GeometricCoefficients

/-!
Native migration from
`R5Lab.Aglib.AlgebraicGeometry.Cohomology.FiniteLocallyConstant.SheafCoherence` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`3248682dc080989857f6c580e3c55e7f4de79dfcbde118ac2341e1a6943216ec`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

open _root_.AlgebraicGeometry.Scheme.EtaleH1
/- Current interface migration: `46f53465aaf3b0167049e9c8e9e2294111bb4281`.
Original mathematical and construction provenance is retained below.
Previous validation is historical; new-interface validation is pending. -/
/-!
# Ordinary finite coefficient sheaf coherence

Manuscript locators: `K2-018#lem:k2018-geometric-exact-order` and
`K2-018#prop:k2018-arithmetic-characters`. Mathematical basis
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`; engineering basis
`7f86e4a1763cc4ec35e9b0a8acd659750355a0de`.

Finite represented sheaf maps are compared on literal geometric stalks.
Actual pointed stalk units prove represented pullback composition and finite
inverse-image associativity. The root-cup field square uses the literal image
root and actual canonical roots base change, with positive native RootCup
orientation. No target H1 or Bockstein equality is retained as a premise.
-/
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj CategoryTheory.PreGaloisCategory TensorProduct
open AlgebraicGeometry.Scheme.EtaleH1
open AlgebraicGeometry.Scheme.Group
open _root_.AlgebraicGeometry.Scheme.FiniteEtale.FieldGalois
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (fiberToFinite)
open _root_.AlgebraicGeometry.Scheme.FiniteEtale.FiberTorsorActions
open _root_.GroupCohomology.ContinuousH1
open AlgebraicGeometry.Scheme.EtaleH1
open AlgebraicGeometry.Scheme.Group.BaseChange.PointTransport
namespace AlgebraicGeometry.Scheme.EtaleH1.SheafCoherence
universe u w w'
attribute [local instance] Over.cartesianMonoidalCategory

section RootPointCoordinates
variable {X S : Scheme.{u}} {C D : Type u} [Field C] [Field D]
variable (n : ℕ)
/-- The native commutative group law on the roots scheme over each test scheme. -/
local instance (Y : Scheme.{u}) : CommGrpObj (MultiplicativeGroup.rootsScheme Y n) :=
  MultiplicativeGroup.rootsCommGroup Y n

/-- Ordinary root-point evaluation commutes with literal extension of the point field. -/
theorem pointRoots_extension (s : Spec (.of C) ⟶ X) (t : Spec (.of D) ⟶ X)
    (φ : C →+* D) (g : Over.mk t ⟶ Over.mk s)
    (hg : g.left = Spec.map (CommRingCat.ofHom φ))
    (a : Over.mk s ⟶ (MultiplicativeGroup.rootsGroupScheme X n).X) :
    GroupCohomology.Kummer.GeometricCoefficients.pointRoots D t n (g ≫ a) =
      restrictRootsOfUnity φ n
          (GroupCohomology.Kummer.GeometricCoefficients.pointRoots C s n a) := by
  apply Subtype.ext
  apply Units.ext
  change (Scheme.ΓSpecIso (.of D)).hom.hom
    ((MultiplicativeGroup.rootsHomEquiv X n _ (g ≫ a)).val.val) =
    φ ((Scheme.ΓSpecIso (.of C)).hom.hom
      ((MultiplicativeGroup.rootsHomEquiv X n _ a).val.val))
  have h := (MultiplicativeGroup.rootsRepresentable X n).homEquiv_comp g a
  have hh := congrArg (fun z : rootsOfUnity n Γ(Spec (.of D), ⊤) =>
    (Scheme.ΓSpecIso (.of D)).hom.hom z.val.val) h
  change _ = (Scheme.ΓSpecIso (.of D)).hom.hom
    (g.left.appTop.hom ((MultiplicativeGroup.rootsHomEquiv X n _ a).val.val)) at hh
  rw [hg] at hh
  exact hh.trans (ConcreteCategory.congr_hom (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)) _)

/-- Canonical roots group pullback preserves the actual root coordinate at every point. -/
theorem pointRoots_pullback (f : S ⟶ X) (s : Spec (.of C) ⟶ S)
    (a : Over.mk s ⟶ (baseChangedGroup f (MultiplicativeGroup.rootsGroupScheme X n)).X) :
    GroupCohomology.Kummer.GeometricCoefficients.pointRoots C s n
      (a ≫ (MultiplicativeBaseChange.rootsBaseChangeIso f n).hom.hom.hom) =
    GroupCohomology.Kummer.GeometricCoefficients.pointRoots C (s ≫ f) n
      ((Scheme.FiniteEtale.GroupBaseChange.pullbackFiberMulEquiv f s
        (MultiplicativeGroup.rootsGroupScheme X n)).symm a) := by
  exact congrArg ((Scheme.ΓSpecIso (.of
      C)).commRingCatIsoToRingEquiv.toMulEquiv.restrictRootsOfUnity n)
    (MultiplicativeBaseChange.rootsBaseChangeIso_sections f n (Over.mk s) a)

/-- The positive primitive-root marking commutes with actual pointed roots pullback. -/
theorem pointMark_pointed_pullback [NeZero n] (f : S ⟶ X)
    (s : Spec (.of C) ⟶ S) (x : Spec (.of C) ⟶ X) (hx : s ≫ f = x)
    (ζ : rootsOfUnity n C) (hζ : IsPrimitiveRoot (ζ : Cˣ) n)
    (a : Over.mk x ⟶ (MultiplicativeGroup.rootsGroupScheme X n).X) :
    GroupCohomology.Kummer.GeometricCoefficients.pointMark C s n ζ hζ
      (pointedGroupPointEquiv f s x hx (MultiplicativeGroup.rootsGroupScheme X n) a ≫
        (MultiplicativeBaseChange.rootsBaseChangeIso f n).hom.hom.hom) =
      GroupCohomology.Kummer.GeometricCoefficients.pointMark C x n ζ hζ a := by
  subst x
  change (GroupCohomology.Kummer.GeometricCoefficients.rootCoordinate C n ζ
      hζ).symm
    (Additive.ofMul (GroupCohomology.Kummer.GeometricCoefficients.pointRoots C
        s n _)) = _
  rw [pointRoots_pullback]
  change (GroupCohomology.Kummer.GeometricCoefficients.rootCoordinate C n ζ
      hζ).symm
    (Additive.ofMul (GroupCohomology.Kummer.GeometricCoefficients.pointRoots C
        (s ≫ f) n
      ((Scheme.FiniteEtale.GroupBaseChange.pullbackFiberMulEquiv f s
        (MultiplicativeGroup.rootsGroupScheme X n)).symm
      ((Scheme.FiniteEtale.GroupBaseChange.pullbackFiberMulEquiv f s
        (MultiplicativeGroup.rootsGroupScheme X n)) a)))) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

end RootPointCoordinates

section FiniteStalkFaithfulness
variable {X : Scheme.{u}} {C : Type u} [Field C] [IsSepClosed C]
variable (x : Spec (.of C) ⟶ X)
variable [GaloisCategory (Scheme.FiniteEtale X)] [PreGaloisCategory.FiberFunctor (fiberToFinite x)]
variable {L D : AbelianSheaf.{u, u + 1} X}
variable (R : CoefficientRepresentation L) (T : CoefficientRepresentation D)

include R T in
/-- Actual finite coefficient sheaf maps are determined by their literal
geometric stalk maps. The proof uses the genuine represented maps and the
faithful finite-etale fibre functor. -/
theorem finiteSheaf_hom_ext (q r : L ⟶ D)
    (h : ∀ a : coefficientFiber x L,
      ((Scheme.pointSmallEtale x).sheafFiber (A := AddCommGrpCat.{u + 1})).map q a =
      ((Scheme.pointSmallEtale x).sheafFiber (A := AddCommGrpCat.{u + 1})).map r a) : q = r := by
  have he : R.map T q = R.map T r := by
    apply Grp.hom_ext
    apply finiteEtale_hom_ext x
    intro a
    have hh := congrArg (T.fiberPointEquiv x) (h ((R.fiberPointEquiv x).symm (Additive.ofMul a)))
    rw [R.fiberPointEquiv_naturality x T q, R.fiberPointEquiv_naturality x T r,
      AddEquiv.apply_symm_apply] at hh
    exact Additive.ofMul.injective hh
  have hh := congrArg representedSheafMap he
  rw [R.map_sheaf T q, R.map_sheaf T r] at hh
  exact (cancel_epi R.iso.hom).mp ((cancel_mono T.iso.inv).mp hh)

end FiniteStalkFaithfulness

section RepresentedStalkCoherence
open _root_.AlgebraicGeometry.Scheme.EtaleH1.CoefficientStalkBaseChange
variable {X S T : Scheme.{u}} {C : Type u} [Field C] [IsSepClosed C]

/-- The literal represented coefficient point of an actual stalk element. -/
def representedPointEquiv (x : Spec (.of C) ⟶ X) (A : Grp (Over X))
    [IsCommMonObj A.X] [Etale A.X.hom] :
    coefficientFiber x (representedSheaf A) ≃+ Additive (Over.mk x ⟶ A.X) :=
  (representedFiberIso x A).addCommGroupIsoToAddEquiv.trans AddEquiv.ulift

/-- A genuinely represented finite coefficient has its identity representation. -/
def identityRepresentation (A : Grp (Over X)) [IsCommMonObj A.X]
    [IsFinite A.X.hom] [Etale A.X.hom] : CoefficientRepresentation (representedSheaf A) :=
  ⟨A, inferInstance, inferInstance, inferInstance, Iso.refl _⟩

/-- Actual stalk action of a represented group map is literal postcomposition. -/
theorem representedPointEquiv_map (x : Spec (.of C) ⟶ X)
    {A B : Grp (Over X)} [IsCommMonObj A.X] [IsCommMonObj B.X]
    [Etale A.X.hom] [Etale B.X.hom] (q : A ⟶ B)
    (a : coefficientFiber x (representedSheaf A)) :
    representedPointEquiv x B
      (((Scheme.pointSmallEtale x).sheafFiber (A := AddCommGrpCat.{u + 1})).map
        (representedSheafMap q) a) =
      Additive.ofMul ((representedPointEquiv x A a).toMul ≫ q.hom.hom) := by
  exact congrArg ULift.down (representedFiberEvaluation_naturality x q a)

/-- The actual inverse-image unit followed by represented base change is
exactly literal pullback of the represented coefficient point. -/
theorem representedPointEquiv_pullback (f : S ⟶ X) (s : Spec (.of C) ⟶ S)
    (x : Spec (.of C) ⟶ X) (hx : s ≫ f = x)
    (A : Grp (Over X)) [IsCommMonObj A.X] [Etale A.X.hom]
    (a : coefficientFiber x (representedSheaf A)) :
    representedPointEquiv s (baseChangedGroup f A)
      (((Scheme.pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})).map
        (representedSheafBaseChangeIso f A).hom
        (pointedStalkUnit f s (representedSheaf A) x hx a)) =
    Additive.ofMul (pointedGroupPointEquiv f s x hx A (representedPointEquiv x A a).toMul) := by
  subst x
  exact congrArg ULift.down (ConcreteCategory.congr_hom (represented_stalkUnit f s A) a)

/-- Pointed canonical stalk units retain ordinary coefficient naturality. -/
theorem pointedStalkUnit_naturality (f : S ⟶ X) (s : Spec (.of C) ⟶ S)
    (x : Spec (.of C) ⟶ X) (hx : s ≫ f = x)
    {L D : AbelianSheaf.{u, u + 1} X} (q : L ⟶ D) :
    ((Scheme.pointSmallEtale x).sheafFiber (A := AddCommGrpCat.{u + 1})).map q ≫
      pointedStalkUnit f s D x hx =
    pointedStalkUnit f s L x hx ≫
      ((Scheme.pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})).map ((inverseImage
          f).map q) := by
  subst x
  exact stalkUnit_naturality f s L q

/-- Actual represented coefficient pullback composes with the canonical group
pullback iso. This is an equality of ordinary sheaf maps, proved on literal
finite coefficient points after the fixed inverse-image composition. -/
theorem representedSheafBaseChangeIso_comp (f : S ⟶ X) (g : T ⟶ S)
    (t : Spec (.of C) ⟶ T)
    [GaloisCategory (Scheme.FiniteEtale T)] [PreGaloisCategory.FiberFunctor (fiberToFinite t)]
    (A : Grp (Over X)) [IsCommMonObj A.X] [IsFinite A.X.hom] [Etale A.X.hom] :
    (inverseImageComp f g).hom.app (representedSheaf A) ≫
      (inverseImage g).map (representedSheafBaseChangeIso f A).hom ≫
      (representedSheafBaseChangeIso g (baseChangedGroup f A)).hom ≫
      representedSheafMap (groupPullbackCompIso g f A).hom =
    (representedSheafBaseChangeIso (g ≫ f) A).hom := by
  let x := (t ≫ g) ≫ f
  let hx : t ≫ (g ≫ f) = x := (Category.assoc t g f).symm
  let R := identityRepresentation A
  apply finiteSheaf_hom_ext t
      (Scheme.EtaleH1.Naturality.pulledBackRepresentation (g ≫ f) R)
    (identityRepresentation (baseChangedGroup (g ≫ f) A))
  intro a
  obtain ⟨b, hb⟩ := (pointedPullbackStalkEquiv (g ≫ f) t (representedSheaf A) x hx
      R).symm.surjective a
  rw [← pointedStalkUnit_eq_inverse] at hb
  subst a
  apply (representedPointEquiv t (baseChangedGroup (g ≫ f) A)).injective
  let Ft := (Scheme.pointSmallEtale t).sheafFiber (A := AddCommGrpCat.{u + 1})
  let Fs := (Scheme.pointSmallEtale (t ≫ g)).sheafFiber (A := AddCommGrpCat.{u + 1})
  have hc := ConcreteCategory.congr_hom
    (pointedStalkUnit_comp f (t ≫ g) (representedSheaf A) g t x rfl rfl) b
  have hn := ConcreteCategory.congr_hom
    (pointedStalkUnit_naturality g t (t ≫ g) rfl
      (representedSheafBaseChangeIso f A).hom)
    (pointedStalkUnit f (t ≫ g) (representedSheaf A) x rfl b)
  simp only [ConcreteCategory.comp_apply] at hc hn
  simp only [Functor.map_comp, ConcreteCategory.comp_apply]
  erw [hc, ← hn]
  rw [representedPointEquiv_map t (groupPullbackCompIso g f A).hom,
    representedPointEquiv_pullback g t (t ≫ g) rfl (baseChangedGroup f A),
    representedPointEquiv_pullback f (t ≫ g) x rfl A,
    representedPointEquiv_pullback (g ≫ f) t x hx A]
  exact congrArg Additive.ofMul (groupPullbackCompIso_point g f t (t ≫ g) x rfl rfl A
    (representedPointEquiv x A b).toMul)

/-- Reverse group-pullback composition has the corresponding actual sheaf formula. -/
theorem representedSheafBaseChangeIso_comp_inv (f : S ⟶ X) (g : T ⟶ S)
    (t : Spec (.of C) ⟶ T)
    [GaloisCategory (Scheme.FiniteEtale T)] [PreGaloisCategory.FiberFunctor (fiberToFinite t)]
    (A : Grp (Over X)) [IsCommMonObj A.X] [IsFinite A.X.hom] [Etale A.X.hom] :
    (representedSheafBaseChangeIso (g ≫ f) A).hom ≫
      representedSheafMap (groupPullbackCompIso g f A).inv =
    (inverseImageComp f g).hom.app (representedSheaf A) ≫
      (inverseImage g).map (representedSheafBaseChangeIso f A).hom ≫
      (representedSheafBaseChangeIso g (baseChangedGroup f A)).hom := by
  have h := representedSheafBaseChangeIso_comp f g t A
  rw [← h]
  simp only [Category.assoc]
  rw [← representedSheafMap_comp, Iso.hom_inv_id, representedSheafMap_id, Category.comp_id]

/-- Literal equality of base maps is compatible with represented sheaf base change. -/
theorem representedSheafBaseChangeIso_congr {f g : S ⟶ X} (he : f = g)
    (A : Grp (Over X)) [IsCommMonObj A.X] [Etale A.X.hom] :
    (representedSheafBaseChangeIso f A).hom ≫
      representedSheafMap (eqToIso (congrArg (fun k => baseChangedGroup k A) he)).hom =
    (eqToIso (congrArg (fun k => (inverseImage k).obj (representedSheaf A)) he)).hom ≫
      (representedSheafBaseChangeIso g A).hom := by
  subst g
  simp [representedSheafMap_id]

/-- Three actual inverse-image pullbacks associate on finite coefficient sheaves.
This is proved on genuine stalks, where both routes are the same three literal
unit maps. No H1 class or coefficient-isomorphism independence is a premise. -/
theorem inverseImageComp_assoc_finite {U : Scheme.{u}}
    (f : S ⟶ X) (g : T ⟶ S) (h : U ⟶ T) (t : Spec (.of C) ⟶ U)
    [GaloisCategory (Scheme.FiniteEtale U)] [PreGaloisCategory.FiberFunctor (fiberToFinite t)]
    {L : AbelianSheaf.{u, u + 1} X} (R : CoefficientRepresentation L) :
    (inverseImageComp f (h ≫ g)).hom.app L ≫
      (inverseImageComp g h).hom.app ((inverseImage f).obj L) =
    (eqToIso (congrArg (fun k => (inverseImage k).obj L) (Category.assoc h g f))).hom ≫
      (inverseImageComp (g ≫ f) h).hom.app L ≫
      (inverseImage h).map ((inverseImageComp f g).hom.app L) := by
  let y := t ≫ h
  let z := y ≫ g
  let x := z ≫ f
  have hty : t ≫ h = y := rfl
  have htz : t ≫ (h ≫ g) = z := (Category.assoc t h g).symm
  have htx : t ≫ ((h ≫ g) ≫ f) = x := by simp only [x, z, y, Category.assoc]
  have htx' : t ≫ (h ≫ (g ≫ f)) = x := by simp only [x, z, y, Category.assoc]
  have hyx : y ≫ (g ≫ f) = x := (Category.assoc y g f).symm
  apply finiteSheaf_hom_ext t
      (Scheme.EtaleH1.Naturality.pulledBackRepresentation ((h ≫ g) ≫ f) R)
    (Scheme.EtaleH1.Naturality.pulledBackRepresentation h
        (Scheme.EtaleH1.Naturality.pulledBackRepresentation g
      (Scheme.EtaleH1.Naturality.pulledBackRepresentation f R)))
  intro a
  obtain ⟨b, hb⟩ := (pointedPullbackStalkEquiv ((h ≫ g) ≫ f) t L x htx R).symm.surjective a
  rw [← pointedStalkUnit_eq_inverse] at hb
  subst a
  have h₁ := ConcreteCategory.congr_hom
    (pointedStalkUnit_comp f z L (h ≫ g) t x htz rfl) b
  have h₂ := ConcreteCategory.congr_hom
    (pointedStalkUnit_comp g y ((inverseImage f).obj L) h t z hty rfl)
    (pointedStalkUnit f z L x rfl b)
  have h₃ := ConcreteCategory.congr_hom
    (pointedStalkUnit_congr ((h ≫ g) ≫ f) t L (Category.assoc h g f) x htx htx') b
  have h₄ := ConcreteCategory.congr_hom
    (pointedStalkUnit_comp (g ≫ f) y L h t x hty hyx) b
  have h₅ := ConcreteCategory.congr_hom
    (pointedStalkUnit_naturality h t y hty ((inverseImageComp f g).hom.app L))
    (pointedStalkUnit (g ≫ f) y L x hyx b)
  have h₆ := ConcreteCategory.congr_hom
    (pointedStalkUnit_comp f z L g y x rfl rfl) b
  simp only [ConcreteCategory.comp_apply] at h₁ h₂ h₃ h₄ h₅ h₆
  simp only [Functor.map_comp, ConcreteCategory.comp_apply]
  erw [h₁, h₂, h₃, h₄, ← h₅, h₆]
  rfl

end RepresentedStalkCoherence


section RootCupFieldCoefficients
variable {K L : Type u} [Field K] [Field L] [CharZero K] [CharZero L] [Algebra K L]
  (i : Field.absoluteGaloisGroup.RootsOfUnity.FieldPullbackIndependence.Embedding (K := K) (L
      := L)) (n : ℕ) [NeZero n]
  [GaloisCategory (Scheme.FiniteEtale (Spec (.of K)))]
  [PreGaloisCategory.FiberFunctor (fiberToFinite (geometricPoint K))]
  [GaloisCategory (Scheme.FiniteEtale (Spec (.of L)))]
  [PreGaloisCategory.FiberFunctor (fiberToFinite (geometricPoint L))]
/-- The represented roots group structure on each field spectrum used for field transport. -/
local instance (E : Type u) [Field E] : CommGrpObj (MultiplicativeGroup.rootsScheme (Spec (.of
    E)) n) :=
  MultiplicativeGroup.rootsCommGroup (Spec (.of E)) n
local instance (E : Type u) [Field E] : IsFinite (MultiplicativeGroup.rootsGroupScheme (Spec
    (.of E)) n).X.hom :=
  RootsFiniteEtale.rootsScheme_finite _ n (NeZero.pos n)
local instance (E : Type u) [Field E] [CharZero E] : Etale
    (MultiplicativeGroup.rootsGroupScheme (Spec (.of E)) n).X.hom :=
  RootsFiniteEtale.rootsScheme_etale _ n (NeZero.pos n)
      (GroupCohomology.Kummer.RootStalk.levelInvertible E n)

omit [CharZero K] [CharZero L]
    [GaloisCategory (Scheme.FiniteEtale (Spec (.of K)))]
    [PreGaloisCategory.FiberFunctor (fiberToFinite (geometricPoint K))]
    [GaloisCategory (Scheme.FiniteEtale (Spec (.of L)))]
    [PreGaloisCategory.FiberFunctor (fiberToFinite (geometricPoint L))] in
/-- The canonical roots group iso is exactly the previously constructed
literal field root-point transport. -/
-- Retain the original characteristic-zero and chosen field fibre-functor comparison inputs.
@[nolint unusedArguments]
theorem rootsBaseChangeIso_fieldPoint [CharZero K] [CharZero L]
    [GaloisCategory (Scheme.FiniteEtale (Spec (.of K)))]
    [PreGaloisCategory.FiberFunctor (fiberToFinite (geometricPoint K))]
    [GaloisCategory (Scheme.FiniteEtale (Spec (.of L)))]
    [PreGaloisCategory.FiberFunctor (fiberToFinite (geometricPoint L))]
    (a : Over.mk (geometricPoint K) ⟶ (MultiplicativeGroup.rootsGroupScheme (Spec (.of K)) n).X) :
    fieldGroupPointEquiv i (MultiplicativeGroup.rootsGroupScheme (Spec (.of K)) n) a ≫
      (MultiplicativeBaseChange.rootsBaseChangeIso
        (GroupCohomology.Kummer.FieldNaturality.fieldMorphism (K := K) (L :=
            L)) n).hom.hom.hom =
      GroupCohomology.Kummer.FieldNaturality.pullbackCoefficientPoint i n a :=
  MultiplicativeBaseChange.groupIsoOfSections_hom _ _ _ _ _ _

end RootCupFieldCoefficients
end AlgebraicGeometry.Scheme.EtaleH1.SheafCoherence
