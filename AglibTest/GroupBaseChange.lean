/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Group.Kernel.PrimeDegree
public import Aglib.AlgebraicGeometry.Group.Kernel.DeckTranslation
public import Aglib.AlgebraicGeometry.Group.Kernel.Remarking
public import Aglib.AlgebraicGeometry.Group.BaseChange.CyclicKernel
public import Aglib.AlgebraicGeometry.Group.BaseChange.UnitRange
public import Aglib.AlgebraicGeometry.Group.BaseChange.FullFaithful
public import Aglib.AlgebraicGeometry.Group.BaseChange.Composition
public import Aglib.AlgebraicGeometry.FundamentalGroup.Field.EmbeddingConjugacy
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.GroupBaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.RepresentedKernel
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.MarkedCoefficients

/-!
# Clients and original-map comparisons for group base change

The examples retain the actual kernel pullback and inclusion, all-test-object
marking, exact pullback of a lifted group map, and the original fibre-action
construction of a field group isomorphism. No arithmetic marked object is used.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj CategoryTheory.PreGaloisCategory
open AlgebraicGeometry.Scheme.Group
open AlgebraicGeometry.Scheme.Group.BaseChange
open AlgebraicGeometry.Scheme.FiniteEtale
open AlgebraicGeometry.Scheme.FiniteEtale.GroupDescent
open AlgebraicGeometry.Scheme.FiniteEtale.FiberTorsorActions
open AlgebraicGeometry.Scheme.EtaleCohomology
open AlgebraicGeometry.Scheme.EtaleCohomology.SchemeTorsorClassification
open AlgebraicGeometry.Scheme.EtaleCohomology.MarkedCoefficients
open AlgebraicGeometry.Scheme.OverField

universe u

namespace AglibTest.GroupBaseChange

attribute [local instance] Over.cartesianMonoidalCategory

example {S : Scheme.{u}} {G E : Grp (Over S)} (p : G ⟶ E) :
    Kernel.group p =
      pullback p (Grp.homMk (A := Grp.trivial (Over S)) (B := E) η[E.X]) := rfl

example {S : Scheme.{u}} {G E : Grp (Over S)} (p : G ⟶ E) :
    (Kernel.marking p).inclusion = Kernel.inclusion p := rfl

example {S T : Scheme.{u}} (f : S ⟶ T) {A G E : Grp (Over T)} {p : G ⟶ E}
    (m : KernelMarking A G E p) :
    (BaseChange.kernelMarking f m).inclusion =
      (groupSchemeBaseChange f).functor.map m.inclusion := rfl

example {S : Scheme.{u}} {A A' G E : Grp (Over S)} {p : G ⟶ E}
    (m : KernelMarking A G E p) (e : A ≅ A') :
    (m.transportCoefficient e).inclusion = e.inv ≫ m.inclusion := rfl

example {S : Scheme.{u}} (A A' : Grp (Over S)) (e : A ≅ A')
    (U : Over S) (a : U ⟶ A.X) :
    ((yonedaGrp.mapIso e).app (Opposite.op U)).groupIsoToMulEquiv a =
      a ≫ e.hom.hom.hom := rfl

example {S : Scheme.{u}} {A B : Grp (Over S)}
    [IsCommMonObj A.X] [IsCommMonObj B.X] (e : A ≅ B) :
    (representedSheafIso e).hom = representedSheafMap e.hom := rfl

/-- Prime cyclicity concerns the literal kernel, without a supplied marking. -/
example {F : Type u} [Field F] {G E : Grp (FScheme F)} (p : G ⟶ E)
    {n : ℕ} (hn : n.Prime) [IsFinite p.hom.hom.left] [Etale p.hom.hom.left]
    (hd : HasGeometricDegree p.hom.hom n) :
    PointedCovers.CyclicCoefficient (Kernel.group p) n :=
  Kernel.cyclicCoefficient_of_prime_degree p hn hd

example {F K : Type u} [Field F] [Field K] (s : Base K ⟶ Base F)
    {G E : Grp (FScheme F)} (p : G ⟶ E) {n : ℕ}
    (hd : HasGeometricDegree p.hom.hom n) :
    HasGeometricDegree ((groupSchemeBaseChange s).functor.map p).hom.hom n :=
  geometricDegreeBaseChange s p hd

example {X Z : Scheme.{u}} (j : Z ⟶ X)
    [(baseChange j).Full] [(baseChange j).Faithful]
    (H J : Grp (Over X)) [IsFinite H.X.hom] [Etale H.X.hom]
    [IsFinite J.X.hom] [Etale J.X.hom]
    (α : (Over.pullback j).mapGrp.obj H ⟶ (Over.pullback j).mapGrp.obj J) :
    (Over.pullback j).mapGrp.map (extendedGroupHom j H J α) = α :=
  extendedGroupHom_pullback j H J α

section OriginalFibreConstruction

open AlgebraicGeometry.Scheme.FiniteEtale.FieldGalois

variable (F : Type u) [Field F]
  [GaloisCategory (Scheme.FiniteEtale (Base F))]
  [PreGaloisCategory.FiberFunctor (fiberToFinite (geometricPoint F))]
  (A B : Grp (FScheme F))
  [IsFinite A.X.hom] [Etale A.X.hom] [IsFinite B.X.hom] [Etale B.X.hom]
  (e : (Over.mk (geometricPoint F) ⟶ A.X) ≃*
    (Over.mk (geometricPoint F) ⟶ B.X))
  (he : ∀ (g : FieldFundamentalGroup F) x,
    e (g.hom.app (coefficientCover A) x) = g.hom.app (coefficientCover B) (e x))

/-- Test fixture containing the packet's original continuous-action iso expression. -/
private def packetActionIso :
    (classification (geometricPoint F)).functor.obj (coefficientCover A) ≅
      (classification (geometricPoint F)).functor.obj (coefficientCover B) :=
  ObjectProperty.isoMk _ (Action.mkIso (FintypeCat.equivEquivIso e.toEquiv) (fun g => by
    apply FintypeCat.hom_ext
    intro x
    exact he g x))

/-- The same comparison also holds in the original finite-etale cover category. -/
example :
    (classification (geometricPoint F)).functor.preimageIso (packetActionIso F A B e he) =
      ObjectProperty.isoMk _ (descendFiberIso (geometricPoint F)
        (Y := coefficientCover A) (Z := coefficientCover B) e.toEquiv he) := by
  apply Iso.ext
  apply ObjectProperty.hom_ext
  apply finiteEtale_hom_ext (geometricPoint F) (Y := A.X) (Z := B.X)
  intro x
  have h := (classification (geometricPoint F)).functor.map_preimage
    (packetActionIso F A B e he).hom
  have hx : x ≫ ((classification (geometricPoint F)).functor.preimageIso
      (packetActionIso F A B e he)).hom.hom = e x :=
    ConcreteCategory.congr_hom (C := FintypeCat) (congrArg (fun f => f.hom.hom) h) x
  exact hx.trans (descendFiberIso_hom_fiber (geometricPoint F)
    (Y := coefficientCover A) (Z := coefficientCover B) e.toEquiv he x).symm

/-- The original chosen scheme isomorphism equals the actual native reconstruction. -/
example :
    (Scheme.FiniteEtale.forget (Base F)).mapIso
        ((classification (geometricPoint F)).functor.preimageIso
          (packetActionIso F A B e he)) =
      (Grp.forget (FScheme F)).mapIso
        (descendFiberGroupIso (geometricPoint F) A B e he) := by
  apply Iso.ext
  apply finiteEtale_hom_ext (geometricPoint F) (Y := A.X) (Z := B.X)
  intro x
  have h := (classification (geometricPoint F)).functor.map_preimage
    (packetActionIso F A B e he).hom
  have hx : x ≫ ((Scheme.FiniteEtale.forget (Base F)).mapIso
      ((classification (geometricPoint F)).functor.preimageIso
        (packetActionIso F A B e he))).hom = e x :=
    ConcreteCategory.congr_hom (C := FintypeCat) (congrArg (fun f => f.hom.hom) h) x
  exact hx.trans (descendFiberGroupIso_fiber (geometricPoint F) A B e he x).symm

end OriginalFibreConstruction

end AglibTest.GroupBaseChange
