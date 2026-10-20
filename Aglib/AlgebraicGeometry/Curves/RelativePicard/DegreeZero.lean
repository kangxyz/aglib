/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.LineBundleDegree
public import Aglib.AlgebraicGeometry.Picard.Relative.Groups
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.Properties
public import Aglib.AlgebraicGeometry.Properties.Normal.Basic
public import Aglib.AlgebraicGeometry.SchemeOverField
public import Aglib.AlgebraicGeometry.Modules.InternalHom
public import Aglib.AlgebraicGeometry.Modules.Invertible.Basic
public import Aglib.AlgebraicGeometry.Modules.Invertible.Dual
public import Aglib.AlgebraicGeometry.Modules.Invertible.Tensor
public import Aglib.AlgebraicGeometry.Modules.Invertible.TensorAssociator
public import Aglib.AlgebraicGeometry.Modules.Pullback.OpenRestriction
public import Aglib.AlgebraicGeometry.Modules.Invertible.Pullback

/-!
# Fibrewise degree zero for the actual normalized Picard functor

Each test is an arbitrary algebraically closed field K, arbitrary structural
map Spec K → Spec F, and every actual Over-morphism Spec K → T. The degree
is C's actual Picard degree on the actual base-changed curve, after the actual
family pullback. Thus the subgroup contains exactly normalized classes whose
geometric-fibre degrees vanish. No chosen algebraic closure, resizing, pointwise
surrogate Picard group, or assumed degree function is used.

Family-map composition proves stability under every test-scheme map, yielding
a commutative group subfunctor. This constructs the candidate degree-zero
functor; representability and the Abel inverse are separate obligations.
No new general theorem family is retained here. The parameters are the
already disclosed B1 dimension/regularity/normality, C product formula and
optional 01CD tensor-pullback family needed to construct actual group maps.
The canonical-degree family is not a parameter or dependency of the proofs.

Incoming actual curveDegree is the independent LineBundleDegree adapter.
The source imports no genus, differential, or Riemann–Hurwitz module.
Application K2-018#prop:k2018-arithmetic-characters, source
e73d98b1b5c1e5abcdebf7d058e436d792b87982; frozen engineering basis
7f86e4a1763cc4ec35e9b0a8acd659750355a0de and unchanged pins.
-/

open _root_.AlgebraicGeometry.Scheme
  (NormalComponentsOpen SmoothClosedPointDimension SmoothFieldDimension SmoothFieldNormality
    SmoothFieldRegularity)
open _root_.AlgebraicGeometry.Scheme.OverField (Base FScheme)

/- Interface migration basis: 46f53465aaf3b0167049e9c8e9e2294111bb4281.
Original mathematical and construction source identities are retained. -/

@[expose] public section

noncomputable section
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.RelativePicard.Classes
open AlgebraicGeometry.Scheme
open CategoryTheory Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.OverField.Curve
namespace AlgebraicGeometry.Scheme.OverField.Curve.RelativePicard
universe u
open AlgebraicGeometry.Scheme.Hom
variable (hnormal : SmoothFieldNormality.{u}) (hcomp : NormalComponentsOpen.{u})
variable (hreg : SmoothFieldRegularity.{u}) (hclosed : SmoothClosedPointDimension.{u})
variable (hdim : SmoothFieldDimension.{u}) (hprod : Picard.Degree.ProperCurveProductFormula.{u})
variable (htensor : AlgebraicGeometry.Scheme.Modules.Invertible.ModuleTensorPullback.{u})
variable {F : Type u} [Field F] (X : FScheme F) (hX : Properties X)

/-- The degree homomorphism obtained by restricting a family Picard class to the fibre over a
field-valued test point. -/
def fibreDegree (T : FScheme F) (K : Type u) [Field K]
    (s : Spec (.of K) ⟶ Base F) (t : Over.mk s ⟶ T) :
    Invertible.PicardGroup (pullback X.hom T.hom) →+ ℤ :=
  (curveDegree hnormal hcomp hreg hclosed hdim hprod
    (Over.mk (pullback.snd X.hom s)) (curveProperties_baseChange hX K s)).comp
    (AlgebraicGeometry.Scheme.Modules.Invertible.pullbackHom htensor (familyMap X.hom T.hom s
      t.left (Over.w t)))

theorem fibreDegree_pullback {T T' : FScheme F} (f : T' ⟶ T)
    (K : Type u) [Field K] (s : Spec (.of K) ⟶ Base F) (t : Over.mk s ⟶ T')
    (a : Invertible.PicardGroup (pullback X.hom T.hom)) :
    fibreDegree hnormal hcomp hreg hclosed hdim hprod htensor X hX T' K s t
      (Invertible.pullbackClass (familyMap X.hom T.hom T'.hom f.left (Over.w f)) a) =
    fibreDegree hnormal hcomp hreg hclosed hdim hprod htensor X hX T K s (t ≫ f) a := by
  dsimp only [fibreDegree, AddMonoidHom.comp_apply,
    AlgebraicGeometry.Scheme.Modules.Invertible.pullbackHom_apply]
  apply congrArg (curveDegree hnormal hcomp hreg hclosed hdim hprod
    (Over.mk (pullback.snd X.hom s)) (curveProperties_baseChange hX K s))
  rw [← Invertible.pullbackClass_comp, familyMap_comp]
  rfl

variable (o : Base F ⟶ X.left) (ho : o ≫ X.hom = 𝟙 _)
set_option backward.isDefEq.respectTransparency false in
/-- The subgroup of origin-normalized Picard classes having degree zero on every algebraically
closed field-valued fibre. -/
def degreeZeroGroup (T : FScheme F) : AddSubgroup (normalizedGroup htensor X.hom o ho T) where
  carrier a := ∀ (K : Type u) [Field K] [IsAlgClosed K]
    (s : Spec (.of K) ⟶ Base F) (t : Over.mk s ⟶ T),
      fibreDegree hnormal hcomp hreg hclosed hdim hprod htensor X hX T K s t a.val = 0
  zero_mem' := by
    intro K _ _ s t
    exact map_zero (fibreDegree hnormal hcomp hreg hclosed hdim hprod htensor X hX T K s t)
  add_mem' {a b} ha hb := by
    intro K _ _ s t
    change fibreDegree hnormal hcomp hreg hclosed hdim hprod htensor X hX T K s t (a.val + b.val)
      = 0
    rw [map_add, ha K s t, hb K s t, zero_add]
  neg_mem' {a} ha := by
    intro K _ _ s t
    change fibreDegree hnormal hcomp hreg hclosed hdim hprod htensor X hX T K s t (-a.val) = 0
    rw [map_neg, ha K s t, neg_zero]

/-- The pullback homomorphism on the subgroups of fibrewise degree-zero normalized Picard
classes. -/
def degreeZeroMap {T T' : FScheme F} (f : T' ⟶ T) :
    degreeZeroGroup hnormal hcomp hreg hclosed hdim hprod htensor X hX o ho T →+
      degreeZeroGroup hnormal hcomp hreg hclosed hdim hprod htensor X hX o ho T' where
  toFun a := ⟨normalizedMap htensor X.hom o ho f a.val, by
    intro K _ _ s t
    exact (fibreDegree_pullback hnormal hcomp hreg hclosed hdim hprod htensor X hX f K s t
      a.val.val).trans
      (a.property K s (t ≫ f))⟩
  map_zero' := by apply Subtype.ext; exact map_zero _
  map_add' a b := by apply Subtype.ext; exact map_add _ _ _

/-- The contravariant functor of fibrewise degree-zero normalized Picard classes on test schemes
over `F`. -/
def degreeZeroGroupFunctor : (FScheme F)ᵒᵖ ⥤ AddCommGrpCat.{u+1} where
  obj T := AddCommGrpCat.of (degreeZeroGroup hnormal hcomp hreg hclosed hdim hprod htensor X hX o
    ho T.unop)
  map f := AddCommGrpCat.ofHom (degreeZeroMap hnormal hcomp hreg hclosed hdim hprod htensor X hX o
    ho f.unop)
  map_id T := by
    ext a
    exact congrArg (fun k ↦ k a.val.val) ((familyPicardFunctor X.hom).map_id T)
  map_comp f g := by
    ext a
    exact congrArg (fun k ↦ k a.val.val) ((familyPicardFunctor X.hom).map_comp f g)

/-- The natural inclusion of fibrewise degree-zero classes into the normalized Picard group
functor. -/
def degreeZeroInclusion : degreeZeroGroupFunctor hnormal hcomp hreg hclosed hdim hprod htensor X
  hX o ho ⟶
    normalizedGroupFunctor htensor X.hom o ho where
  app _ := AddCommGrpCat.ofHom (AddSubgroup.subtype _)
  naturality := by intros; rfl
end AlgebraicGeometry.Scheme.OverField.Curve.RelativePicard
