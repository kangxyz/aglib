/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.CoverPreservation
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.TrivialCoverConstant
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.BaseChange

/-! A finite product of a cover, its actual field-valued tuple point, and the
map from the labelled trivial cover to its pullback. No Galois-category
premises or connectedness assumptions enter these constructions. -/

@[expose] public section

noncomputable section
set_option autoImplicit false

open _root_.CategoryTheory _root_.CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.FiniteEtale
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (Fiber baseChange forget)

universe u

/-- The finite product of copies of `Y` indexed by `A` in finite étale schemes over `X` . -/
def tupleCover (X : Scheme.{u}) (Y : Scheme.FiniteEtale X) (A : Type u)
    [Finite A] : Scheme.FiniteEtale X :=
  ∏ᶜ fun _ : A => Y

/-- The projection from the tuple cover to its coordinate indexed by `a` . -/
abbrev tupleCoverπ (X : Scheme.{u}) (Y : Scheme.FiniteEtale X) (A : Type u) [Finite A]
    (a : A) : tupleCover X Y A ⟶ Y :=
  Pi.π (fun _ : A => Y) a

/-- The tuple cover is a product in the actual over-category, so its
universal property accepts an arbitrary geometric point over `X`. -/
def tupleCoverOverIsLimit (X : Scheme.{u}) (Y : Scheme.FiniteEtale X) (A : Type u) [Finite A] :
    IsLimit (Fan.mk (tupleCover X Y A).obj (fun a => (tupleCoverπ X Y A a).hom)) :=
  isLimitOfHasProductOfPreservesLimit (forget X) (fun _ : A => Y)

/-- The empty tuple is the terminal cover by the typed product universal
property; its construction does not require a selected component. -/
def tupleCoverIsTerminalOfIsEmpty (X : Scheme.{u}) (Y : Scheme.FiniteEtale X)
    (A : Type u) [Finite A] [IsEmpty A] : IsTerminal (tupleCover X Y A) :=
  .ofUniqueHom (fun _ => Pi.lift (fun a : A => isEmptyElim a))
    (fun _ _ => Pi.hom_ext _ _ (fun a : A => isEmptyElim a))

/-- The fiber point of the tuple cover induced by the family `t` of fiber points over `s` . -/
def tupleCoverPointOver {X : Scheme.{u}} (Y : Scheme.FiniteEtale X) (A : Type u) [Finite A]
    {Ω : Type u} [Field Ω] (s : Spec (CommRingCat.of Ω) ⟶ X)
    (t : A → Fiber s Y) : Fiber s (tupleCover X Y A) :=
  (tupleCoverOverIsLimit X Y A).lift (Fan.mk (Over.mk s) t)

@[reassoc] theorem tupleCoverPointOver_π {X : Scheme.{u}} (Y : Scheme.FiniteEtale X)
    (A : Type u) [Finite A] {Ω : Type u} [Field Ω]
    (s : Spec (CommRingCat.of Ω) ⟶ X) (t : A → Fiber s Y) (a : A) :
    tupleCoverPointOver Y A s t ≫ (tupleCoverπ X Y A a).hom = t a :=
  (tupleCoverOverIsLimit X Y A).fac (Fan.mk (Over.mk s) t) (Discrete.mk a)

/-- The underlying scheme morphism of the tuple fiber point determined by `t` . -/
abbrev tupleCoverPoint {X : Scheme.{u}} (Y : Scheme.FiniteEtale X) (A : Type u) [Finite A]
    {Ω : Type u} [Field Ω] (s : Spec (CommRingCat.of Ω) ⟶ X)
    (t : A → Fiber s Y) : Spec (CommRingCat.of Ω) ⟶ (tupleCover X Y A).obj.left :=
  (tupleCoverPointOver Y A s t).left

@[reassoc] theorem tupleCoverPoint_struct {X : Scheme.{u}} (Y : Scheme.FiniteEtale X)
    (A : Type u) [Finite A] {Ω : Type u} [Field Ω]
    (s : Spec (CommRingCat.of Ω) ⟶ X) (t : A → Fiber s Y) :
    tupleCoverPoint Y A s t ≫ (tupleCover X Y A).obj.hom = s :=
  Over.w (tupleCoverPointOver Y A s t)

@[reassoc] theorem tupleCoverPoint_π {X : Scheme.{u}} (Y : Scheme.FiniteEtale X)
    (A : Type u) [Finite A] {Ω : Type u} [Field Ω]
    (s : Spec (CommRingCat.of Ω) ⟶ X) (t : A → Fiber s Y) (a : A) :
    tupleCoverPoint Y A s t ≫ (tupleCoverπ X Y A a).hom.left = (t a).left :=
  congrArg (fun f : Over.mk s ⟶ Y.obj => f.left) (tupleCoverPointOver_π Y A s t a)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A product projection is a section of the cover pulled back to the
tuple cover. -/
def tupleCoverSection (X : Scheme.{u}) (Y : Scheme.FiniteEtale X) (A : Type u) [Finite A]
    (a : A) : terminalCover (tupleCover X Y A).obj.left ⟶
      (baseChange (tupleCover X Y A).obj.hom).obj Y := by
  refine ObjectProperty.homMk ?_
  change Over.mk (𝟙 (tupleCover X Y A).obj.left) ⟶
    Over.mk (pullback.snd Y.obj.hom (tupleCover X Y A).obj.hom)
  exact Over.homMk
    (pullback.lift (tupleCoverπ X Y A a).hom.left (𝟙 _)
      (by rw [Category.id_comp]; exact Over.w (tupleCoverπ X Y A a).hom))
    (pullback.lift_snd _ _ _)

@[reassoc] theorem tupleCoverSection_fst (X : Scheme.{u}) (Y : Scheme.FiniteEtale X)
    (A : Type u) [Finite A] (a : A) :
    (tupleCoverSection X Y A a).hom.left ≫
      pullback.fst Y.obj.hom (tupleCover X Y A).obj.hom =
      (tupleCoverπ X Y A a).hom.left :=
  pullback.lift_fst _ _ _

/-- The map from the trivial `A` -cover of the tuple scheme to the pullback of `Y` , using
coordinate sections. -/
def splitMap (X : Scheme.{u}) (Y : Scheme.FiniteEtale X) (A : Type u) [Finite A] :
    trivialCover (tupleCover X Y A).obj.left A ⟶
      (baseChange (tupleCover X Y A).obj.hom).obj Y :=
  Sigma.desc (fun a => tupleCoverSection X Y A a)

@[reassoc] theorem trivialCoverι_splitMap (X : Scheme.{u}) (Y : Scheme.FiniteEtale X)
    (A : Type u) [Finite A] (a : A) :
    trivialCoverι (tupleCover X Y A).obj.left A a ≫ splitMap X Y A =
      tupleCoverSection X Y A a :=
  Sigma.ι_comp_desc _ _

end AlgebraicGeometry.Scheme.FiniteEtale

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 99ad614d168d2a3ebfd11bf282d1d929c87bb1b6b6da604ea7f0a416670a25f3.
Definitions, hypotheses and universes are retained modulo native names. -/
