/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.TupleCover
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.TrivialCoverFiber

/-! The tuple point given by an enumeration of all geometric fibre sections
is a point where the actual splitting map has a bijective fibre. -/

@[expose] public section

noncomputable section
set_option autoImplicit false

open _root_.CategoryTheory _root_.CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.FiniteEtale
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (Fiber baseChange fiber fiberBaseChangeEquiv
  fiberBaseChangeEquiv_symm_left fiberToFinite)

universe u

/-- The equivalence of cover fibres induced by the equality `h` of their field-valued base
points. -/
def fiberPointCongrEquiv {X : Scheme.{u}} {Ω : Type u} [Field Ω]
    {s t : Spec (CommRingCat.of Ω) ⟶ X} (h : s = t) (Y : Scheme.FiniteEtale X) :
    Fiber s Y ≃ Fiber t Y := by
  subst t
  exact Equiv.refl _

@[simp] theorem fiberPointCongrEquiv_left {X : Scheme.{u}} {Ω : Type u} [Field Ω]
    {s t : Spec (CommRingCat.of Ω) ⟶ X} (h : s = t) (Y : Scheme.FiniteEtale X) (p : Fiber s Y) :
    (fiberPointCongrEquiv h Y p).left = p.left := by
  subst t
  rfl

/-- The identification of the base-changed cover fibre at the tuple point with the original
fibre at `s`. -/
def tupleCoverTargetFiberEquiv {X : Scheme.{u}} (Y : Scheme.FiniteEtale X) (A : Type u) [Finite A]
    {Ω : Type u} [Field Ω] (s : Spec (CommRingCat.of Ω) ⟶ X) (t : A → Fiber s Y) :
    Fiber (tupleCoverPoint Y A s t) ((baseChange (tupleCover X Y A).obj.hom).obj Y) ≃
      Fiber s Y :=
  (fiberBaseChangeEquiv (tupleCover X Y A).obj.hom (tupleCoverPoint Y A s t) Y).symm.trans
    (fiberPointCongrEquiv (tupleCoverPoint_struct Y A s t) Y)

theorem splitMap_fiber_label {X : Scheme.{u}} (Y : Scheme.FiniteEtale X) (A : Type u) [Finite A]
    {Ω : Type u} [Field Ω] (s : Spec (CommRingCat.of Ω) ⟶ X) (t : A → Fiber s Y) (a : A) :
    tupleCoverTargetFiberEquiv Y A s t
        ((fiber (tupleCoverPoint Y A s t)).map (splitMap X Y A)
          (trivialCoverFiberPoint A (tupleCoverPoint Y A s t) a)) = t a := by
  apply Over.OverMorphism.ext
  change (fiberPointCongrEquiv (tupleCoverPoint_struct Y A s t) Y
    ((fiberBaseChangeEquiv (tupleCover X Y A).obj.hom (tupleCoverPoint Y A s t) Y).symm
      ((fiber (tupleCoverPoint Y A s t)).map (splitMap X Y A)
        (trivialCoverFiberPoint A (tupleCoverPoint Y A s t) a)))).left = (t a).left
  rw [fiberPointCongrEquiv_left]
  change ((fiberBaseChangeEquiv (tupleCover X Y A).obj.hom (tupleCoverPoint Y A s t) Y).symm
    (trivialCoverFiberPoint A (tupleCoverPoint Y A s t) a ≫ (splitMap X Y A).hom)).left = _
  refine (fiberBaseChangeEquiv_symm_left (tupleCover X Y A).obj.hom
    (tupleCoverPoint Y A s t) Y
    (trivialCoverFiberPoint A (tupleCoverPoint Y A s t) a ≫ (splitMap X Y A).hom)).trans ?_
  have hi := congrArg
    (fun f : terminalCover (tupleCover X Y A).obj.left ⟶
        (baseChange (tupleCover X Y A).obj.hom).obj Y => f.hom.left)
    (trivialCoverι_splitMap X Y A a)
  change (trivialCoverι (tupleCover X Y A).obj.left A a).hom.left ≫
    (splitMap X Y A).hom.left = (tupleCoverSection X Y A a).hom.left at hi
  change ((tupleCoverPoint Y A s t ≫
    (trivialCoverι (tupleCover X Y A).obj.left A a).hom.left) ≫
    (splitMap X Y A).hom.left) ≫
    pullback.fst Y.obj.hom (tupleCover X Y A).obj.hom = (t a).left
  calc
    _ = tupleCoverPoint Y A s t ≫
        (((trivialCoverι (tupleCover X Y A).obj.left A a).hom.left ≫
          (splitMap X Y A).hom.left) ≫
          pullback.fst Y.obj.hom (tupleCover X Y A).obj.hom) := by
      exact (congrArg
        (fun f : Spec (CommRingCat.of Ω) ⟶
            ((baseChange (tupleCover X Y A).obj.hom).obj Y).obj.left =>
          f ≫ pullback.fst Y.obj.hom (tupleCover X Y A).obj.hom)
        (Category.assoc _ _ _)).trans (Category.assoc _ _ _)
    _ = tupleCoverPoint Y A s t ≫
        ((tupleCoverSection X Y A a).hom.left ≫
          pullback.fst Y.obj.hom (tupleCover X Y A).obj.hom) := by rw [hi]
    _ = tupleCoverPoint Y A s t ≫ (tupleCoverπ X Y A a).hom.left := by
      rw [tupleCoverSection_fst]
    _ = (t a).left := tupleCoverPoint_π Y A s t a

theorem splitMap_fiber_bijective {X : Scheme.{u}} (Y : Scheme.FiniteEtale X) (A : Type u) [Finite A]
    {Ω : Type u} [Field Ω] (s : Spec (CommRingCat.of Ω) ⟶ X) (e : A ≃ Fiber s Y) :
    Function.Bijective ((fiberToFinite (tupleCoverPoint Y A s e)).map (splitMap X Y A)) := by
  let q := tupleCoverPoint Y A s e
  let sourceEquiv := trivialCoverFiberEquiv A q
  let targetEquiv := tupleCoverTargetFiberEquiv Y A s e
  have hlabel (a : A) :
      targetEquiv ((fiberToFinite q).map (splitMap X Y A) (sourceEquiv a)) = e a :=
    splitMap_fiber_label Y A s e a
  constructor
  · intro p r h
    obtain ⟨a, rfl⟩ := sourceEquiv.surjective p
    obtain ⟨b, rfl⟩ := sourceEquiv.surjective r
    have hab : a = b := e.injective
      ((hlabel a).symm.trans ((congrArg targetEquiv h).trans (hlabel b)))
    exact congrArg sourceEquiv hab
  · intro p
    obtain ⟨a, ha⟩ := e.surjective (targetEquiv p)
    refine ⟨sourceEquiv a, targetEquiv.injective ?_⟩
    exact (hlabel a).trans ha

end AlgebraicGeometry.Scheme.FiniteEtale

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 a7925d879edea785d10e83ec2e788370850a543f2a6dd5dcee5f7ab451e3f4bc.
Definitions, hypotheses and universes are retained modulo native names. -/
