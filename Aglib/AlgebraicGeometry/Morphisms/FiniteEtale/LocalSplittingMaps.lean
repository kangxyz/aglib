/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.SplitMapFiber
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.TrivialCoverBaseChange
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.FiniteCoverSheafBaseChange

/-! The actual restriction and sheaf maps that consume an isomorphism on an
open locus of the tuple cover. The producer of that locus is separate. -/

@[expose] public section

noncomputable section
set_option autoImplicit false

open _root_.CategoryTheory _root_.CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.EtaleH1

namespace AlgebraicGeometry.Scheme.FiniteEtale
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (Fiber baseChange baseChangeComp)

universe u

/-- The étale chart over `X` obtained from the open subscheme `U` of the tuple cover. -/
def localSplitChart {X : Scheme.{u}} (Y : Scheme.FiniteEtale X) (A : Type u) [Finite A]
    (U : (tupleCover X Y A).obj.left.Opens) : X.Etale :=
  Scheme.Etale.mk (U.ι ≫ (tupleCover X Y A).obj.hom)

/-- The splitting isomorphism over `U`, assuming the restriction of `splitMap` to `U` is an
isomorphism. -/
def localSplitIso {X : Scheme.{u}} (Y : Scheme.FiniteEtale X) (A : Type u) [Finite A]
    (U : (tupleCover X Y A).obj.left.Opens)
    [IsIso ((baseChange U.ι).map (splitMap X Y A))] :
    trivialCover U.toScheme A ≅ (baseChange (U.ι ≫ (tupleCover X Y A).obj.hom)).obj Y :=
  trivialCoverBaseChangeIso U.ι A ≪≫
    asIso ((baseChange U.ι).map (splitMap X Y A)) ≪≫
      (baseChangeComp (tupleCover X Y A).obj.hom U.ι).symm.app Y

/-- The constant-sheaf comparison on `U`, assuming the restricted splitting map is an
isomorphism. -/
def localSplitSheafIso {X : Scheme.{u}} (Y : Scheme.FiniteEtale X) (A : Type u) [Finite A]
    (U : (tupleCover X Y A).obj.left.Opens)
    [IsIso ((baseChange U.ι).map (splitMap X Y A))] :
    (setInverseImage (localSplitChart Y A U).hom).obj (finiteCoverSectionSheaf Y) ≅
      (constantSheaf (Scheme.smallEtaleTopology U.toScheme) (Type (u + 1))).obj
        (ULift.{u + 1} A) :=
  finiteCoverSectionSheafBaseChangeIso (U.ι ≫ (tupleCover X Y A).obj.hom) Y ≪≫
    finiteCoverSectionSheafIso (localSplitIso Y A U).symm ≪≫
      trivialCoverConstantIso U.toScheme A

/-- The point of the local splitting chart determined by the tuple `t` and its membership proof
`hu`. -/
def localSplitChartPoint {X : Scheme.{u}} (Y : Scheme.FiniteEtale X) (A : Type u) [Finite A]
    {Ω : Type u} [Field Ω] (s : Spec (CommRingCat.of Ω) ⟶ X) (t : A → Fiber s Y)
    (U : (tupleCover X Y A).obj.left.Opens)
    (hu : tupleCoverPoint Y A s t (default : Spec (CommRingCat.of Ω)) ∈ U) :
    (localSplitChart Y A U).left :=
  ⟨tupleCoverPoint Y A s t (default : Spec (CommRingCat.of Ω)), hu⟩

theorem localSplitChartPoint_image {X : Scheme.{u}} (Y : Scheme.FiniteEtale X) (A : Type u)
    [Finite A]
    {Ω : Type u} [Field Ω] (s : Spec (CommRingCat.of Ω) ⟶ X) (t : A → Fiber s Y)
    (U : (tupleCover X Y A).obj.left.Opens)
    (hu : tupleCoverPoint Y A s t (default : Spec (CommRingCat.of Ω)) ∈ U) :
    (localSplitChart Y A U).hom (localSplitChartPoint Y A s t U hu) = s default :=
  congrArg (fun f : Spec (CommRingCat.of Ω) ⟶ X => f default)
    (tupleCoverPoint_struct Y A s t)

end AlgebraicGeometry.Scheme.FiniteEtale

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 bbb65a026d0edafbdd07c279d94283ce80bdb21f2738946aca433d6d2276e5e7.
Definitions, hypotheses and universes are retained modulo native names. -/
