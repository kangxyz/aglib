/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AffineScheme.AlgebraMapTriangles
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.BaseChange

/-! # The same whole cover on the coefficient generic fibre

The common-field embedding determines the original generic square. The
existing finite-etale base-change composition isomorphisms carry the specified
whole-cover reconstruction through that square. No new cover or field model
is selected. This supplies geometry for arbitrary-coefficient continuity over
`B`, the coefficient base, not over `A`, the smooth-target base. No class-zero
or initial normal arithmetic model is supplied here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization

universe u

variable (A B F E : Type u) [CommRing A] [CommRing B] [Field F] [Field E]
  [Algebra A B] [Algebra A F] [Algebra A E] [Algebra B E]
  [IsScalarTower A B E] (a : F →ₐ[A] E)
  {X : Scheme.{u}} (p : X ⟶ Spec (.of A))

local notation "b" => Spec.algebraMap A B
local notation "s" => Spec.algebraMap A F
local notation "t" => Spec.algebraMap B E
local notation "ρ" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom a))
local notation "Y" => pullback p b
local notation "h" => pullback.fst p b
local notation "e" => pullback.snd p b
local notation "D" => pullback e t
local notation "δ" => pullback.fst e t
local notation "π" => pullback.fst p s

/-- The original common-field square, retaining the specified ambient map. -/
theorem coefficientGeneric_base_square : t ≫ b = ρ ≫ s := by
  rw [Spec.map_algHom_algebraMap]
  simp only [Spec.algebraMap, ← Spec.map_comp]
  exact congrArg Spec.map (CommRingCat.hom_ext
    (IsScalarTower.algebraMap_eq A B E).symm)

/-- The actual map from the coefficient generic fibre to the target generic
fibre uses the original scheme projection and original common-field map. -/
def coefficientGenericMap : D ⟶ pullback p s :=
  pullback.lift (δ ≫ h) (pullback.snd e t ≫ ρ) (by
    calc
      (δ ≫ h) ≫ p = δ ≫ (h ≫ p) := Category.assoc ..
      _ = δ ≫ (e ≫ b) := congrArg (fun m => δ ≫ m) (pullback.condition (f := p) (g := b))
      _ = (δ ≫ e) ≫ b := (Category.assoc ..).symm
      _ = (pullback.snd e t ≫ t) ≫ b :=
        congrArg (fun m => m ≫ b) (pullback.condition (f := e) (g := t))
      _ = pullback.snd e t ≫ (t ≫ b) := Category.assoc ..
      _ = pullback.snd e t ≫ (ρ ≫ s) :=
        congrArg (fun m => pullback.snd e t ≫ m)
          (coefficientGeneric_base_square A B F E a)
      _ = (pullback.snd e t ≫ ρ) ≫ s := (Category.assoc ..).symm)

@[reassoc (attr := simp)] theorem coefficientGenericMap_fst :
    coefficientGenericMap A B F E a p ≫ π = δ ≫ h := pullback.lift_fst ..

@[reassoc (attr := simp)] theorem coefficientGenericMap_snd :
    coefficientGenericMap A B F E a p ≫ pullback.snd p s =
      pullback.snd e t ≫ ρ := pullback.lift_snd ..

/-- The same original whole cover and same original generic cover, compared on
`D` solely by original base-change composition and the given reconstruction. -/
def coefficientGenericCoverReconstruction
    (G : FiniteEtale X) (Z : FiniteEtale (pullback p s))
    (r : (baseChange π).obj G ≅ Z) :
    (baseChange δ).obj ((baseChange h).obj G) ≅
      (baseChange (coefficientGenericMap A B F E a p)).obj Z := by
  calc
    (baseChange δ).obj ((baseChange h).obj G) ≅
        (baseChange (δ ≫ h)).obj G := (baseChangeComp h δ).symm.app G
    _ ≅ (baseChange (coefficientGenericMap A B F E a p ≫ π)).obj G :=
      eqToIso (congrArg (fun (v : D ⟶ X) => (baseChange v).obj G)
        (coefficientGenericMap_fst A B F E a p).symm)
    _ ≅ (baseChange (coefficientGenericMap A B F E a p)).obj
        ((baseChange π).obj G) :=
      (baseChangeComp π (coefficientGenericMap A B F E a p)).app G
    _ ≅ (baseChange (coefficientGenericMap A B F E a p)).obj Z :=
      (baseChange (coefficientGenericMap A B F E a p)).mapIso r

/-- Reconstruction preserves the actual projection to the coefficient generic
fibre. This is the literal triangle needed by arbitrary-coefficient zero
transport, rather than an abstract existence of isomorphic covers. -/
@[reassoc] theorem coefficientGenericCoverReconstruction_over
    (G : FiniteEtale X) (Z : FiniteEtale (pullback p s))
    (r : (baseChange π).obj G ≅ Z) :
    (coefficientGenericCoverReconstruction A B F E a p G Z r).hom.hom.left ≫
        ((baseChange (coefficientGenericMap A B F E a p)).obj Z).obj.hom =
      ((baseChange δ).obj ((baseChange h).obj G)).obj.hom :=
  Over.w (coefficientGenericCoverReconstruction A B F E a p G Z r).hom.hom

omit [Algebra A E] [IsScalarTower A B E] in
/-- The entire reconstructed source, not just an open piece, is the original
coefficient-generic pullback of the whole cover on `Y`. This is the square
consumed by `exists_fraction_principalOpen_composite_zero_of_reconstruction`
with coefficient base `B` and fraction field `E`. -/
theorem coefficientGenericCover_isPullback (G : FiniteEtale X) :
    IsPullback
      (pullback.fst ((baseChange h).obj G).obj.hom δ)
      (pullback.snd ((baseChange h).obj G).obj.hom δ ≫ pullback.snd e t)
      (((baseChange h).obj G).obj.hom ≫ e) t :=
  (IsPullback.of_hasPullback ((baseChange h).obj G).obj.hom δ).paste_vert
    (IsPullback.of_hasPullback e t)

end AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization
