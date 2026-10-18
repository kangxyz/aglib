/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.AlgebraicGeometry.RelativeGluing
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.BaseChange

/-! Glue actual finite-etale schemes along an equifibered open-cover diagram. -/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (baseChange mk)

namespace AlgebraicGeometry.Scheme.FiniteEtale.RelativeGluing

universe u
variable {X : Scheme.{u}} {𝒰 : X.OpenCover}
variable [Category 𝒰.I₀] [𝒰.LocallyDirected] [Small.{u} 𝒰.I₀] [Quiver.IsThin 𝒰.I₀]
variable (D : Scheme.Cover.RelativeGluingData 𝒰)

/-- A property local on the base passes from the local pieces to the actual
glued structural morphism. -/
theorem property_toBase (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P]
    (hP : ∀ i, P (D.natTrans.app i)) : P D.toBase := by
  apply IsZariskiLocalAtTarget.of_openCover 𝒰
  intro i
  change P (pullback.snd D.toBase (𝒰.f i))
  apply (MorphismProperty.cancel_left_of_respectsIso P
    (D.isPullback_natTrans_ι_toBase i).flip.isoPullback.hom _).1
  simpa using hP i

variable [∀ i, IsFinite (D.natTrans.app i)] [∀ i, Etale (D.natTrans.app i)]

/-- The global output is the actual scheme supplied by relative gluing. -/
def gluedCover : Scheme.FiniteEtale X :=
  ⟨Over.mk D.toBase,
    property_toBase D @IsFinite (fun _ => inferInstance),
    property_toBase D @Etale (fun _ => inferInstance)⟩

/-- The local finite étale cover over `𝒰.X i` whose structure map is `D.natTrans.app i`. -/
def localCover (i : 𝒰.I₀) : Scheme.FiniteEtale (𝒰.X i) :=
  mk (D.natTrans.app i)

/-- The global cover has the prescribed local pieces, in the actual cover
category over each open chart. -/
def localCoverIso (i : 𝒰.I₀) :
    (baseChange (𝒰.f i)).obj (gluedCover D) ≅ localCover D i :=
  ObjectProperty.isoMk _ (Over.isoMk (D.isPullback_natTrans_ι_toBase i).flip.isoPullback.symm
    (by
      change (D.isPullback_natTrans_ι_toBase i).flip.isoPullback.inv ≫ D.natTrans.app i =
        pullback.snd D.toBase (𝒰.f i)
      apply (Iso.inv_comp_eq _).2
      exact (D.isPullback_natTrans_ι_toBase i).flip.isoPullback_hom_snd.symm))

end AlgebraicGeometry.Scheme.FiniteEtale.RelativeGluing

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 b0d7e7b437785b16db518fd2fef5319ba417027cbb0905823fb5d92b8734b1c4.
Definitions, hypotheses and universes are retained modulo native names. -/
