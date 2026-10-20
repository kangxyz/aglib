/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.MultiplicationCone.Quotient
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.Algebra.Homology.QuasiIso

/-!
# Conditional homology transport from actual quasi-isomorphisms

The supplied native QuasiIso/QuasiIsoAt hypotheses yield bijectivity for the
original four-term homology maps. The full-chain truncation and all maps remain explicit.

Source: `lean/R5Lab/Aglib/Algebra/Homology/MultiplicationCone/HomologyTransport.lean`.
Frozen R5 revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
SHA-256: `391924a2a504d9f399e4362a76e96c8677ded7c3adb837ad335de6a2faa5baf7`.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace AddCommGrpCat.MultiplicationCone.HomologyTransport
open AddCommGrpCat.MultiplicationCone
universe u

section Generic
variable {A₀ A₁ A₂ A₃ B₀ B₁ B₂ B₃ : Type u}
  [AddCommGroup A₀] [AddCommGroup A₁] [AddCommGroup A₂] [AddCommGroup A₃]
  [AddCommGroup B₀] [AddCommGroup B₁] [AddCommGroup B₂] [AddCommGroup B₃]
  (C : AddCommGrpCat.MultiplicationCone.Complex A₀ A₁ A₂ A₃)
  (D : AddCommGrpCat.MultiplicationCone.Complex B₀ B₁ B₂ B₃)

/-- The short complex `A₀ → A₁ → A₂` extracted from the four-term complex. -/
def short1 : ShortComplex AddCommGrpCat :=
  ShortComplex.mk (AddCommGrpCat.ofHom C.d₀) (AddCommGrpCat.ofHom C.d₁)
    (by ext x; exact C.d₁_d₀ x)

/-- The short complex `A₁ → A₂ → A₃` extracted from the four-term complex. -/
def short2 : ShortComplex AddCommGrpCat :=
  ShortComplex.mk (AddCommGrpCat.ofHom C.d₁) (AddCommGrpCat.ofHom C.d₂)
    (by ext x; exact C.d₂_d₁ x)

variable {C D} (f : AddCommGrpCat.MultiplicationCone.ChainMap C D)

/-- The map between the first short complexes induced by a chain map. -/
def shortMap1 : short1 C ⟶ short1 D where
  τ₁ := AddCommGrpCat.ofHom f.f₀
  τ₂ := AddCommGrpCat.ofHom f.f₁
  τ₃ := AddCommGrpCat.ofHom f.f₂
  comm₁₂ := by ext x; exact (f.comm₀ x).symm
  comm₂₃ := by ext x; exact (f.comm₁ x).symm

/-- The map between the second short complexes induced by a chain map. -/
def shortMap2 : short2 C ⟶ short2 D where
  τ₁ := AddCommGrpCat.ofHom f.f₁
  τ₂ := AddCommGrpCat.ofHom f.f₂
  τ₃ := AddCommGrpCat.ofHom f.f₃
  comm₁₂ := by ext x; exact (f.comm₁ x).symm
  comm₂₃ := by ext x; exact (f.comm₂ x).symm

/-- Left homology map data for the first short complex, using the explicit cycle and quotient
maps. -/
def homologyData1 : ShortComplex.LeftHomologyMapData (shortMap1 f)
    (short1 C).abLeftHomologyData (short1 D).abLeftHomologyData where
  φK := AddCommGrpCat.ofHom f.onCycles₁
  φH := AddCommGrpCat.ofHom f.onH₁
  commi := by ext x; rfl
  commf' := by ext x; apply Subtype.ext; exact f.comm₀ x
  commπ := by ext x; rfl

/-- Left homology map data for the second short complex, using the explicit cycle and quotient
maps. -/
def homologyData2 : ShortComplex.LeftHomologyMapData (shortMap2 f)
    (short2 C).abLeftHomologyData (short2 D).abLeftHomologyData where
  φK := AddCommGrpCat.ofHom f.onCycles₂
  φH := AddCommGrpCat.ofHom f.onH₂
  commi := by ext x; rfl
  commf' := by ext x; apply Subtype.ext; exact f.comm₁ x
  commπ := by ext x; rfl

theorem onH1_bijective [ShortComplex.QuasiIso (shortMap1 f)] :
    Function.Bijective f.onH₁ := by
  have : IsIso (homologyData1 f).φH :=
    (homologyData1 f).quasiIso_iff.mp inferInstance
  exact (asIso (homologyData1 f).φH).addCommGroupIsoToAddEquiv.bijective

theorem onH2_bijective [ShortComplex.QuasiIso (shortMap2 f)] :
    Function.Bijective f.onH₂ := by
  have : IsIso (homologyData2 f).φH :=
    (homologyData2 f).quasiIso_iff.mp inferInstance
  exact (asIso (homologyData2 f).φH).addCommGroupIsoToAddEquiv.bijective
end Generic

section FullChain
variable (C D : ChainComplex AddCommGrpCat.{u} ℕ)

/-- The four-term complex formed from chain degrees `2`, `1`, `0`, and the zero differential at
`0`. -/
def chainLow : AddCommGrpCat.MultiplicationCone.Complex (C.X 2) (C.X 1) (C.X 0) (C.X 0) where
  d₀ := (C.d 2 1).hom
  d₁ := (C.d 1 0).hom
  d₂ := (C.d 0 0).hom
  d₁_d₀ x := by
    have h := CategoryTheory.congr_fun (C.d_comp_d 2 1 0) x
    exact h
  d₂_d₁ x := by
    have h := CategoryTheory.congr_fun (C.d_comp_d 1 0 0) x
    exact h

variable {C D} (f : C ⟶ D)

/-- The four-term chain map obtained from a chain-complex morphism in degrees `2`, `1`, and `0`. -/
def chainLowMap : AddCommGrpCat.MultiplicationCone.ChainMap (chainLow C) (chainLow D) where
  f₀ := (f.f 2).hom
  f₁ := (f.f 1).hom
  f₂ := (f.f 0).hom
  f₃ := (f.f 0).hom
  comm₀ x := (CategoryTheory.congr_fun (f.comm 2 1) x).symm
  comm₁ x := (CategoryTheory.congr_fun (f.comm 1 0) x).symm
  comm₂ x := (CategoryTheory.congr_fun (f.comm 0 0) x).symm

theorem chainLow_onH1_bijective [QuasiIsoAt f 1] :
    Function.Bijective (chainLowMap f).onH₁ := by
  have : ShortComplex.QuasiIso (shortMap1 (chainLowMap f)) := by
    exact (quasiIsoAt_iff' f 2 1 0 (by simp) (by simp)).mp inferInstance
  exact onH1_bijective (chainLowMap f)

theorem chainLow_onH2_bijective [QuasiIsoAt f 0] :
    Function.Bijective (chainLowMap f).onH₂ := by
  have : ShortComplex.QuasiIso (shortMap2 (chainLowMap f)) := by
    exact (ChainComplex.quasiIsoAt₀_iff f).mp inferInstance
  exact onH2_bijective (chainLowMap f)
end FullChain

end AddCommGrpCat.MultiplicationCone.HomologyTransport
