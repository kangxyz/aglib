/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Tangent.Cech.Scaling

/-! Focused consumer of the Čech tangent kernel of the Picard functor (Kleiman,
arXiv:math/0504020v1, proof of Thm 5.11, p. 43; Stacks, Tag 0B8R): units `1 + ε b`, the class
map from pair cocycles, its kernel and range, `ker(Pic X[ε] → Pic X) ≃+ H^1(X, 𝒪_X)` on an affine
cover of a separated scheme over a field, and linearity under `ε ↦ a ε`. -/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.SplitThickening
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.Modules.Invertible.PullbackTensor.Local

universe u

section Thickening

variable {X Y : Scheme.{u}} {i : X ⟶ Y} {p : Y ⟶ X} {h : i ≫ p = 𝟙 X}
  (G : IdealGenerator i p h) {ι : Type u} (U : ι → X.Opens) (hU : iSup U = ⊤)
  (hU₁ : ∀ j, IsAffineOpen (U j)) (hV₁ : ∀ j, IsAffineOpen (p ⁻¹ᵁ U j))
  (hU₂ : ∀ j l, IsAffineOpen (U j ⊓ U l))

example (W : X.Opens) (hW : IsAffineOpen W) (g : (Γ(Y, p ⁻¹ᵁ W))ˣ) :
    Units.map ((reduction i p h).hom.app (Opposite.op W)).hom.toMonoidHom g = 1 ↔
      ∃ b : Γ(X, W), G.oneAdd W b = g :=
  G.units_reduction_eq_one_iff W hW g

example (W : X.Opens) (a b : Γ(X, W)) : G.oneAdd W (a + b) = G.oneAdd W a * G.oneAdd W b :=
  G.oneAdd_add W a b

example (b : pairCocycles U) : pullbackHom i (G.cocycleClass U hU b) = 0 :=
  G.pullbackHom_cocycleClass U hU b

example (b : pairCocycles U) : G.cocycleClass U hU b = 0 ↔ b ∈ pairCoboundaries U :=
  G.cocycleClass_eq_zero_iff U hU hU₁ b

example (c : PicardGroup Y) (hc : pullbackHom i c = 0) :
    ∃ b : pairCocycles U, G.cocycleClass U hU b = c :=
  G.exists_cocycleClass_eq U hU₁ hV₁ hU hU₂ c hc

example : PairCohomology U ≃+ (pullbackHom i).ker :=
  G.pairCohomologyEquivKer U hU hU₁ hV₁ hU₂

end Thickening

section DualNumbers

variable {k : Type u} [Field k] (X : FScheme k) [X.left.IsSeparated] {ι : Type u}
  (U : ι → X.left.Opens) (hU : iSup U = ⊤) (hU₁ : ∀ j, IsAffineOpen (U j))

/-- The tangent kernel has the type of the conditional `DualNumbers.picardKerEquiv`. -/
example : (pullbackHom (DualNumbers.inclusion k X.hom)).ker ≃+
    Sheaf.H (Scheme.structureAddSheaf X.left) 1 :=
  DualNumbers.picardKerEquivCech X U hU hU₁

example (a : k) (c : (pullbackHom (DualNumbers.inclusion k X.hom)).ker) :
    DualNumbers.picardKerEquivCech X U hU hU₁ (DualNumbers.dualScaleKer k X.hom a c) =
      a • DualNumbers.picardKerEquivCech X U hU hU₁ c :=
  DualNumbers.picardKerEquivCech_dualScale X U hU hU₁ a c

example (a : k) : DualNumbers.inclusion k X.hom ≫ DualNumbers.dualScale k X.hom a =
    DualNumbers.inclusion k X.hom :=
  DualNumbers.inclusion_dualScale k X.hom a

example (b : pairCocycles U) :
    DualNumbers.picardKerEquivCech X U hU hU₁
        ⟨(DualNumbers.dualIdealGenerator k X.hom).cocycleClass U hU b, AddMonoidHom.mem_ker.mpr
          ((DualNumbers.dualIdealGenerator k X.hom).pullbackHom_cocycleClass U hU b)⟩ =
      Cohomology.structureCechCohomologyLinearEquiv X U hU
        (Cohomology.isAffineOpen_cechTuple U hU₁) (injectiveResolution _) 0
        (Cohomology.pairCohomologyEquivCech X U (QuotientAddGroup.mk b)) :=
  DualNumbers.picardKerEquivCech_cocycleClass X U hU hU₁ b

end DualNumbers

/--
info: 'AlgebraicGeometry.Scheme.SplitThickening.IdealGenerator.pairCohomologyEquivKer' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms IdealGenerator.pairCohomologyEquivKer

/--
info: 'AlgebraicGeometry.Scheme.SplitThickening.IdealGenerator.exists_cocycleClass_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms IdealGenerator.exists_cocycleClass_eq

/--
info: 'AlgebraicGeometry.Scheme.DualNumbers.picardKerEquivCech' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms DualNumbers.picardKerEquivCech

/--
info: 'AlgebraicGeometry.Scheme.DualNumbers.picardKerEquivCech_dualScale' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms DualNumbers.picardKerEquivCech_dualScale
