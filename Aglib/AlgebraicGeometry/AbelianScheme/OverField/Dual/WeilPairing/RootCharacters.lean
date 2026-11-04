/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.Dual.WeilPairing.Polarization
public import Aglib.AlgebraicGeometry.Group.CartierDuality.CharacterRoots

/-! The original root characters for a given principal isomorphism. -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory
open Scheme.OverField Scheme.Group

universe u

namespace AlgebraicGeometry.Scheme.RelativePicard

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k] (A : Grp (FScheme k))
  (P : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType P.obj.hom]
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙ (fppfPicardSheaf A.X.hom).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
  [IsHProjective A.X.hom] [GeometricallyIntegral A.X.hom] [Smooth A.X.hom]
  [IsSeparated P.obj.hom] [IsCommMonObj A.X]

variable (e : A ≅ Grp.mk (picardIdentityComponent A.X.hom P R))

/-- The positive original Cartier character of the given second kernel point. -/
abbrev multiplicationKernelRootCharacterOfPrincipalIso
    (n : ℕ) (hn : 0 < n) (T : FScheme k)
    (y : T ⟶ (MultiplicationKernel.kernelGroup A n).X) :=
  let G := MultiplicationKernel.kernelGroup A n
  letI : IsFinite G.X.hom := Multiplication.kernelGroup_isFinite_of_pos A n hn
  letI : IsCommMonObj G.X := Kernel.isCommMonObj_group (MultiplicationKernel.multiplicationHom A n)
  let t := y ≫ (principalIsoOnMultiplicationKernel A P R e n).hom.hom.hom
  CartierDuality.characterRoots G T (t ≫ (multiplicationKernelCartierHom A P R n hn).hom.hom)
    n (Kernel.multiplication_kernel_pow_eq_one A n)

/-- The original second kernel point gives all root characters of the same first kernel. -/
def multiplicationKernelRootCharacterEquivOfPrincipalIso (n : ℕ) (hn : 0 < n)
    (T : FScheme k) :
    (T ⟶ (MultiplicationKernel.kernelGroup A n).X) ≃
      ((Over.pullback T.hom).mapGrp.obj (MultiplicationKernel.kernelGroup A n) ⟶
        MultiplicativeGroup.rootsGroupScheme T.left n) := by
  let G := MultiplicationKernel.kernelGroup A n
  letI : IsFinite G.X.hom := Multiplication.kernelGroup_isFinite_of_pos A n hn
  letI : IsCommMonObj G.X := Kernel.isCommMonObj_group (MultiplicationKernel.multiplicationHom A n)
  let i := (Grp.forget (FScheme k)).mapIso
    (multiplicationKernelCartierIsoOfPrincipalIso A P R e n hn)
  let E := ((Iso.refl T).homCongr i).trans
    (CartierDuality.characterRootsEquiv G T n (Kernel.multiplication_kernel_pow_eq_one A n))
  let g := multiplicationKernelRootCharacterOfPrincipalIso A P R e n hn T
  have h : (fun y => E y) = g := by
    funext y
    let j := (principalIsoOnMultiplicationKernel A P R e n).hom.hom.hom
    let k₀ := (multiplicationKernelCartierIso A P R n hn).hom.hom.hom
    let k₁ := (multiplicationKernelCartierHom A P R n hn).hom.hom
    let H := fun z => CartierDuality.characterRoots G T z n
      (Kernel.multiplication_kernel_pow_eq_one A n)
    have hk : k₀ = k₁ :=
      congrArg (fun f => f.hom.hom) (multiplicationKernelCartierIso_hom A P R n hn)
    have hp : y ≫ j ≫ k₀ = (y ≫ j) ≫ k₁ :=
      (Category.assoc y j k₀).symm.trans (congrArg (fun z => (y ≫ j) ≫ z) hk)
    change H ((𝟙 T) ≫ y ≫ j ≫ k₀) = H ((y ≫ j) ≫ k₁)
    exact congrArg H ((Category.id_comp _).trans hp)
  refine Equiv.ofBijective g ?_
  rw [← h]
  exact E.bijective

/-- The equivalence evaluates the same positive character. -/
theorem multiplicationKernelRootCharacterEquivOfPrincipalIso_apply
    (n : ℕ) (hn : 0 < n) (T : FScheme k)
    (y : T ⟶ (MultiplicationKernel.kernelGroup A n).X) :
    multiplicationKernelRootCharacterEquivOfPrincipalIso A P R e n hn T y =
      multiplicationKernelRootCharacterOfPrincipalIso A P R e n hn T y := rfl

end AlgebraicGeometry.Scheme.RelativePicard
