/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.Dual.WeilPairing
public import Aglib.AlgebraicGeometry.Group.MultiplicationKernel.Functoriality

/-! Transport of the original Weil pairing along a given principal isomorphism. -/

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

/-- The given principal isomorphism restricted to the original multiplication kernels. -/
def principalIsoOnMultiplicationKernel (n : ℕ) :
    MultiplicationKernel.kernelGroup A n ≅ dualMultiplicationKernel A P R n := by
  let := picardCommGrpObj A.X.hom P R
  let D := picardIdentityComponent A.X.hom P R
  let : IsCommMonObj D := inferInstanceAs (IsCommMonObj (Group.identityComponentOver P.obj))
  exact MultiplicationKernel.mapIso e n

omit [IsHProjective A.X.hom] [GeometricallyIntegral A.X.hom] [Smooth A.X.hom]
  [IsSeparated P.obj.hom] in
/-- The restricted principal isomorphism retains the original two inclusions. -/
theorem principalIsoOnMultiplicationKernel_hom_inclusion (n : ℕ) :
    (principalIsoOnMultiplicationKernel A P R e n).hom ≫
        dualMultiplicationKernelInclusion A P R n =
      Kernel.inclusion (MultiplicationKernel.multiplicationHom A n) ≫ e.hom := by
  let := picardCommGrpObj A.X.hom P R
  let D := picardIdentityComponent A.X.hom P R
  let : IsCommMonObj D := inferInstanceAs (IsCommMonObj (Group.identityComponentOver P.obj))
  unfold principalIsoOnMultiplicationKernel
  rw [MultiplicationKernel.mapIso_hom]
  exact MultiplicationKernel.map_inclusion e.hom n

/-- Restrict the given principal isomorphism to the original kernels and
use the original Weil pairing. -/
def weilPairingMorphismOfPrincipalIso (n : ℕ) (hn : 0 < n) :
    (MultiplicationKernel.kernelGroup A n).X ⊗ (MultiplicationKernel.kernelGroup A n).X ⟶
      MultiplicativeGroup.rootsScheme (Base k) n :=
  let G := MultiplicationKernel.kernelGroup A n
  (𝟙 G.X ⊗ₘ (principalIsoOnMultiplicationKernel A P R e n).hom.hom.hom) ≫
    weilPairingMorphism A P R n hn

/-- The first Cartier adjoint is the composite of the two original isomorphisms. -/
def multiplicationKernelCartierIsoOfPrincipalIso (n : ℕ) (hn : 0 < n) :
    MultiplicationKernel.kernelGroup A n ≅ multiplicationKernelCartierDual A n hn :=
  principalIsoOnMultiplicationKernel A P R e n ≪≫ multiplicationKernelCartierIso A P R n hn

/-- The original evaluation after the same principal isomorphism. -/
def weilPairingEvaluationOfPrincipalIso (n : ℕ) (hn : 0 < n) :
    (MultiplicationKernel.kernelGroup A n).X ⊗ (MultiplicationKernel.kernelGroup A n).X ⟶
      MultiplicativeGroup.scheme (Base k) :=
  let G := MultiplicationKernel.kernelGroup A n
  (𝟙 G.X ⊗ₘ (principalIsoOnMultiplicationKernel A P R e n).hom.hom.hom) ≫
    weilPairingEvaluation A P R n hn

/-- The original evaluation is the composite with the original roots inclusion. -/
theorem weilPairingMorphismOfPrincipalIso_comp_inclusion (n : ℕ) (hn : 0 < n) :
    weilPairingMorphismOfPrincipalIso A P R e n hn ≫
        MultiplicativeGroup.rootsInclusion (Base k) n =
      weilPairingEvaluationOfPrincipalIso A P R e n hn := by
  unfold weilPairingMorphismOfPrincipalIso weilPairingEvaluationOfPrincipalIso
  let G := MultiplicationKernel.kernelGroup A n
  let a := 𝟙 G.X ⊗ₘ (principalIsoOnMultiplicationKernel A P R e n).hom.hom.hom
  exact (Category.assoc _ _ _).trans
    (congrArg (fun q => a ≫ q) (weilPairingMorphism_comp_inclusion A P R n hn))

end AlgebraicGeometry.Scheme.RelativePicard
