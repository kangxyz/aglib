/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.FiniteTrivialization
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.GaloisInstances
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.HenselianConstant
public import Aglib.AlgebraicGeometry.EtaleCohomology.H0.ConnectedConstantValues

/-! # A finite étale cyclic trivialization of the original roots coefficient

The original roots group supplies a pointed finite splitting cover. Its finite
constant value is identified at that same point, using the two actual constant
adjunction units over the algebraically closed residue field. The coordinate
need not be canonical; no global primitive root on the original base is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme.EtaleCohomology
open AlgebraicGeometry.Scheme.Group
open GroupCohomology.Kummer.Coefficients
open GroupCohomology.Kummer.CoefficientBaseChange

universe u

namespace GroupCohomology.Kummer

attribute [local instance] hasSheafifyLarge Over.cartesianMonoidalCategory

/-- Positive invertible roots become the actual finite cyclic constant
coefficient on one finite étale surjective cover of an integral scheme. -/
theorem exists_finiteEtale_cyclic_trivialization
    (X : Scheme.{u}) [IsIntegral X] (n : ℕ) (hn : 0 < n)
    (hinv : IsUnit (n : Γ(X, ⊤))) :
    ∃ T : Scheme.FiniteEtale X, Surjective T.obj.hom ∧
      Nonempty ((inverseImage T.obj.hom).obj (mu X n) ≅
        ConstantFinite.coefficient (ULift.{u} (ZMod n)) T.obj.left) := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let Ω := AlgebraicClosure (X.residueField (genericPoint X))
  let s : Spec (.of Ω) ⟶ X :=
    Scheme.FiniteEtale.algebraicClosureResiduePoint X (genericPoint X)
  let H := MultiplicativeGroup.rootsGroupScheme X n
  let : IsFinite H.X.hom := RootsFiniteEtale.rootsScheme_finite X n hn
  let : Etale H.X.hom := RootsFiniteEtale.rootsScheme_etale X n hn hinv
  let T := finiteSplittingCover s H
  let η : Spec (.of Ω) ⟶ T.cover.obj.left := T.point.left
  let G : AddCommGrpCat.{u + 1} := T.localValue
  let V : AddCommGrpCat.{u + 1} := ConstantFinite.value (ULift.{u} (ZMod n))
  let eT : mu T.cover.obj.left n ≅
      (constantSheaf (Scheme.smallEtaleTopology T.cover.obj.left)
        AddCommGrpCat.{u + 1}).obj G :=
    (rootsPullbackIso T.cover.obj.hom n hn hinv).symm ≪≫ T.localTrivializationIso
  have hT : IsUnit (n : Γ(T.cover.obj.left, ⊤)) :=
    levelInvertible T.cover.obj.hom n hinv
  have hΩ : IsUnit (n : Γ(Spec (.of Ω), ⊤)) := levelInvertible η n hT
  let : IsAlgClosed (IsLocalRing.ResidueField Ω) := IsAlgClosed.of_ringEquiv Ω _
    (RingEquiv.ofBijective (IsLocalRing.residue Ω)
      ⟨(IsLocalRing.residue Ω).injective, IsLocalRing.residue_surjective⟩)
  let E :
      (constantSheaf (Scheme.smallEtaleTopology (Spec (.of Ω)))
        AddCommGrpCat.{u + 1}).obj G ≅
      (constantSheaf (Scheme.smallEtaleTopology (Spec (.of Ω)))
        AddCommGrpCat.{u + 1}).obj V :=
    ((inverseImageConstantIso η).app G).symm ≪≫
      (inverseImage η).mapIso eT.symm ≪≫ rootsPullbackIso η n hn hT ≪≫
      (AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.HenselianConstant.constantRootIso
        Ω n hn hΩ).symm
  let : IsIso ((constantAdjunction (Spec (.of Ω))).unit.app G) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (ConstantFinite.constantUnit_bijective_value_of_connected (Spec (.of Ω)) G)
  let : IsIso ((constantAdjunction (Spec (.of Ω))).unit.app V) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (ConstantFinite.constantUnit_bijective_value_of_connected (Spec (.of Ω)) V)
  let eG : G ≅ V :=
    asIso ((constantAdjunction (Spec (.of Ω))).unit.app G) ≪≫
      (globalSections (Spec (.of Ω))).mapIso E ≪≫
      (asIso ((constantAdjunction (Spec (.of Ω))).unit.app V)).symm
  refine ⟨T.cover, ⟨T.surjective⟩, ⟨?_⟩⟩
  exact T.localTrivializationIso ≪≫
    (constantSheaf (Scheme.smallEtaleTopology T.cover.obj.left)
      AddCommGrpCat.{u + 1}).mapIso eG

end GroupCohomology.Kummer
