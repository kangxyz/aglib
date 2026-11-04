/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.WeilPairing
public import Aglib.AlgebraicGeometry.Group.MultiplicativeGroup.PairingSections
public import Aglib.AlgebraicGeometry.FundamentalGroup.Field.Basic

/-! Galois compatibility of the original canonical Jacobian Weil pairing. -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory
open Scheme.RelativePicard Scheme.Group CartesianMonoidalCategory
open Scheme.FiniteEtale.FieldGalois

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k] {X : FScheme k} (hX : Properties X)
  (P : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType P.obj.hom]
  [IsSeparated P.obj.hom]
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙ (fppfPicardSheaf X.hom).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
  (Q : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType Q.obj.hom]
  [IsSeparated Q.obj.hom]
  (RQ : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf (picardIdentityComponent X.hom P R).hom).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy Q)

/-- The original canonical Weil value on geometric points is equivariant for
the actual Galois automorphism of the chosen algebraic closure. -/
theorem jacobianWeilPairingMorphism_galois (n : ℕ) (hn : 0 < n)
    (σ : Field.absoluteGaloisGroup k) :
    letI := picardCommGrpObj X.hom P R
    let J := picardIdentityComponent X.hom P R
    let comm : IsCommMonObj J := inferInstanceAs (IsCommMonObj (Group.identityComponentOver P.obj))
    letI : IsCommMonObj J := comm
    let G := MultiplicationKernel.kernelGroup (Grp.mk J) n
    let T := Over.mk (geometricPoint k)
    let e := (Scheme.ΓSpecIso (.of (AlgebraicClosure k))).hom
    let v (x y : T ⟶ G.X) :=
      Units.map e.hom.toMonoidHom
        (MultiplicativeGroup.rootsHomEquiv (Base k) n T
          (lift x y ≫ jacobianWeilPairingMorphism hX P R Q RQ n hn)).val
    ∀ x y : T ⟶ G.X,
      v (pointEnd k σ ≫ x) (pointEnd k σ ≫ y) =
        Units.map (asAutomorphism k σ).toMonoidHom (v x y) := by
  intro J comm G T e v x y
  let p := jacobianWeilPairingMorphism hX P R Q RQ n hn
  let f := pointEnd k σ
  let a := (MultiplicativeGroup.rootsHomEquiv (Base k) n T (lift x y ≫ p)).val
  have h := MultiplicativeGroup.rootsValue_pair_naturality n p f x y
  have hs : f.left.appTop ≫ e = e ≫ CommRingCat.ofHom (asAutomorphism k σ).toRingHom := by
    unfold f
    rw [pointEnd_left]
    exact Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (asAutomorphism k σ).toRingHom)
  calc
    _ = Units.map e.hom.toMonoidHom (Units.map f.left.appTop.hom.toMonoidHom a) :=
      congrArg (Units.map e.hom.toMonoidHom) h
    _ = _ := by
      apply Units.ext
      change e (f.left.appTop a.val) = (asAutomorphism k σ) (e a.val)
      exact congrArg (fun m => m a.val) hs

end AlgebraicGeometry.Scheme.OverField.Curve
