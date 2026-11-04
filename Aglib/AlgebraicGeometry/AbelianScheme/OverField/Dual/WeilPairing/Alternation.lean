/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.Dual.WeilPairing.AlternatingCharacter
public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.Dual.WeilPairing.Character
public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.Dual.WeilPairing.Polarization
public import Aglib.AlgebraicGeometry.Group.CartierDuality.EvaluationPoint

/-! Alternation of the original Weil pairing along the map of an original line bundle. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open Scheme.OverField Scheme.Group Scheme.Modules.Invertible
open CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Scheme.RelativePicard

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k] (A : Grp (FScheme k))
  (P : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType P.obj.hom]
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙ (fppfPicardSheaf A.X.hom).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
  [IsHProjective A.X.hom] [GeometricallyIntegral A.X.hom] [Smooth A.X.hom]
  [IsSeparated P.obj.hom] [IsCommMonObj A.X]

private theorem lift_evaluation_of_eq
    {C : Type*} [Category C] [CartesianMonoidalCategory C]
    {U G H D Z : C} (x : U ⟶ G) (t : U ⟶ H) (f : H ⟶ D)
    (v : G ⊗ H ⟶ Z) (e : G ⊗ D ⟶ Z) (h : v = (𝟙 G ⊗ₘ f) ≫ e) :
    lift x t ≫ v = lift x (t ≫ f) ≫ e := by
  have hLift : lift x t ≫ (𝟙 G ⊗ₘ f) = lift x (t ≫ f) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  rw [h, ← Category.assoc, hLift]

/-- Evaluation of the original root factor at an original pair of test
points is Cartier evaluation at the original normalized character. -/
theorem weilPairingMorphism_comp_inclusion_lift
    (n : ℕ) (hn : 0 < n) {T : FScheme k}
    (x : T ⟶ (MultiplicationKernel.kernelGroup A n).X)
    (t : T ⟶ (dualMultiplicationKernel A P R n).X) :
    let G := MultiplicationKernel.kernelGroup A n
    let fin := Multiplication.kernelGroup_isFinite_of_pos A n hn
    let comm := Kernel.isCommMonObj_group (MultiplicationKernel.multiplicationHom A n)
    (lift x t ≫ weilPairingMorphism A P R n hn) ≫
        MultiplicativeGroup.rootsInclusion (Base k) n =
      lift x (t ≫ (multiplicationKernelCartierHom A P R n hn).hom.hom) ≫
        @CartierDuality.evaluation k _ G fin comm := by
  let G := MultiplicationKernel.kernelGroup A n
  let H := dualMultiplicationKernel A P R n
  let fin := Multiplication.kernelGroup_isFinite_of_pos A n hn
  let comm := Kernel.isCommMonObj_group (MultiplicationKernel.multiplicationHom A n)
  let D := (@CartierDuality.dualGroup k _ G fin comm).X
  let Z := MultiplicativeGroup.scheme (Base k)
  let f : H.X ⟶ D := (multiplicationKernelCartierHom A P R n hn).hom.hom
  let e : G.X ⊗ D ⟶ Z := @CartierDuality.evaluation k _ G fin comm
  let v : G.X ⊗ H.X ⟶ Z := weilPairingEvaluation A P R n hn
  have h0 := weilPairingEvaluation_eq A P R n hn
  have h : v = (𝟙 G.X ⊗ₘ f) ≫ e := by
    unfold v f e
    with_reducible exact h0
  have hInc := weilPairingMorphism_comp_inclusion A P R n hn
  have hLift := @lift_evaluation_of_eq (FScheme k) _ _ T G.X H.X D Z x t f v e h
  calc
    _ = lift x t ≫ (weilPairingMorphism A P R n hn ≫
        MultiplicativeGroup.rootsInclusion (Base k) n) := Category.assoc _ _ _
    _ = lift x t ≫ v := by
      unfold v
      with_reducible exact congrArg (fun a : G.X ⊗ H.X ⟶ Z => lift x t ≫ a) hInc
    _ = _ := by
      unfold f e at hLift
      with_reducible exact hLift

private theorem character_units_congr {S : Scheme.{u}} {H : Grp (Over S)}
    {c d : H ⟶ MultiplicativeGroup.groupScheme S} (h : c = d) :
    MultiplicativeGroup.sectionsUnitsEquiv S H.X c.hom.hom =
      MultiplicativeGroup.sectionsUnitsEquiv S H.X d.hom.hom := by
  cases h
  rfl

variable (L : LineBundle A.X.left)

/-- The actual line-bundle map restricted to the original positive kernels. -/
def lineBundleClassMultiplicationKernelHom (n : ℕ) :
    MultiplicationKernel.kernelGroup A n ⟶ dualMultiplicationKernel A P R n := by
  let := picardCommGrpObj A.X.hom P R
  let D := picardIdentityComponent A.X.hom P R
  let : IsCommMonObj D := inferInstanceAs (IsCommMonObj (Group.identityComponentOver P.obj))
  exact MultiplicationKernel.map
    (lineBundleClassIdentityComponentGroupHom A.X P R (classOf A.X.left L)) n

/-- The original root-valued Weil pairing along the original line-bundle
map is alternating on the whole original multiplication kernel. -/
theorem weilPairingMorphism_lineBundleClass_diagonal (n : ℕ) (hn : 0 < n) :
    let G := MultiplicationKernel.kernelGroup A n
    MultiplicativeGroup.rootsHomEquiv (Base k) n G.X
      (lift (𝟙 G.X) (lineBundleClassMultiplicationKernelHom A P R L n).hom.hom ≫
        weilPairingMorphism A P R n hn) = 1 := by
  let q := MultiplicationKernel.multiplicationHom A n
  let G := MultiplicationKernel.kernelGroup A n
  let : IsFinite q.hom.hom.left :=
    (Multiplication.multiplicationHom_finite_flat_surjective A n hn).1
  let fin : IsFinite G.X.hom := Multiplication.kernelGroup_isFinite_of_pos A n hn
  let comm : IsCommMonObj G.X := Kernel.isCommMonObj_group q
  let : IsFinite G.X.hom := fin
  let : IsCommMonObj G.X := comm
  let T := G.X
  let t := (lineBundleClassMultiplicationKernelHom A P R L n).hom.hom
  let j := (dualMultiplicationKernelInclusion A P R n).hom.hom
  let δ := (multiplicationKernelCartierHom A P R n hn).hom.hom
  let d := t ≫ δ
  let i := (Kernel.inclusion q).hom.hom
  let φ := lineBundleClassMorphismIdentityComponent A.X P R (classOf A.X.left L)
  let v := lift (𝟙 T) t ≫ weilPairingMorphism A P R n hn
  have hv := weilPairingMorphism_comp_inclusion_lift A P R n hn (T := T) (𝟙 T) t
  have hvalue : v ≫ MultiplicativeGroup.rootsInclusion (Base k) n =
      lift (𝟙 T) d ≫ @CartierDuality.evaluation k _ G fin comm := by
    unfold v d δ
    with_reducible exact hv
  have hj : t ≫ j = i ≫ φ := by
    let := picardCommGrpObj A.X.hom P R
    let D := picardIdentityComponent A.X.hom P R
    let : IsCommMonObj D := inferInstanceAs (IsCommMonObj (Group.identityComponentOver P.obj))
    let f := lineBundleClassIdentityComponentGroupHom A.X P R (classOf A.X.left L)
    exact congrArg (fun z : G ⟶ Grp.mk D => z.hom.hom) (MultiplicationKernel.map_inclusion f n)
  let z := polarizedKernel_comp_dualPullback A P R L n
  have hz : (t ≫ j) ≫ picardIdentityComponentPullback P R P R q.hom.hom = 1 := by
    rw [hj]
    exact z
  let B := (poincarePullback A.X P R (i ≫ φ)).bundle
  let a := poincareKernelFrame A A P R P R q (i ≫ φ) z
  have hc : CartierDuality.characterEquiv G T d =
      kernelTrivializationCharacter q (Kernel.marking q) T B a := by
    have h := characterEquiv_comp_multiplicationKernelCartierHom A P R n hn t
    have he (p r : T ⟶ picardIdentityComponent A.X.hom P R)
        (hp : p ≫ picardIdentityComponentPullback P R P R q.hom.hom = 1)
        (hr : r ≫ picardIdentityComponentPullback P R P R q.hom.hom = 1)
        (e : p = r) :
        poincareKernelCharacter A A P R P R q p hp =
          poincareKernelCharacter A A P R P R q r hr := by
      cases e
      rfl
    exact h.trans (he _ _ hz z hj)
  let F := MultiplicativeBaseChange.baseChangedGroup T.hom (Kernel.group q)
  let U := MultiplicativeGroup.sectionsUnitsEquiv T.left F.X
  let e := Units.map (lift (𝟙 T) (𝟙 T)).left.appTop.hom.toMonoidHom
  let χ : F ⟶ MultiplicativeGroup.groupScheme T.left := CartierDuality.characterEquiv G T d
  let χ' : F ⟶ MultiplicativeGroup.groupScheme T.left :=
    kernelTrivializationCharacter q (Kernel.marking q) T B a
  have hU₁ : U χ.hom.hom = U χ'.hom.hom := by
    have h : χ = χ' := hc
    exact character_units_congr h
  have hU₂ : U χ'.hom.hom = kernelMultiplier q (Kernel.marking q) T B a := by
    unfold U F χ'
    with_reducible
      exact sectionsUnitsEquiv_kernelTrivializationCharacter q (Kernel.marking q) T B a
  apply Subtype.ext
  change MultiplicativeGroup.sectionsUnitsEquiv (Base k) T
      (v ≫ MultiplicativeGroup.rootsInclusion (Base k) n) = 1
  calc
    _ = MultiplicativeGroup.sectionsUnitsEquiv (Base k) T
          (lift (𝟙 T) d ≫ @CartierDuality.evaluation k _ G fin comm) :=
      congrArg (MultiplicativeGroup.sectionsUnitsEquiv (Base k) T) hvalue
    _ = e (U χ.hom.hom) := by
      unfold e U χ F
      with_reducible exact CartierDuality.evaluation_units_eq_character_on_section G T (𝟙 T) d
    _ = e (U χ'.hom.hom) := congrArg e hU₁
    _ = e (kernelMultiplier q (Kernel.marking q) T B a) := congrArg e hU₂
    _ = _ := poincareKernelMultiplier_polarized_diagonal A P R L n

/-- A principal isomorphism induced by an actual line bundle gives an
alternating pairing on the original positive multiplication kernel. -/
theorem weilPairingMorphismOfPrincipalIso_diagonal_of_lineBundleClass
    (e : A ≅ Grp.mk (picardIdentityComponent A.X.hom P R))
    (he : e.hom = lineBundleClassIdentityComponentGroupHom A.X P R (classOf A.X.left L))
    (n : ℕ) (hn : 0 < n) :
    let T := (MultiplicationKernel.kernelGroup A n).X
    MultiplicativeGroup.rootsHomEquiv (Base k) n T
      (lift (𝟙 T) (𝟙 T) ≫ weilPairingMorphismOfPrincipalIso A P R e n hn) = 1 := by
  let T := (MultiplicationKernel.kernelGroup A n).X
  let u := (principalIsoOnMultiplicationKernel A P R e n).hom.hom.hom
  let v := (lineBundleClassMultiplicationKernelHom A P R L n).hom.hom
  have hu : u = v := by
    let := picardCommGrpObj A.X.hom P R
    let D := picardIdentityComponent A.X.hom P R
    let : IsCommMonObj D := inferInstanceAs (IsCommMonObj (Group.identityComponentOver P.obj))
    have h := (MultiplicationKernel.mapIso_hom e n).trans
      (congrArg (fun g => MultiplicationKernel.map g n) he)
    exact congrArg (fun g => g.hom.hom) h
  have hLift : lift (𝟙 T) (𝟙 T) ≫ (𝟙 T ⊗ₘ u) = lift (𝟙 T) u := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  have hPair : lift (𝟙 T) (𝟙 T) ≫ weilPairingMorphismOfPrincipalIso A P R e n hn =
      lift (𝟙 T) v ≫ weilPairingMorphism A P R n hn := by
    unfold weilPairingMorphismOfPrincipalIso
    change lift (𝟙 T) (𝟙 T) ≫ (𝟙 T ⊗ₘ u) ≫ weilPairingMorphism A P R n hn =
      lift (𝟙 T) v ≫ weilPairingMorphism A P R n hn
    rw [← Category.assoc, hLift, hu]
  exact (congrArg (MultiplicativeGroup.rootsHomEquiv (Base k) n T) hPair).trans
    (weilPairingMorphism_lineBundleClass_diagonal A P R L n hn)

end AlgebraicGeometry.Scheme.RelativePicard
