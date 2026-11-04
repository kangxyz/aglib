/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.Theta.IntrinsicImage
public import Aglib.AlgebraicGeometry.Curves.PointDivisor.GraphBaseChange
public import Aglib.AlgebraicGeometry.Picard.BaseChangeRepresentableBy

/-! # Field base change of the positive ordered Abel morphism

The original ordered product and its original coordinates determine the comparison.
The graph class calculation uses the same positive family and Picard representative.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Scheme Scheme.Modules.Invertible Scheme.RelativePicard
open Scheme.Modules.Invertible.PullbackTensor.Local

open Scheme.Cohomology

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section Parameter

variable {S S' Y : Scheme.{u}} (p : Y ⟶ S) (b : S' ⟶ S)

private def parameterBaseChangeLift (n : ℕ) :
    (Over.map b).obj (parameter (pullback.snd p b) n) ⟶ parameter p n :=
  finiteProductOverLift (fun _ : Fin n => Over.mk p) (fun i =>
    ((Over.mapPullbackAdj b).homEquiv _ (Over.mk p)).symm
      (finiteProductOverπ (fun _ : Fin n => Over.mk (pullback.snd p b)) i))

private def parameterBaseChangeHom (n : ℕ) :
    parameter (pullback.snd p b) n ⟶ (Over.pullback b).obj (parameter p n) :=
  (Over.mapPullbackAdj b).homEquiv _ _ (parameterBaseChangeLift p b n)

private theorem parameterBaseChangeHom_π (n : ℕ) (i : Fin n) :
    parameterBaseChangeHom p b n ≫
        (Over.pullback b).map (finiteProductOverπ (fun _ : Fin n => Over.mk p) i) =
      finiteProductOverπ (fun _ : Fin n => Over.mk (pullback.snd p b)) i := by
  let adj := Over.mapPullbackAdj b
  apply (adj.homEquiv _ (Over.mk p)).symm.injective
  rw [adj.homEquiv_naturality_right_symm]
  change (adj.homEquiv _ _).symm
      (adj.homEquiv _ _ (parameterBaseChangeLift p b n)) ≫ _ = _
  rw [Equiv.symm_apply_apply]
  exact finiteProductOverLift_π _ _ i

private theorem pullbackParameter_hom_ext {n : ℕ} {T : Over S'}
    {f g : T ⟶ (Over.pullback b).obj (parameter p n)}
    (h : ∀ i, f ≫ (Over.pullback b).map
        (finiteProductOverπ (fun _ : Fin n => Over.mk p) i) =
      g ≫ (Over.pullback b).map (finiteProductOverπ (fun _ : Fin n => Over.mk p) i)) :
    f = g := by
  let adj := Over.mapPullbackAdj b
  apply (adj.homEquiv T (parameter p n)).symm.injective
  apply finiteProductOver_hom_ext (fun _ : Fin n => Over.mk p)
  intro i
  let π := finiteProductOverπ (fun _ : Fin n => Over.mk p) i
  rw [← adj.homEquiv_naturality_right_symm f π, ← adj.homEquiv_naturality_right_symm g π]
  exact congrArg (adj.homEquiv T (Over.mk p)).symm (h i)

/-- The canonical comparison between the original ordered parameter of the
base-changed family and the actual base change of the original ordered parameter. -/
@[no_expose]
def parameterBaseChangeIso (n : ℕ) :
    parameter (pullback.snd p b) n ≅ (Over.pullback b).obj (parameter p n) where
  hom := parameterBaseChangeHom p b n
  inv := finiteProductOverLift (fun _ : Fin n => Over.mk (pullback.snd p b))
    (fun i => (Over.pullback b).map (finiteProductOverπ (fun _ : Fin n => Over.mk p) i))
  hom_inv_id := by
    apply finiteProductOver_hom_ext (fun _ : Fin n => Over.mk (pullback.snd p b))
    intro i
    rw [Category.assoc, finiteProductOverLift_π, parameterBaseChangeHom_π, Category.id_comp]
  inv_hom_id := by
    apply pullbackParameter_hom_ext p b
    intro i
    rw [Category.assoc, parameterBaseChangeHom_π, finiteProductOverLift_π, Category.id_comp]

/-- The comparison commutes with every original coordinate projection. -/
@[reassoc (attr := simp)]
theorem parameterBaseChangeIso_hom_π (n : ℕ) (i : Fin n) :
    (parameterBaseChangeIso p b n).hom ≫
        (Over.pullback b).map (finiteProductOverπ (fun _ : Fin n => Over.mk p) i) =
      finiteProductOverπ (fun _ : Fin n => Over.mk (pullback.snd p b)) i :=
  parameterBaseChangeHom_π p b n i

/-- The inverse comparison recovers every pulled-back original coordinate. -/
@[reassoc (attr := simp)]
theorem parameterBaseChangeIso_inv_π (n : ℕ) (i : Fin n) :
    (parameterBaseChangeIso p b n).inv ≫
        finiteProductOverπ (fun _ : Fin n => Over.mk (pullback.snd p b)) i =
      (Over.pullback b).map (finiteProductOverπ (fun _ : Fin n => Over.mk p) i) :=
  finiteProductOverLift_π _ _ i

private theorem parameterBaseChangeIso_hom_adjoint (n : ℕ) :
    ((Over.mapPullbackAdj b).homEquiv (parameter (pullback.snd p b) n) (parameter p n)).symm
        (parameterBaseChangeIso p b n).hom =
      parameterBaseChangeLift p b n :=
  ((Over.mapPullbackAdj b).homEquiv _ _).symm_apply_apply _

end Parameter

section Field

variable {k : Type u} [Field k] {X : FScheme k} (hX : Properties X)
  (K : Type u) [Field K] [Algebra k K]

private theorem positiveFamilyClass_baseChange (n : ℕ) :
    let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
    let X' := fieldBaseChange K X
    let T := parameter X'.hom n
    letI := hX.smooth
    letI := hX.proper
    letI := (curveProperties_baseChange hX K b).smooth
    letI := (curveProperties_baseChange hX K b).proper
    pullbackClass (familyBaseChangeIso X.hom b T).hom
        (pullbackClass ((familyScheme X.hom).map (parameterBaseChangeLift X.hom b n))
          (classOf _ (positiveFamilyLineBundle X.hom n))) =
      classOf _ (positiveFamilyLineBundle X'.hom n) := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let X' := fieldBaseChange K X
  let T := parameter X'.hom n
  let T₀ := (Over.map b).obj T
  let d := parameterBaseChangeLift X.hom b n
  let := hX.smooth
  let := hX.proper
  let := (curveProperties_baseChange hX K b).smooth
  let := (curveProperties_baseChange hX K b).proper
  let s' (i : Fin n) : T ⟶ X' := finiteProductOverπ (fun _ : Fin n => Over.mk X'.hom) i
  let s (i : Fin n) : T₀ ⟶ Over.mk X.hom :=
    ((Over.mapPullbackAdj b).homEquiv T (Over.mk X.hom)).symm (s' i)
  have hd : d = (Over.homMk (parameterPoint X.hom T₀.hom (fun i => (s i).left)
      (fun i => (s i).w)) (parameterPoint_over X.hom T₀.hom (fun i => (s i).left)
        (fun i => (s i).w)) : T₀ ⟶ parameter X.hom n) := by
    apply finiteProductOver_hom_ext (fun _ : Fin n => Over.mk X.hom)
    intro i
    apply Over.OverMorphism.ext
    change (d ≫ finiteProductOverπ (fun _ : Fin n => Over.mk X.hom) i).left =
      parameterPoint X.hom T₀.hom (fun i => (s i).left) (fun i => (s i).w) ≫
        coordinate X.hom n i
    rw [parameterPoint_coordinate]
    change (finiteProductOverLift (fun _ : Fin n => Over.mk X.hom) s ≫
      finiteProductOverπ (fun _ : Fin n => Over.mk X.hom) i).left = (s i).left
    rw [finiteProductOverLift_π]
  have hclass : pullbackClass ((familyScheme X.hom).map d)
      (classOf _ (positiveFamilyLineBundle X.hom n)) =
    ∑ i : Fin n, classOf _ (Hom.positiveGraphLineBundle Hom.smoothRelativeDivisorIdeal
      X.hom T₀.hom (s i).left (s i).w) := by
    rw [familyScheme_map_eq_familyMap, hd]
    exact positiveFamilyLineBundle_class_at_tuple X.hom T₀.hom
      (fun i => (s i).left) (fun i => (s i).w)
  change pullbackClass (familyBaseChangeIso X.hom b T).hom
      (pullbackClass ((familyScheme X.hom).map d)
        (classOf _ (positiveFamilyLineBundle X.hom n))) =
    classOf _ (positiveFamilyLineBundle X'.hom n)
  rw [hclass, positiveFamilyLineBundle_class, ← PullbackTensor.Local.pullbackHom_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact positiveGraphClass_fieldBaseChange hX K T (s' i)

variable (P : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType P.obj.hom]
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf X.hom).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)

/-- The original positive ordered Abel morphism commutes with arbitrary field
extension on the actual ordered parameter and the actual Picard representative. -/
theorem positiveAbelMorphism_baseChange (n : ℕ) :
    let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
    let X' := fieldBaseChange K X
    letI := hX.smooth
    letI := hX.proper
    letI := (curveProperties_baseChange hX K b).smooth
    letI := (curveProperties_baseChange hX K b).proper
    (parameterBaseChangeIso X.hom b n).hom ≫
        (Over.pullback b).map (positiveAbelMorphism X P R n).hom =
      (positiveAbelMorphism X' (LocallyNoetherianOver.baseChange b P)
        (baseChangeRepresentableBy X.hom b P R) n).hom := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let X' := fieldBaseChange K X
  let := hX.smooth
  let := hX.proper
  let := (curveProperties_baseChange hX K b).smooth
  let := (curveProperties_baseChange hX K b).proper
  let T := locallyNoetherianParameter X' n
  let T₀ := (LocallyNoetherianOver.map b).obj T
  let P' := LocallyNoetherianOver.baseChange b P
  let R' := baseChangeRepresentableBy X.hom b P R
  let E := fppfPicardSheafBaseChangeIso X.hom b
  let d : T₀.obj ⟶ (locallyNoetherianParameter X n).obj :=
    parameterBaseChangeLift X.hom b n
  let f : T ⟶ P' := ObjectProperty.homMk
    ((parameterBaseChangeIso X.hom b n).hom ≫
      (Over.pullback b).map (positiveAbelMorphism X P R n).hom)
  let f' : T ⟶ P' := positiveAbelMorphism X' P' R' n
  let c : PicardGroup (pullback X.hom T₀.obj.hom) :=
    pullbackClass ((familyScheme X.hom).map d)
      (classOf _ (positiveFamilyLineBundle X.hom n))
  let c' : PicardGroup (pullback X'.hom T.obj.hom) :=
    classOf _ (positiveFamilyLineBundle X'.hom n)
  let q₀ : PicardGroup (pullback X.hom T₀.obj.hom) →+
      (fppfPicardSheaf X.hom).obj.obj (op T₀.obj) :=
    ((quotientProjection X.hom ≫ toFppfPicardSheaf X.hom).app (op T₀.obj)).hom
  let q₁ : PicardGroup (pullback X'.hom T.obj.hom) →+
      (fppfPicardSheaf X'.hom).obj.obj (op T.obj) :=
    ((quotientProjection X'.hom ≫ toFppfPicardSheaf X'.hom).app (op T.obj)).hom
  have hc : pullbackClass (familyBaseChangeIso X.hom b T.obj).hom c = c' :=
    positiveFamilyClass_baseChange hX K n
  have hc' : pullbackClass (familyBaseChangeIso X.hom b T.obj).inv c' = c := by
    rw [← hc, ← pullbackClass_comp, Iso.inv_hom_id, pullbackClass_id]
  have hleft : (E.hom.app (op T.obj)).hom (R'.homEquiv f) = q₀ c := by
    let adj := Over.mapPullbackAdj b
    have hd : (adj.homEquiv T.obj P.obj).symm f.hom =
        d ≫ (positiveAbelMorphism X P R n).hom := by
      change (adj.homEquiv T.obj P.obj).symm ((parameterBaseChangeIso X.hom b n).hom ≫
        (Over.pullback b).map (positiveAbelMorphism X P R n).hom) =
          d ≫ (positiveAbelMorphism X P R n).hom
      rw [adj.homEquiv_naturality_right_symm]
      have h : (adj.homEquiv T.obj (locallyNoetherianParameter X n).obj).symm
          (parameterBaseChangeIso X.hom b n).hom = d :=
        parameterBaseChangeIso_hom_adjoint X.hom b n
      exact congrArg (fun a : T₀.obj ⟶ (locallyNoetherianParameter X n).obj =>
        a ≫ (positiveAbelMorphism X P R n).hom) h
    have H := baseChangeRepresentableBy_homEquiv X.hom b P R (T := T) f
    change R'.homEquiv f = (E.inv.app (op T.obj)).hom
      (R.homEquiv (ObjectProperty.homMk ((adj.homEquiv T.obj P.obj).symm f.hom) :
        T₀ ⟶ P)) at H
    rw [hd] at H
    have hval : R.homEquiv (ObjectProperty.homMk
        (d ≫ (positiveAbelMorphism X P R n).hom) : T₀ ⟶ P) = q₀ c :=
      homEquiv_comp_positiveAbelMorphism X P R (ObjectProperty.homMk d)
    rw [H, hval]
    exact fppfPicardSheafBaseChangeIso_hom_app_inv_app_apply X.hom b (q₀ c)
  have hright : (E.hom.app (op T.obj)).hom (R'.homEquiv f') = q₀ c := by
    have hval : R'.homEquiv f' = q₁ c' := homEquiv_positiveAbelMorphism X' P' R' n
    rw [hval]
    have h := fppfPicardSheafBaseChangeIso_hom_app_toFppfPicardSheaf_mk
      X.hom b (op T.obj) c'
    change (E.hom.app (op T.obj)).hom (q₁ c') =
      q₀ (pullbackClass (familyBaseChangeIso X.hom b T.obj).inv c') at h
    exact h.trans (congrArg q₀ hc')
  have he : f = f' := by
    apply R'.homEquiv.injective
    apply (E.app (op T.obj)).addCommGroupIsoToAddEquiv.injective
    exact hleft.trans hright.symm
  exact congrArg (fun a : T ⟶ P' => a.hom) he

end Field

end AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily
