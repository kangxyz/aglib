/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

/- Current interface basis: 46f53465aaf3b0167049e9c8e9e2294111bb4281.
Original construction and mathematical provenance are retained below. -/
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.SchemeTorsorClassification
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.TorsorClass

/-!
# Coefficient naturality of the actual represented-torsor comparison

Construction for `K2-018#eq:k2018-pointed-character`, frozen basis
`7f86e4a1763cc4ec35e9b0a8acd659750355a0de`. An ordinary coefficient-equivariant
sheaf torsor morphism gives its actual scheme morphism by the proved Yoneda
inverse. Equivariance is proved on every scheme test via the universal finite
product, and actual fibre evaluation gives the common continuous-H¹ square.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj CategoryTheory.PreGaloisCategory
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (Fiber fiberToFinite toEtale)
open AlgebraicGeometry.Scheme.EtaleFundamentalGroups
open CategoryTheory
open AlgebraicGeometry.Scheme.FiniteEtale.GroupDescent
open AlgebraicGeometry.Scheme.FiniteEtale.FiberTorsorActions
namespace AlgebraicGeometry.Scheme.EtaleCohomology
universe u
attribute [local instance] Over.cartesianMonoidalCategory coverCartesian
variable {X : Scheme.{u}}
variable (A B : Grp (Over X)) [IsCommMonObj A.X] [IsCommMonObj B.X]
variable {P : Torsor (representedSheaf A)} {Q : Torsor (representedSheaf B)}
variable (q : A ⟶ B) (r : Torsor.Hom (representedSheafMap q) P Q)
variable (Y Z : Scheme.FiniteEtale X) (e : finiteRepresentedSetSheaf Y ≅ P.carrier)
variable (d : finiteRepresentedSetSheaf Z ≅ Q.carrier)

/-- The actual scheme map associated to an ordinary coefficient-equivariant
sheaf torsor morphism, using the proved Yoneda inverse. -/
def Torsor.Hom.representedMap : Y.obj ⟶ Z.obj :=
  finiteRepresentedSetSheafPreimage (e.hom ≫ r.map ≫ d.inv)

/-- Exact section evaluation of the recovered actual scheme morphism. -/
theorem Torsor.Hom.representedMap_section (U : X.Etale)
    (x : (Scheme.Etale.forget X).obj U ⟶ Y.obj) :
    d.hom.hom.app (op U) (ULift.up (x ≫ r.representedMap A B q Y Z e d)) =
      r.map.hom.app (op U) (e.hom.hom.app (op U) (ULift.up x)) := by
  have h := finiteRepresentedSetSheafPreimage_app (e.hom ≫ r.map ≫ d.inv) U x
  change ULift.up (x ≫ r.representedMap A B q Y Z e d) =
    d.inv.hom.app (op U) (r.map.hom.app (op U) (e.hom.hom.app (op U) (ULift.up x))) at h
  rw [h]
  exact congrArg (fun a : Q.carrier ⟶ Q.carrier => a.hom.app (op U)
    (r.map.hom.app (op U) (e.hom.hom.app (op U) (ULift.up x)))) d.inv_hom_id

variable [IsFinite A.X.hom] [Etale A.X.hom] [IsFinite B.X.hom] [Etale B.X.hom]

/-- The actual representative morphism preserves the original coefficient action
on all étale test schemes, with the given actual group-scheme morphism. -/
theorem Torsor.Hom.representedMap_equivariant_etale (U : X.Etale)
    (a : (Scheme.Etale.forget X).obj U ⟶ A.X)
    (x : (Scheme.Etale.forget X).obj U ⟶ Y.obj) :
    (P.representedSchemeAction A Y e).act a x ≫ r.representedMap A B q Y Z e d =
      (Q.representedSchemeAction B Z d).act (a ≫ q.hom.hom)
        (x ≫ r.representedMap A B q Y Z e d) := by
  apply (Q.representedSectionEquiv B Z d U).injective
  change d.hom.hom.app (op U) (ULift.up _) = d.hom.hom.app (op U) (ULift.up _)
  rw [r.representedMap_section, P.representedSchemeAction_section,
    Q.representedSchemeAction_section, r.representedMap_section]
  exact r.equivariant (op U) (ULift.up (Additive.ofMul a)) (e.hom.hom.app (op U) (ULift.up x))

/-- The universal finite coefficient-times-torsor product extends the proved
action compatibility to every scheme-valued point, including geometric fibres. -/
theorem Torsor.Hom.representedMap_equivariant {T : Over X} (a : T ⟶ A.X) (x : T ⟶ Y.obj) :
    (P.representedSchemeAction A Y e).act a x ≫ r.representedMap A B q Y Z e d =
      (Q.representedSchemeAction B Z d).act (a ≫ q.hom.hom)
        (x ≫ r.representedMap A B q Y Z e d) := by
  have h := r.representedMap_equivariant_etale A B q Y Z e d
    ((toEtale X).obj (Torsor.representedActionDomain A Y)) (fst A.X Y.obj) (snd A.X Y.obj)
  have hh := congrArg (fun m => lift a x ≫ m) h
  simpa only [← Category.assoc, TorsorAction.naturality, lift_fst, lift_snd] using hh

section Classes
open ContinuousTorsors SchemeTorsorClassification
open GroupCohomology.ContinuousH1
variable {K : Type u} [Field K] (s : Spec (CommRingCat.of K) ⟶ X)
variable {M N : Type u} [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
variable [AddCommGroup N] [TopologicalSpace N] [DiscreteTopology N]
variable [DistribMulAction (FiberAutGroup s) M] [ContinuousSMul (FiberAutGroup s) M]
variable [DistribMulAction (FiberAutGroup s) N] [ContinuousSMul (FiberAutGroup s) N]
variable (markA : (Over.mk s ⟶ A.X) ≃* Multiplicative M)
variable (markB : (Over.mk s ⟶ B.X) ≃* Multiplicative N)
variable (hmarkA : ∀ (γ : FiberAutGroup s) (a : Over.mk s ⟶ A.X),
  markA (γ.hom.app (coefficientCover A) a) = Multiplicative.ofAdd (γ • (markA a).toAdd))
variable (hmarkB : ∀ (γ : FiberAutGroup s) (b : Over.mk s ⟶ B.X),
  markB (γ.hom.app (coefficientCover B) b) = Multiplicative.ofAdd (γ • (markB b).toAdd))
variable (φ : CoefficientMap (FiberAutGroup s) M N)
variable (hq : ∀ a : Over.mk s ⟶ A.X, (markB (a ≫ q.hom.hom)).toAdd = φ (markA a).toAdd)

include hq in
set_option linter.unusedSectionVars false in
-- Preserve the original supplied hypotheses and binder order.
/-- The given coefficient marking square is used on the actual fibre morphism. -/
-- Keep the original supplied class/data inputs and binder order of this interface.
@[nolint unusedArguments]
theorem representedMap_marked_translation (m : M) (x : Fiber s Y) :
    (P.representedSchemeAction A Y e).act (markA.symm (Multiplicative.ofAdd m)) x ≫
        r.representedMap A B q Y Z e d =
      (Q.representedSchemeAction B Z d).act (markB.symm (Multiplicative.ofAdd (φ m)))
        (x ≫ r.representedMap A B q Y Z e d) := by
  rw [r.representedMap_equivariant]
  congr 1
  apply markB.injective
  rw [MulEquiv.apply_symm_apply]
  apply Multiplicative.toAdd.injective
  rw [hq, MulEquiv.apply_symm_apply]
  rfl

include r hq in
/-- The common continuous-H¹ class of any two actual representatives is
natural for the actual sheaf/group morphism and the ordinary marked coefficient map. -/
theorem representedSchemeClass_naturality [Nonempty (Fiber s Y)] [Nonempty (Fiber s Z)] :
    schemeTorsorClass s B Z (Q.representedSchemeAction B Z d) markB hmarkB =
      φ.onH1 (schemeTorsorClass s A Y (P.representedSchemeAction A Y e) markA hmarkA) :=
  schemeTorsorClass_naturality s A Y (P.representedSchemeAction A Y e) markA hmarkA
    B Z (Q.representedSchemeAction B Z d) markB hmarkB φ
    (fun x => x ≫ r.representedMap A B q Y Z e d)
    (representedMap_marked_translation A B q r Y Z e d s markA markB φ hq)
    (fun γ x => (Scheme.FiniteEtale.FiberTorsorActions.evaluation_naturality s γ
      (r.representedMap A B q Y Z e d) x).symm)

variable [GaloisCategory (Scheme.FiniteEtale X)] [PreGaloisCategory.FiberFunctor (fiberToFinite s)]
variable (hR : Stacks03RV X)
variable (hA : IsFiniteLocallyConstant (representedSheaf A))
variable (hB : IsFiniteLocallyConstant (representedSheaf B))

include r hq in
/-- Naturality of the explicit genuine torsor-class extraction, with no
cohomological naturality square supplied as a premise. -/
theorem representedTorsorClass_naturality :
    representedTorsorClass s B markB hmarkB hR hB Q =
      φ.onH1 (representedTorsorClass s A markA hmarkA hR hA P) := by
  let Y' := P.finiteEtaleRepresentative hR hA
  let Z' := Q.finiteEtaleRepresentative hR hB
  let e' := P.finiteEtaleRepresentativeIso hR hA
  let d' := Q.finiteEtaleRepresentativeIso hR hB
  let : Surjective Y'.obj.hom := P.represented_surjective A Y' e'
  let : Surjective Z'.obj.hom := Q.represented_surjective B Z' d'
  let : Nonempty (Fiber s Y') := nonempty_fiber_of_surjective s Y'
  let : Nonempty (Fiber s Z') := nonempty_fiber_of_surjective s Z'
  exact representedSchemeClass_naturality A B q r Y' Z' e' d' s
    markA markB hmarkA hmarkB φ hq

include r hq in
/-- The quotient representative formula exposes the same coefficient square
for the public torsor-class-to-H¹ map. -/
theorem torsorClassToH1_naturality :
    SchemeTorsorClassification.torsorClassToH1 s B markB hmarkB hR hB (Quotient.mk _ Q) =
      φ.onH1 (SchemeTorsorClassification.torsorClassToH1 s A markA hmarkA hR hA (Quotient.mk _
        P)) :=
  representedTorsorClass_naturality A B q r s markA markB hmarkA hmarkB φ hq hR hA hB

end Classes
end AlgebraicGeometry.Scheme.EtaleCohomology

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 2353e76ee2c0c7def6839c92f93b98d252cfbae03c860071d337c6861b5e6f4d.
Definitions, hypotheses and universes are retained modulo native names. -/
