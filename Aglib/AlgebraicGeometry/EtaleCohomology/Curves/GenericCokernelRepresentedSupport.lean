/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.GenericCokernelLocalLifting
public import Aglib.Topology.NoetherianCurveSupport

/-!
# Finite support neighborhoods for represented generic-unit cokernel sections

The cokernel class of an actual generic direct-image section is zero on
affine neighborhoods of all generic points, with finite closed complement
on a Noetherian curve test. The cokernel and restriction maps are the original
small-etale abelian-sheaf maps. Arbitrary cokernel sections still require
local lifting along the original cokernel epimorphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace Set
open GroupCohomology.Kummer.Coefficients

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Curves

universe u

private theorem cokernel_restriction_zero {X : Scheme.{u}}
    {A B : AbelianSheaf.{u, u + 1} X} (φ : A ⟶ B) {U V : X.Etale} (f : V ⟶ U)
    (a : B.obj.obj (op U)) (b : A.obj.obj (op V))
    (h : φ.hom.app (op V) b = B.obj.map f.op a) :
    (cokernel φ).obj.map f.op ((cokernel.π φ).hom.app (op U) a) = 0 := by
  have hn := ConcreteCategory.congr_hom ((cokernel.π φ).hom.naturality f.op) a
  have hz := congrArg (fun k : A ⟶ cokernel φ => k.hom.app (op V)) (cokernel.condition φ)
  have hzv := ConcreteCategory.congr_hom hz b
  change (cokernel.π φ).hom.app (op V) (φ.hom.app (op V) b) = 0 at hzv
  exact hn.symm.trans ((congrArg (fun c => (cokernel.π φ).hom.app (op V) c) h.symm).trans hzv)

variable {X : Scheme.{u}} [IsNoetherian X] (U : X.Etale) [QuasiCompact U.hom]

/-- An actual represented cokernel class is locally zero off a finite closed set. -/
theorem genericCokernel_represented_zero_off_finite (hdim : topologicalKrullDim U.left ≤ 1)
    (a : ((directImage (genericArtinMap X)).obj (gm (genericArtinLocus X))).obj.obj (op U)) :
    ∃ (W : genericPoints U.left → U.left.Opens) (_hW : ∀ η, IsAffineOpen (W η))
      (_hηW : ∀ η, η.val ∈ W η),
      (∀ η, (cokernel (genericArtinUnit X)).obj.map (Etale.openChartHom U (W η)).op
        ((cokernel.π (genericArtinUnit X)).hom.app (op U) a) = 0) ∧
      ((⋃ η, (W η : Set U.left))ᶜ).Finite := by
  let : IsNoetherian U.left := {
    toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian (X := U.left) (Y := X) U.hom
    toCompactSpace := QuasiCompact.compactSpace_of_compactSpace (X := U.left) (Y := X) U.hom }
  let e := genericArtinBaseChangeIndexEquiv (X := X) (U := U.left) U.hom
  choose W hW hpW b hb using fun η : genericPoints U.left =>
    exists_genericUnit_local_lift U a (e.symm η)
  have hηW : ∀ η : genericPoints U.left, η.val ∈ W η := by
    intro η
    have he : (pullback.fst U.hom (genericArtinMap X)) (e.symm η) = η.val :=
      (genericArtinBaseChangeIndexEquiv_val (X := X) (U := U.left) U.hom (e.symm η)).symm.trans
        (congrArg Subtype.val (e.apply_symm_apply η))
    exact he ▸ hpW η
  refine ⟨W, hW, hηW, ?_, ?_⟩
  · intro η
    exact cokernel_restriction_zero (genericArtinUnit X) (Etale.openChartHom U (W η)) a
      (b η) (hb η)
  · exact TopologicalSpace.finite_compl_open_of_contains_genericPoints hdim
      (isOpen_iUnion fun η => (W η).isOpen)
      (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hηW ⟨x, hx⟩⟩)

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves
