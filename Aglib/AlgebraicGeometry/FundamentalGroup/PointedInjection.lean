/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.FundamentalGroup.GeometricKernel
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Connectedness

/-!
# A cover-extension criterion for the actual geometric homomorphism

The criterion below isolates the injectivity argument in Stacks 0BTX. It does
not construct the extension of a geometric cover; that finite-presentation
descent obligation is retained explicitly. It uses the existing point fibre
and the existing pointedMap, so there is no replacement fundamental-group map.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (baseChange fiberToFinite)
open AlgebraicGeometry.Scheme.EtaleFundamentalGroups

namespace AlgebraicGeometry.Scheme.FiniteEtale.PointedInjection

universe u

variable {K : Type u} [Field K] {S X : PointedScheme K}

/-- A monomorphism of finite étale covers induces an injection of actual point
fibres, without any Galois-category or fibre-functor dictionary assumption. -/
theorem fiber_map_injective {B : Scheme.{u}} (x : Spec (CommRingCat.of K) ⟶ B)
    {Y Z : Scheme.FiniteEtale B} (j : Y ⟶ Z) [Mono j] :
    Function.Injective ((fiberToFinite x).map j) := by
  let : Mono j.hom.left := Connectedness.mono_left j
  intro a b h
  apply Over.OverMorphism.ext
  exact (cancel_mono j.hom.left).mp (congrArg (fun q ↦ q.left) h)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- If every source cover embeds into the pullback of a target cover, the
already defined homomorphism on fibre automorphisms is injective. -/
theorem pointedMap_injective_of_subobjects (f : S ⟶ X)
    (h : ∀ Y : Scheme.FiniteEtale S.right, ∃ Z : Scheme.FiniteEtale X.right,
      ∃ j : Y ⟶ (baseChange f.right).obj Z, Mono j) :
    Function.Injective (pointedMap f) := by
  intro a b hab
  apply Aut.ext
  apply NatTrans.ext
  funext Y
  apply FintypeCat.hom_ext
  intro q
  obtain ⟨Z, j, hj⟩ := h Y
  let : Mono j := hj
  apply fiber_map_injective S.hom j
  let t := (fiberToFinite S.hom).map j q
  have he := congrArg (fun g : FiberAutGroup X.hom ↦
    g.hom.app Z ((pointedFiberEquiv f Z).symm t)) hab
  simp only [pointedMap_apply, Equiv.apply_symm_apply] at he
  exact (evaluate_naturality S.hom a j q).trans
    (((pointedFiberEquiv f Z).symm.injective he).trans
      (evaluate_naturality S.hom b j q).symm)

open GeometricKernel

/-- The cover-extension criterion specializes to the exact existing
`geometricKernelHom`. Its geometric cover-extension premise remains to be
produced by finite-extension descent and purely inseparable invariance. -/
theorem geometricKernelHom_injective_of_subobjects
    (F : Type u) [Field F] {T : Scheme.{u}}
    (p : T ⟶ Spec (CommRingCat.of F))
    (o : Spec (CommRingCat.of F) ⟶ T) (ho : o ≫ p = 𝟙 _)
    (h : ∀ Y : Scheme.FiniteEtale (geometricBaseChange F p), ∃ Z : Scheme.FiniteEtale T,
      ∃ j : Y ⟶ (baseChange (pullback.fst p (algebraicClosurePoint F))).obj Z, Mono j) :
    Function.Injective (geometricKernelHom F p o ho) := by
  intro a b hab
  apply pointedMap_injective_of_subobjects
    (pointedInclusion (algebraicClosurePoint F) p o ho) h
  exact congrArg Subtype.val hab

end AlgebraicGeometry.Scheme.FiniteEtale.PointedInjection

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 f420351e239908171abba007184883a68465dc8d1e1a2230ca85f951c8d80e3b.
Definitions, hypotheses and universes are retained modulo native names. -/
