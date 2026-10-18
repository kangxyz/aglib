/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.FundamentalGroup.PointedInjection

/-!
# Restricting actual fibre automorphisms to a finite étale pointed cover

An automorphism fixing the selected fibre point of a finite étale base cover
acts on the actual fibres of every cover of that base. This is the component
preservation step for the constructive geometric-kernel inverse.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (Fiber baseChange fiberBaseChangeEquiv
  fiberBaseChangeEquiv_left fiberToFinite forgetToScheme mk)
open AlgebraicGeometry.Scheme.EtaleFundamentalGroups

namespace AlgebraicGeometry.Scheme.FiniteEtale.PointLift

universe u
variable {K : Type u} [Field K] {S X : Scheme.{u}}
  (f : S ⟶ X) [IsFinite f] [Etale f]
  (s : Spec (CommRingCat.of K) ⟶ S)

/-- The finite etale cover of `X` obtained by composing the structure map of `Y` with `f`. -/
def totalCover (Y : Scheme.FiniteEtale S) : Scheme.FiniteEtale X := mk (Y.obj.hom ≫ f)

/-- The map of total covers induced by a morphism of covers over `S`. -/
def totalCoverMap {Y Z : Scheme.FiniteEtale S} (g : Y ⟶ Z) : totalCover f Y ⟶ totalCover f Z :=
  ObjectProperty.homMk ((Over.map f).map g.hom)

/-- The map from the total cover of `Y` to the cover `f`, with underlying map `Y.obj.hom`. -/
def totalProjection (Y : Scheme.FiniteEtale S) : totalCover f Y ⟶ mk f :=
  ObjectProperty.homMk (Over.homMk Y.obj.hom rfl)

/-- The fibre point of the cover `f` over `s ≫ f` represented by `s`. -/
def selectedPoint : Fiber (s ≫ f) (mk f) := Over.homMk s rfl

/-- A fibre point over `s` regarded as a point of the total cover over `s ≫ f`. -/
def totalFiber (Y : Scheme.FiniteEtale S) (q : Fiber s Y) : Fiber (s ≫ f) (totalCover f Y) :=
  Over.homMk q.left (by
    change q.left ≫ (Y.obj.hom ≫ f) = s ≫ f
    rw [← Category.assoc, Over.w q]
    rfl)

theorem totalFiber_injective (Y : Scheme.FiniteEtale S) : Function.Injective
    (totalFiber f s Y) := by
  intro q r h
  exact Over.OverMorphism.ext (congrArg (fun z ↦ z.left) h)

-- Keep this original canonical-map simp formula alongside its lower evaluation expansion.
@[simp, nolint simpNF] theorem totalFiber_projection (Y : Scheme.FiniteEtale S) (q : Fiber s Y) :
    (fiberToFinite (s ≫ f)).map (totalProjection f Y) (totalFiber f s Y q) =
      selectedPoint f s :=
  Over.OverMorphism.ext (Over.w q)

-- Keep this original canonical-map simp formula alongside its lower evaluation expansion.
@[simp, nolint simpNF]
theorem totalFiber_map {Y Z : Scheme.FiniteEtale S} (g : Y ⟶ Z) (q : Fiber s Y) :
    totalFiber f s Z ((fiberToFinite s).map g q) =
      (fiberToFinite (s ≫ f)).map (totalCoverMap f g) (totalFiber f s Y q) := rfl

variable (a : FiberAutGroup (s ≫ f))
  (ha : a.hom.app (mk f) (selectedPoint f s) = selectedPoint f s)

/-- Naturality along the real structural map preserves the selected component. -/
def liftPoint (Y : Scheme.FiniteEtale S) (q : Fiber s Y) : Fiber s Y :=
  Over.homMk (a.hom.app (totalCover f Y) (totalFiber f s Y q)).left (by
    have hn := evaluate_naturality (s ≫ f) a (totalProjection f Y) (totalFiber f s Y q)
    rw [totalFiber_projection, ha] at hn
    exact congrArg (fun z ↦ z.left) hn)

@[simp] theorem totalFiber_liftPoint (Y : Scheme.FiniteEtale S) (q : Fiber s Y) :
    totalFiber f s Y (liftPoint f s a ha Y q) =
      a.hom.app (totalCover f Y) (totalFiber f s Y q) :=
  Over.OverMorphism.ext rfl

include ha in
theorem inverse_fixes_selectedPoint :
    a.inv.app (mk f) (selectedPoint f s) = selectedPoint f s := by
  have h := ConcreteCategory.congr_hom (a.hom_inv_id_app (mk f)) (selectedPoint f s)
  change a.inv.app (mk f) (a.hom.app (mk f) (selectedPoint f s)) = selectedPoint f s at h
  rwa [ha] at h

/-- The permutation of the fibre over `s` induced by `a`, assuming `a` fixes the selected point. -/
def liftFiberEquiv (Y : Scheme.FiniteEtale S) : Fiber s Y ≃ Fiber s Y where
  toFun := liftPoint f s a ha Y
  invFun := liftPoint f s a.symm (inverse_fixes_selectedPoint f s a ha) Y
  left_inv q := by
    apply totalFiber_injective f s Y
    rw [totalFiber_liftPoint, totalFiber_liftPoint]
    exact ConcreteCategory.congr_hom (a.hom_inv_id_app (totalCover f Y)) (totalFiber f s Y q)
  right_inv q := by
    apply totalFiber_injective f s Y
    rw [totalFiber_liftPoint, totalFiber_liftPoint]
    exact ConcreteCategory.congr_hom (a.inv_hom_id_app (totalCover f Y)) (totalFiber f s Y q)

theorem liftPoint_naturality {Y Z : Scheme.FiniteEtale S} (g : Y ⟶ Z) (q : Fiber s Y) :
    (fiberToFinite s).map g (liftPoint f s a ha Y q) =
      liftPoint f s a ha Z ((fiberToFinite s).map g q) := by
  apply totalFiber_injective f s Z
  rw [totalFiber_map, totalFiber_liftPoint, totalFiber_liftPoint, totalFiber_map]
  exact evaluate_naturality (s ≫ f) a (totalCoverMap f g) (totalFiber f s Y q)

/-- The resulting automorphism is of the existing finite-valued point fibre functor. -/
def liftAut : FiberAutGroup s :=
  NatIso.ofComponents (fun Y ↦ FintypeCat.equivEquivIso (liftFiberEquiv f s a ha Y)) (by
    intro Y Z g
    apply FintypeCat.hom_ext
    intro q
    exact (liftPoint_naturality f s a ha g q).symm)

@[simp] theorem liftAut_evaluate (Y : Scheme.FiniteEtale S) (q : Fiber s Y) :
    totalFiber f s Y ((liftAut f s a ha).hom.app Y q) =
      a.hom.app (totalCover f Y) (totalFiber f s Y q) :=
  totalFiber_liftPoint f s a ha Y q

/-- The first pullback projection, viewed as a map from the total base-changed cover to `Y`. -/
def totalCounit (Y : Scheme.FiniteEtale X) : totalCover f ((baseChange f).obj Y) ⟶ Y :=
  ObjectProperty.homMk (Over.homMk (pullback.fst Y.obj.hom f) pullback.condition)

-- Keep this original canonical-map simp formula alongside its lower evaluation expansion.
@[simp, nolint simpNF]
theorem totalCounit_fiberBaseChange (Y : Scheme.FiniteEtale X) (q : Fiber (s ≫ f) Y) :
    (fiberToFinite (s ≫ f)).map (totalCounit f Y)
      (totalFiber f s ((baseChange f).obj Y) (fiberBaseChangeEquiv f s Y q)) = q := by
  apply Over.OverMorphism.ext
  change (fiberBaseChangeEquiv f s Y q).left ≫ pullback.fst Y.obj.hom f = q.left
  rw [fiberBaseChangeEquiv_left, pullback.lift_fst]

/-- The restricted natural automorphism maps back along the existing group map. -/
theorem map_liftAut : Scheme.EtaleFundamentalGroups.map f s
    (liftAut f s a ha) = a := by
  apply Aut.ext
  apply NatTrans.ext
  funext Y
  apply FintypeCat.hom_ext
  intro q
  rw [Scheme.EtaleFundamentalGroups.map_apply]
  change (fiberToFinite (s ≫ f)).map (totalCounit f Y)
      (totalFiber f s ((baseChange f).obj Y)
        ((liftAut f s a ha).hom.app ((baseChange f).obj Y) (fiberBaseChangeEquiv f s Y q))) = _
  rw [liftAut_evaluate, evaluate_naturality, totalCounit_fiberBaseChange]

/-- The graph of the structure map of `Y`, viewed as a map to its total cover pulled back to
`S`. -/
def totalGraph (Y : Scheme.FiniteEtale S) : Y ⟶ (baseChange f).obj (totalCover f Y) :=
  ObjectProperty.homMk (Over.homMk
    (pullback.lift (𝟙 Y.obj.left) Y.obj.hom (by
      change (𝟙 Y.obj.left) ≫ (Y.obj.hom ≫ f) = Y.obj.hom ≫ f
      exact Category.id_comp _)) (pullback.lift_snd _ _ _))

instance totalGraph_mono (Y : Scheme.FiniteEtale S) : Mono (totalGraph f Y) := by
  apply (forgetToScheme S).mono_of_mono_map
  apply mono_of_mono_fac (f := pullback.fst (totalCover f Y).obj.hom f) (h := 𝟙 Y.obj.left)
  exact pullback.lift_fst _ _ _

/-- Finite étale pointed base maps are injective on the actual fibre automorphism groups. -/
theorem map_injective : Function.Injective
    (Scheme.EtaleFundamentalGroups.map f s) := by
  exact PointedInjection.pointedMap_injective_of_subobjects
    (Under.homMk f rfl : Under.mk s ⟶ Under.mk (s ≫ f))
    (fun Y ↦ ⟨totalCover f Y, totalGraph f Y, inferInstance⟩)

/-- The fibre-functor automorphism at `s` lifted from `b` using `hs`, assuming `b` fixes the
point represented by `s`. -/
def pointedLiftAut (x : Spec (CommRingCat.of K) ⟶ X) (hs : s ≫ f = x)
    (b : FiberAutGroup x)
    (hb : b.hom.app (mk f) (Over.homMk s hs) = Over.homMk s hs) : FiberAutGroup s := by
  subst x
  exact liftAut f s b hb

theorem pointedMap_pointedLiftAut (x : Spec (CommRingCat.of K) ⟶ X) (hs : s ≫ f = x)
    (b : FiberAutGroup x)
    (hb : b.hom.app (mk f) (Over.homMk s hs) = Over.homMk s hs) :
    pointedMap (Under.homMk f hs : Under.mk s ⟶ Under.mk x)
      (pointedLiftAut f s x hs b hb) = b := by
  subst x
  exact map_liftAut f s b hb

theorem pointedMap_injective (x : Spec (CommRingCat.of K) ⟶ X) (hs : s ≫ f = x) :
    Function.Injective (pointedMap (Under.homMk f hs : Under.mk s ⟶ Under.mk x)) := by
  subst x
  exact map_injective f s

end AlgebraicGeometry.Scheme.FiniteEtale.PointLift

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 05e17275d32330b0bc3c241638d6c80fc0a0d27ea3a30d6a59eb79c98e949c41.
Definitions, hypotheses and universes are retained modulo native names. -/
