# Actual tensor-product comparisons

| Source import | Native result and conditions |
| --- | --- |
| `Aglib.RingTheory.TensorProduct.Domain` | `Algebra.TensorProduct.tensorProduct_isDomain`: an algebraically closed base field and arbitrary commutative domain algebras give a domain tensor product. Finite type occurs only in the internal specialization step. |
| `Aglib.RingTheory.TensorProduct.Equalizer` | `AlgHom.Equalizer.equiv`: flat scalar extension commutes with the explicit equalizer of two actual algebra homomorphisms. |
| `Aglib.RingTheory.TensorProduct.PurelyInseparable` | `Algebra.TensorProduct.tensorAugmentation` is the split augmentation. Its kernel is nil for a purely inseparable field extension and nilpotent when the extension is finite; no Noetherian condition on the coefficient algebra is required. |

[Domain](Domain.lean) also gives `specializeTensor` and no-zero-divisor interfaces; [Equalizer](Equalizer.lean) exposes the canonical tensor/equalizer map and its pure-tensor formula; [PurelyInseparable](PurelyInseparable.lean) supplies the formal-etale nilpotent-lifting comparison.

[Geometric connectedness](../../AlgebraicGeometry/Geometrically/Connected/README.md) consumes the domain tensor result. [Algebra descent](../Descent/README.md) consumes the equalizer and overlap-augmentation interfaces. These comparisons are on the actual algebras and scalar maps.

CoalgebraBaseChange owns `Algebra.TensorProduct.BaseChange`, the canonical
scalar extension of displayed algebra maps, counits and comultiplications.
Its tensor comparison uses the actual tensor product. No field, normality,
finiteness or torsor premise is introduced by these lower maps.

[CommutingActions](CommutingActions.lean) constructs the action of `B ⊗[A] S`
from commuting `B` and `S` actions with compatible `A` scalar towers. The action is
the native tensor universal map into `A`-linear endomorphisms; pure tensors act
by the two original scalar actions. It preserves the `B` and `A` scalar towers
and maps intertwining the original actions. This supplies the affine-coordinate
scalar extension for external graded modules without flatness assumptions.
[CommutingActionsNaturality](CommutingActionsNaturality.lean) allows the
coordinate ring to vary: a coordinate-semilinear map commuting with the second
scalar action intertwines tensor actions along the original tensor algebra map.
This is the restriction/overlap compatibility, not a base-change isomorphism.

[PushoutModuleEquiv](PushoutModuleEquiv.lean) upgrades an original coordinate scalar-extension
isomorphism across an algebra pushout, using a compatible module map. Its
forward map is the original scalar-extension map on every pure tensor.
[CoordinatePushout](CoordinatePushout.lean) identifies the actual coordinate tensor map as the algebra
pushout square, retaining the original coordinate algebra and scalar tower.
Together these suppliers promote original affine localization to localization
over the full tensor ring, without a flatness hypothesis.

[KernelTransport](KernelTransport.lean) transfers an actual tensor-kernel module to its original
additive coordinates. The original coordinate-linear inclusion proves the
literal tensor-scalar law and determines the original homogeneous scalar maps.
