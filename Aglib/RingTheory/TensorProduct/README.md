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
