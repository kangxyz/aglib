# Native sections and an initial object

[Initial](Initial.lean) defines `Functor.sectionsEquivOfIsInitial`: evaluation
of the existing compatible sections at a specified initial object. Its
inverse uses the original functor maps from that object. Forward, inverse
and coefficient-naturality formulas are explicit. No chosen limit or
smallness condition on the diagram is needed.

The actual unit-module/global-section comparison consumes this interface
on the opposite category of scheme opens, with the whole open as its
initial object.
