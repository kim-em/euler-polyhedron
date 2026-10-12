# Vendored Euler proof

These 14 Lean modules are copied without modification from
[tangentproofs/eulers-gem](https://github.com/tangentproofs/eulers-gem),
commit `02c67906ae6b427f7c5c73fab0c89e7956a8a3c1`, directory `lean/EulersGem`.
They are the transitive import closure of `EulersGem.Embed` and
`EulersGem.PolytopeFaces`. The original file headers credit Michal Wallace
and Grok Bot and state the Apache 2.0 licence. Those headers are preserved.
The upstream repository's root MIT licence is also preserved as `LICENSE`
in this directory; the Apache 2.0 text is in the project root.

The Euler proof follows Lawrence C. Paulson's AFP *Euler's Polyhedron
Formula* (2023), ported from HOL Light and crediting Jim Lawrence.
The representation theorem added by this project is in `EulerPolyhedron/`.
