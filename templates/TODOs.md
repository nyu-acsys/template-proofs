Things to do
------------

- Why is Ψ iProp?

- Reorder `globalinv` and `CSS` to match paper.

- (Discuss) add alias `in_inreach` for `in_inset` in link.v to match paper.

- Prove replacement lemma for new contextual extension.

- Add template for full-split.

- Get rid of `in_inset` etc. in `linkset_flows.v` and `inset_flows.v` and instead use `k ∈ inset`.

- Can we make `findNext` return a bool and a node instead of an option node to match implementations?


Lessons learnt
--------------

- Use P -* Q -* R instead of P * Q -* R.

- Avoid iFrame "∗ % #" its too slow.

- Use `as (?C) "H"` pattern to introduce a fresh variable C0/C1/...

- `iAssert (⌜False⌝)%I` can be replaced with `iExFalso`.

