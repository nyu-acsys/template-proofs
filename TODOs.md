Things to do
------------

- Can we prove the lock/unlock specs shown in the paper?

- Why does traverse_spec return inFP(n') and domm In' = {[n']}?

- Rename ghost names to match paper.

- Reorder `globalinv` and `CSS` to match paper.

- (Discuss) add alias `in_inreach` for `in_inset` in link.v to match paper.

- Get rid of `is_CSS` and put the `exists I` in `CSS` to match paper.

- Prove replacement lemma for new contextual extension.

- Add template for full-split.

- Get rid of `in_inset` etc. in `linkset_flows.v` and `inset_flows.v` and instead use `k ∈ inset`.

- We can try to get rid of getLockLoc and just do CAS (lockLoc "l") #true #false in lock, etc.

- Can we make `findNext` return a bool and a node instead of an option node to match implementations?
