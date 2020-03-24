Things to do
------------

- Factor out the lock module.

- Get rid of `in_inset` etc. in `linkset_flows.v` and `inset_flows.v` and instead use `k ∈ inset`.

- We can try to get rid of getLockLoc and just do CAS (lockLoc "l") #true #false in lock, etc.

- Can we simplify the match in `findNext_spec` to `⌜b → in_inset k I_n n⌝`? Similarly get rid of the if-then-else in `lockNode_spec`.

- 
