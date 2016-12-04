This branch (prototuples) is an attempt to add the capability to issue RLWE/RLWR challenges over product rings.
The challenge is figuring out how to serialize these product rings. Currently unsolved.
Also, this capability is needed to serialize key switch hints, which would allow us to
save and reuse precomputation. See branch 'cached-hints'.