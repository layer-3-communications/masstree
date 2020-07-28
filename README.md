# Masstree

This package provides a Masstree data structure based on the paper
"Cache  Craftiness  for  Fast  Multicore  Key-Value  Storage" by Mao, Kohler, and Morris
([pdf](https://pdos.csail.mit.edu/papers/masstree:eurosys12.pdf)).
The key idea is a trie which achieves a fanout of 2^64 by using a B+-tree at
each node. Where their paper focuses on supporting efficient concurrent
update, that approach is not idiomatic in Haskell, so we focused instead on a
persistent form of masstree.

Incidentally, we also expose a standalone `BTree` implementation which
outperforms `Map Word64` from the containers package, but to only supports
`Word64` keys (and if you can't guess how this limitation is related to the
2^64 fanout mentioned above, I'd be one surprised pickachu face).
