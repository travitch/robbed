This package implements a Reduced Ordered Binary Decision Diagram
(ROBDD) datatype.  See the haddock documentation for Data.ROBDD for
more details.

== TODO ==

 * Optimize
 * Implement the compose operation
 * Implement constant-time negation
 * Figure out how to memoize more of replace
 * Test alternative hash tables for memoization.  unordered-containers
   will probably switch to a hash-array mapped trie eventually, so
   that could help space.  A mutable hash table inside of the ST monad
   may give significant gains.
