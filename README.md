# stdiff

Here we develop the diffing primitives for the universe 
of regular types.

The goal of this experiment is to have a stable and relatively simple model
where we can study conflict resolution before porting our ideas
to the universe of Regular Tree Types.

# Agda Versions

The development is made on Agda 2.5.3 and standard library 0.14

# Branches

## master

Finished results; The latest being that the merge of disjoint pathes commute.
For any regular type `t`, and patches `p , q` for elements of type `t`,
if `p` and `q` are disjoint (that is, alter different parts of the tree),
then:

```
apply (merge p q) . apply p == apply (merge q p) . apply q
```

## multirec

Starts extending the algorithm to mutually-recursive families of types
instead of regular types. Very preliminary; only description
of types are done.

## experimental-algorithm

Experiments with a different enumeration heuristic; had the hopes of speeding
things up. Not so much luck though.

## es-to-tree-proof

Here we are trying to convert Lempsink's notion of patches (linear edit scripts
on the list of constructors as seen in a preorder traversal of the trees) to
our tree-structured pathces.

The idea here being that we might be able to have the best of both worls:
i)  Linear patches are easy to compute and hard to merge
ii) Tree-structured patches are hard to compute but easy to merge;
iii) Computing a linear patch and translating to a tree-structured patch
     might just be the solution.

## identity-postulate-removal

Working on removing the postulates about identity patches; Not critical
but will require some work.


