TODO
----

* Build a better `Tree`. No point in walking down n levels just to get to one leaf. Reify `unit k j` as a data constructor.
  We can still zip. More complicated logic for all operations, but speed!

* Provide code for converting trees <-> a prefix of the naturals as an `STArray`.

* Prove I can implement the Gordon Complementary Bijection Principle (GCBP) in O(n log n) time using those two things, and by repeated
  "squerging" on the flat array representation, which would improve the time bound from Yorgey and Foner's O(n^2 log n). 
  Probably publishable.

* Find a use for the GCBP in nominal logic! It should be a usable nominal morphism. "Effective" is the same as nominal,
  replace the word "support" with "stabilizer" and everything transfers from Feldman and Propp.

* Let's re-examine support.

  Support is, effectively, a vocabulary for talking about stabilizers. 

  `G(x) = { y ∈ X | y = g.x, g ∈ G }` is the orbit of x ∈ X under G.
  `G_x = { g ∈ G | g.x = x }` is the stabilizer of x in G.
  `G(x) = G/G_x` and the group's action on G_x is transitive.

  Classically (no pun intended) minimal support is computable. In practice, for computer science needs a finite superset of support
  suffices, but at the cost of transitivity.

  We normally (no pun intended) talk about support in terms of sets of atoms that if you hold them in place, πx=x.

  It seems to me that this isn't the right notion!

  Consider centralizers and normalizers,
  
  `C_G(A) = { g ∈ G | ∀a ∈ A, gag⁻¹=a }` is the centralizer of A in G
  `N_G(A) = { g ∈ G | gA = Ag }` is the normalizer of A in G

  C_G(A) ⊆ N_G(A) ⊆ G

  All of the literature on nominal sets I can find actually only talks about support, which speaks to stabilizers, to get at centralizers.

  In general, this seems to make sense, for single atoms, C_G(a) = N_G(a)!
  
  But consider sets of atoms, not to be confused by sets in the category Set, which are being acted on by permutations in Nom. 
  e.g. the `Set` type in `Nominal.Set`. Those are stable under the larger class N_G(A). You can permute elements in their support,
  you can permute elements outside of their support, but don't cross the boundary in any cycle.

  Properly tallking about their support is effectively talking about partitions that we'd have to respect on atoms. Properly computing
  minimal support here should be computing N_G(S) for the set S of atoms they cover, not C_G(S).

  How to represent such a partitioning in such a way that it can be glued together with other supports?

  I've already gained some benefit from this view in the code for `instance Perm Set`

  This also might point to some use for the GCBP in nominal logic. Why? It provides us a way to enforce respect for such boundaries
  in a nominal-logic compatible manner. This might be publishable.

* Wire the concat plugin up to "Nom", with whatever changes I really need in order to build some kind of alpha-Haskell/fresh-haskell.
  Not sure how robust the compiling to categories stuff is though.

* Implement nominal unification through higher order pattern unification. O(n^2)

* Build NominalFunctor and instances for Tie, Suspended, etc.

* Do we really need arbitrary permutations on Atoms? All operations could get by with just the ability to find something outside
  joint support that can be swapped in.

* What does guanxi need to be able to support nominal logic programming a la α-kanren?

