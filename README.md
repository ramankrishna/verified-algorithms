# verified-algorithms

Algorithms with three things each: a mathematical proof of correctness, a tested Python
implementation, and a Lean 4 proof that the same procedure is correct.

## Results

| Algorithm | Math | Python | Lean |
|---|---|---|---|
| Euclid's GCD | ✓ | ✓ | ✓ verified |
| Exponentiation by squaring | ✓ | ✓ | ✓ verified |
| Fibonacci by dynamic programming | ✓ | ✓ | ✓ verified |
| Insertion sort | ✓ | ✓ | ✓ verified |
| Merge sort | ✓ | ✓ | ✓ verified |
| Binary search (lower bound) | ✓ | ✓ | ✓ verified |
| Dijkstra's shortest paths | ✓ | ✓ | ✓ verified |
| Union-find (quick-find) | ✓ | ✓ | ✓ verified |
| BFS radius bound: tree(G) ≥ rad(G) + 1 | ✓ | ✓ | ✓ verified |
| WOWII 84 for minimum degree ≥ 2 | ✓ | ✓ | ✓ verified |
| WOWII 96 independence bound | ✓ | ✓ | ✓ verified |
| Heap-based Dijkstra, union-find with path compression | ✓ | ✓ | not formalized |
| Independence number, largest induced tree and forest, Havel–Hakimi residue, Hamiltonian path DP, path cover DP, vertex connectivity | ✓ | ✓ | not formalized |

**11 of 11 Lean theorems verified.** Every verified proof uses only Lean's standard axioms
(`propext`, `Classical.choice`, `Quot.sound`), so there is no `sorry`, no `native_decide` and no added axiom.
The implementations and theorem statements were fixed and hashed before any proof was written.
Each one was checked to compile in Lean before any proof attempt.

**Python: 869 tests pass.** They check against the standard library (`math.gcd`, `pow`,
`sorted`, `bisect`) and against networkx, including 600 random weighted digraphs for Dijkstra
and 800 random union sequences for union-find. The three graph theorems are also checked numerically
on every connected graph with 2 to 7 vertices (995 graphs).

## How a Lean proof is accepted

A proof only counts if it passes all five checks:

1. no `sorry`, `admit`, `axiom`, `unsafe` or similar escape hatches
2. the implementation and theorem statement are unchanged from the registered version
3. Lean compiles the file
4. the theorem's type, as Lean itself prints it, equals the registered one
5. only standard axioms are used

## The algorithms

### Euclid's GCD
**Theorem.** `euclid a b = gcd(a, b)` for all naturals a, b.
**Proof.** Strong induction on b. If b = 0, gcd(a, 0) = a. Otherwise every common divisor of a and b
divides a mod b = a − ⌊a/b⌋·b, and every common divisor of b and a mod b divides a, so
gcd(a, b) = gcd(b, a mod b). Here a mod b < b, so the induction hypothesis applies.
**Cost.** O(log min(a, b)) steps: every two steps at least halve the larger argument.

### Exponentiation by squaring
**Theorem.** `powFast b e = b^e`.
**Proof.** Strong induction on e. With h = b^⌊e/2⌋: if e is even, h·h = b^(2⌊e/2⌋) = b^e;
if e is odd, h·h·b = b^(2⌊e/2⌋+1) = b^e.
**Cost.** O(log e) multiplications.

### Fibonacci by dynamic programming
**Theorem.** `fibDP n = F(n)`.
**Proof.** By induction, the DP state after n steps is (F(n), F(n+1)): the step maps
(F(n), F(n+1)) to (F(n+1), F(n) + F(n+1)) = (F(n+1), F(n+2)).
**Cost.** O(n) additions instead of the exponential naive recursion.

### Insertion sort
**Theorem.** The output is sorted and is a permutation of the input.
**Proof.** Two invariants of inserting x into a sorted list l: the result is a permutation of x :: l,
and it is sorted. For sortedness, x is placed before the first y with x ≤ y, so x is at most every
later element, and every earlier element is < x. Induction over the list then gives both properties for the whole sort.
**Cost.** O(n²) comparisons.

### Merge sort
**Theorem.** The output is sorted and is a permutation of the input.
**Proof.** Merging two sorted lists gives a sorted permutation of their concatenation: the emitted
head is the smaller of the two heads, so it is at most everything left in either list. Merge sort
splits at ⌊n/2⌋, sorts both halves by well-founded induction on length, and merges. The halves
concatenate back to the input, so the permutation property carries through.
**Cost.** O(n log n) comparisons.

### Binary search (lower bound)
**Theorem.** For a monotone predicate p on [lo, hi), the result r satisfies lo ≤ r ≤ hi,
p is false on [lo, r), and p is true on [r, hi). For p(i) = (a[i] ≥ x) this is Python's `bisect_left`.
**Proof.** Well-founded induction on hi − lo. With mid = ⌊(lo+hi)/2⌋: if p(mid) holds, monotonicity makes
p true on [mid, hi), so recurse on [lo, mid). If not, monotonicity makes p false on [lo, mid], so recurse
on [mid+1, hi). Each branch strictly shrinks the interval.
**Cost.** O(log(hi − lo)) evaluations of p.

### Dijkstra's shortest paths
**Theorem.** For a directed graph with non-negative integer weights, the distance Dijkstra reports
for v is the weight of some walk from s to v, and it is at most the weight of every walk from s to v.
So it is exactly the shortest-path distance, and "unreachable" exactly when no walk exists.
**Proof.** Four invariants hold after every round, with *settled* meaning already extracted:
1. every tentative distance is the weight of a real walk
2. settled vertices are never farther than unsettled ones
3. a settled vertex's distance never changes again, since anything relaxed later costs at least the current minimum
4. every edge out of a settled vertex is relaxed

The loop stops once no unsettled vertex has a finite distance, or after n rounds when everything is
settled. Then induction on any walk shows the reported distance is at most the walk's weight: the
walk's second-to-last vertex is settled, and its last edge was relaxed.
**Cost.** O(n²) for the array version proved in Lean; O((n + m) log n) with a heap.

### Union-find (quick-find)
**Theorem.** After processing a list of unions, two elements have the same label exactly when they
are connected by the unions, i.e. related by the equivalence relation the pairs generate.
**Proof.** Induction over the list, with two invariants. Every element is equivalent to its own label,
because labels only move to the label of the other side of a union. Equivalent elements share a label,
because a union preserves equal labels and makes the two united elements share one.
**Cost.** O(n) per union for quick-find; the path-compression version runs in near-constant
amortized time per operation.

### BFS radius bound
**Theorem.** Every connected graph has an induced tree on at least rad(G) + 1 vertices.
**Proof.** BFS finds u, v at distance rad(G). A shortest u–v path has no chords, since a chord would
give a shorter path. So its rad(G) + 1 vertices induce a path, which is a tree.

### WOWII 84 for minimum degree ≥ 2
**Theorem.** If δ(G) ≥ 2, then tree(G) ≥ 2·rad(G)/δ(G).
**Proof.** 2·rad/δ ≤ rad < rad + 1 ≤ tree(G), using the BFS radius bound.

### WOWII 96 independence bound
**Theorem.** α(G) ≤ 1 + m·(L − 1), where m is the minimum number of vertices at even distance from a
vertex, and L is the largest independence number of a vertex neighbourhood.
**Proof.** Run BFS from a vertex v achieving m and map each vertex of a maximum independent set
to itself (even layers) or to its BFS parent (odd layers). At most L vertices land on v and at most
L − 1 on each other even-layer vertex, since that vertex's own parent can be added to what lands
on it. Summing gives α ≤ L + (m − 1)(L − 1).

### Exact graph invariants (Python)
Bitmask implementations used to search every small graph:
- BFS eccentricity, radius and diameter, O(n²) per graph
- independence number and largest induced tree and forest, by subset enumeration
- Havel–Hakimi residue
- Hamiltonian paths and path cover number, by Held–Karp style DP over (vertex set, endpoint)
  in O(2ⁿ n²), then a subset DP in O(3ⁿ)
- vertex connectivity, by minimum separator search

Each is tested against networkx or a brute force on every connected graph up to 7 vertices.

## Credits

- Graph definitions from [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures) (Apache-2.0).
- Built by Rama Krishna Bachu with Claude helper.

License: Apache-2.0.
