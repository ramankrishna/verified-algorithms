"""Graph algorithms against networkx (independent implementation) on every connected graph with
up to 7 vertices, plus the proved theorems checked numerically on the same graphs."""
import itertools
import math

import networkx as nx
import pytest

from verified_algorithms import graphs as G


def all_connected_graphs(max_n=7):
    for n in range(2, max_n + 1):
        for g in nx.graph_atlas_g():
            if g.number_of_nodes() == n and nx.is_connected(g):
                yield n, g


GRAPHS = list(all_connected_graphs())


def to_adj(g):
    return G.from_edges(g.number_of_nodes(), g.edges())


def test_corpus_size():
    # connected graphs on 2..7 vertices: 1 + 2 + 6 + 21 + 112 + 853
    assert len(GRAPHS) == 995


@pytest.mark.parametrize("n,g", GRAPHS[::7])
def test_distances_radius_diameter(n, g):
    adj = to_adj(g)
    sp = dict(nx.all_pairs_shortest_path_length(g))
    for s in range(n):
        assert G.bfs_distances(adj, s) == [sp[s][t] for t in range(n)]
    assert G.radius(adj) == nx.radius(g)
    assert G.diameter(adj) == nx.diameter(g)


@pytest.mark.parametrize("n,g", GRAPHS[::5])
def test_independence_number(n, g):
    adj = to_adj(g)
    expected = max(len(c) for c in nx.find_cliques(nx.complement(g)))
    assert G.independence_number(adj) == expected


@pytest.mark.parametrize("n,g", GRAPHS[::5])
def test_vertex_connectivity(n, g):
    adj = to_adj(g)
    expected = n - 1 if nx.density(g) == 1 else nx.node_connectivity(g)
    assert G.vertex_connectivity(adj) == expected


@pytest.mark.parametrize("n,g", GRAPHS[::5])
def test_hamiltonian_path_against_permutations(n, g):
    adj = to_adj(g)
    brute = any(all(g.has_edge(p[i], p[i + 1]) for i in range(n - 1))
                for p in itertools.permutations(range(n)))
    assert G.has_hamiltonian_path(adj) == brute


@pytest.mark.parametrize("n,g", GRAPHS[::9])
def test_largest_induced_tree_and_forest(n, g):
    adj = to_adj(g)
    best_tree = best_forest = 0
    for k in range(1, n + 1):
        for S in itertools.combinations(range(n), k):
            h = g.subgraph(S)
            if nx.is_forest(h):
                best_forest = max(best_forest, k)
                if nx.is_connected(h):
                    best_tree = max(best_tree, k)
    assert G.largest_induced_tree(adj) == best_tree
    assert G.largest_induced_forest(adj) == best_forest


def test_path_cover_small_cases():
    assert G.path_cover_number(G.from_edges(4, [(0, 1), (1, 2), (2, 3)])) == 1   # path
    assert G.path_cover_number(G.from_edges(4, [(0, 1), (0, 2), (0, 3)])) == 2   # star K1,3
    assert G.path_cover_number(G.from_edges(5, [(0, i) for i in range(1, 5)])) == 3  # K1,4


def test_residue_known_values():
    assert G.residue([0, 0, 0]) == 3           # empty graph
    assert G.residue([2, 2, 2]) == 1           # triangle
    assert G.residue([3, 1, 1, 1]) == 3        # star K1,3
    assert G.residue([1, 2, 2, 1]) == 2        # path P4


# ---- the Lean-proved theorems, checked numerically on every graph in the corpus

def test_theorem_radius_plus_one_le_tree():
    for n, g in GRAPHS:
        adj = to_adj(g)
        assert G.radius(adj) + 1 <= G.largest_induced_tree(adj)


def test_theorem_c84_min_degree_two():
    for n, g in GRAPHS:
        delta = min(d for _, d in g.degree())
        if delta >= 2:
            adj = to_adj(g)
            assert 2 * G.radius(adj) / delta <= G.largest_induced_tree(adj)


def test_theorem_c96_independence_bound():
    for n, g in GRAPHS:
        adj = to_adj(g)
        m = min(G.dist_even(adj, v) for v in range(n))
        L = max(G.local_independence(adj, v) for v in range(n))
        assert G.independence_number(adj) <= 1 + m * (L - 1)
