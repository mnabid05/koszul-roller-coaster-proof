# The Koszul Roller Coaster conjecture

Fix any field and any socle degree $d\ge3$. Every prescribed strict ordering of $H_1,\ldots,H_{\lfloor d/2\rfloor}$ occurs as the Hilbert function entries of a standard graded Artinian Gorenstein algebra admitting a quadratic Gröbner basis. Such an algebra is Koszul. Holleben and Nicklasson posed this existence statement for sufficiently large $d$ in Conjecture 5.8. [Published conjecture](https://doi.org/10.1016/j.jpaa.2026.108238) · [Full written proof](notes/roller-coaster.md)

For example, take a complex with five color classes of five vertices each, where a face uses each color at most once. Its face polynomial is $(1+5x)^5$. The resulting degree-six algebra has Hilbert function

$$
(1,3150,3375,2500,3375,3150,1).
$$

The middle entry falls below even the degree-one entry. The general construction lets you choose the entire ordering before constructing the algebra.

## Proof and verification

The proof constructs a positive combination of face-count vectors with a constant contribution in every interior degree. An invertible triangular matrix then lets us adjust the first-half coefficients independently. Disjoint unions of complete multipartite graphs realize the required face counts after a common rescaling.

Lean 4.19 verifies the construction for all permutations, the actual finite face counts, and the shelling criterion for the colored complex. The written proof obtains the algebra and its quadratic Gröbner basis by applying D’Alì and Venturello’s published theorem. That algebraic theorem and its application are outside the Lean formalization. [Formal theorem](Conjectures/RollerFaces.lean) · [Shelling proof](Conjectures/RollerShelling.lean) · [Published algebra theorem, §8](https://arxiv.org/html/2106.05051v2#S8)

From a checkout with the pinned Lean toolchain, run

```sh
lake exe cache get
lake build
lake env lean Audit.lean
python3 scripts/roller_witness.py --self-test
python3 scripts/roller_witness.py 8 3 1 4 2
```

The last command constructs blocks for the order $H_3<H_1<H_4<H_2$ and prints all nine Hilbert coefficients. The self-test checks every ordering for $3\le d\le12$, a total of 1,025 cases.

This is an AI-assisted research proof prepared for independent review. A search of arXiv, journal records, DataCite, GitHub and the public MathDB entry found no prior proof of Conjecture 5.8. Priority and independent expert review are outstanding. [Problem record](https://mathdb.com/p/366913/unconstrained-hilbert-series-conjecture-for-koszul-gorenstei)
