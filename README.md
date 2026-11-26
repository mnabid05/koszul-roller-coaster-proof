# The Koszul Roller Coaster conjecture

**Lean 4 verifies Holleben and Nicklasson’s Conjecture 5.8.** Over every field and in every socle degree $d\ge3$, there is a standard graded Artinian Gorenstein Koszul algebra whose Hilbert function entries $H_1,\ldots,H_{\lfloor d/2\rfloor}$ occur in any prescribed strict order. The paper asks for sufficiently large $d$. [Final Lean theorem](Conjectures/RollerConjecture.lean) · [Published conjecture, §5](https://arxiv.org/html/2502.00155v2#S5) · [Written proof](notes/roller-coaster.md)

For example, take a complex with five color classes of five vertices each, where a face uses each color at most once. Its face polynomial is $(1+5x)^5$. The resulting degree-six algebra has Hilbert function

$$
(1,3150,3375,2500,3375,3150,1).
$$

The middle entry falls below even the degree-one entry. The general construction lets you choose the entire ordering before constructing the algebra.

## Proof and verification

The proof constructs a positive combination of face-count vectors with a constant contribution in every interior degree. An invertible triangular matrix then lets us adjust the first-half coefficients independently. Disjoint unions of complete multipartite graphs realize the required face counts after a common rescaling.

The Lean proof builds the algebra, computes the dimensions of its homogeneous pieces, and identifies its top piece with the one-dimensional socle. It proves Koszulness by showing that the normalized bar cohomology of the residue field vanishes off the diagonal. The bar differential uses multiplication in the constructed algebra. The axiom audit on the final theorem permits only Lean’s standard axioms of propositional extensionality, classical choice and quotient soundness. [Algebra and Hilbert function](Conjectures/RollerAlgebraRealization.lean) · [Bar differential on the actual algebra](Conjectures/RollerKoszulAugmentation.lean) · [Koszul filtration](Conjectures/RollerWhiskeredKoszul.lean) · [Axiom audit](Audit.lean)

The written proof also derives a quadratic Gröbner basis from a theorem of D’Alì and Venturello. That stronger assertion is outside the Lean theorem for Conjecture 5.8. [Published Gröbner basis theorem, §8](https://arxiv.org/html/2106.05051v2#S8)

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
