# Two ways to see a trace — Section 0.1

**Production status:** script draft; no recording. Approximate duration: 8–10 minutes. The blocks below describe a proposed recording sequence, not video timestamps. This covers Section 0.1 only; the full Chapter 0 lecture remains to be developed.

## Opening visual

Show the matrix with rows $(2,1)$ and $(1,2)$. Highlight the diagonal entries and write $2+2=4$. Then show the vectors $(1,1)$ and $(1,-1)$ being stretched by factors $3$ and $1$.

**Narration:** We have obtained the same number from two different descriptions of a linear transformation. One description reads the diagonal of a matrix. The other reads its eigenvalues. Why do these agree, and what survives if there is no basis of eigenvectors?

## The finite-sum mechanism

Display $\operatorname{tr}(AB)=\sum_i\sum_j a_{ij}b_{ji}$. Animate the pairs $(i,j)$ as a rectangular grid. Traverse first by rows, then by columns; commute the two scalar factors to recognize $\operatorname{tr}(BA)$.

**Narration:** We have only changed the order in which we visit a finite collection of terms. There is no limiting argument. The matrices can even be rectangular, provided the products make sense. This proves `linear-algebra.trace-cyclic`.

Show $A=(1\;2)$ and $B=(3\;4)^{\mathsf T}$. Compute the traces $11$ and $3+8$. Explicitly point out that the two products have different sizes.

## Coordinates change, trace stays

Write $S^{-1}AS$. Treat $S^{-1}A$ as one factor and $S$ as the other. Move the second factor to the front and cancel $SS^{-1}$.

**Narration:** This is why trace belongs to the linear transformation, rather than to the chosen coordinates. The argument is `linear-algebra.trace-similarity`.

## Why eigenvalues appear

Display $\det(tI-A)$. For $n\geq1$, highlight its coefficient of $t^{n-1}$. First obtain $-\sum_i a_{ii}$ from the determinant expansion. Explain that a nonidentity permutation moves at least two indices and therefore loses at least two potential factors of $t$.

Then display $\prod_j(t-\lambda_j)$ and highlight its coefficient $-\sum_j\lambda_j$.

**Narration:** The same polynomial coefficient has two descriptions. Over the complex numbers the polynomial splits into linear factors. Equating coefficients proves `linear-algebra.trace-eigenvalue-sum`, with algebraic multiplicities. For a zero-dimensional space both sums are empty and equal zero.

## The example that tests the hypothesis

Show the matrix with rows $(2,1)$ and $(0,2)$. Compute its characteristic polynomial $(t-2)^2$ and its one-dimensional eigenspace.

**Narration:** The eigenvalue $2$ must be counted twice, even though there is only one independent eigenvector. Our proof did not require diagonalizability. This distinction must also survive in the Lean statement.

## Closing and formalization note

Preview a matrix entry as a value of a kernel and a diagonal sum as a future diagonal integral. Keep the words “additional analytic hypotheses required” visible.

**Narration:** The next section develops the finite-rank model. Infinite sums and integrals will require new justifications. The formalization of this section is still pending: the displayed calculations are prose mathematics, and no Lean proof is being claimed here.

Before recording, review the script against Section 0.1. After recording, add the real URL, captions, and measured timestamps; review any subsequent mathematical edits against both the manuscript and recording.
