### Section 1: Discrepancy Analysis

To analyze the discrepancy \( D_N(\{\alpha_j k / d\}_{k=0}^{N-1}) \), we apply the Erdős–Turán inequality:

\[
D_N(\alpha) \leq C_0 / H + C_1 \sum_{h=1}^H \frac{1}{h \| h \alpha \|},
\]

where \( C_0 = 6 \) and \( C_1 = 4 \) are standard constants. For our case, \( \alpha_j = p + 1/(j\sqrt{2}) \), so we have:

\[
\alpha_j / d = \frac{p}{d} + \frac{1}{jd\sqrt{2}}.
\]

Since \( p/d \) is rational with denominator dividing \( d \), the term \( h \cdot p/d \) contributes a rational part, and the discrepancy depends on the fractional part \( \| h \alpha_j / d \| \). The key sub-question is to bound the partial quotients of \( \alpha_j / d \).

### Section 2: Uniformity in \( j \)

As \( j \to \infty \), \( \alpha_j \to p \), which is rational. This causes the discrepancy to degrade because the orbit becomes more structured. For equidistribution, we need \( N \) such that \( D_N(\alpha_j / d) < \epsilon \). The trade-off is:

\[
N \gtrsim f(j, \epsilon),
\]

where \( f(j, \epsilon) \) could be \( O(j \cdot \text{poly}(1/\epsilon)) \), depending on the partial quotients.

### Section 3: Explicit Bound for \( K(j, \mu(A)) \)

Given \( A \) with width \( w = (n-2)/(n \cdot \max u_j) \), we need:

\[
K(j, \mu(A)) \leq C_2 \left( \frac{1}{w} + \frac{\log(1/\epsilon)}{\epsilon} \right),
\]

where \( C_2 \) is a constant derived from the Erdős–Turán inequality and the partial quotients.

### Section 4: Uniform B Resolution

To ensure \( t_j \leq B \), we must bound \( K(j, \mu(A)) \). If it grows with \( j \), we need to truncate \( j \) to a bounded range. This is feasible by choosing \( j_{\text{max}} \) such that the perturbation \( 1/(j\sqrt{2}) \) is small enough for the limit argument.

### Section 5: Alternative Constructions

Considering alternative perturbations, such as \( \alpha_j = p + \xi/j \) with \( \xi \) having bounded partial quotients (e.g., \( \xi = \sqrt{2} \)), could improve discrepancy bounds. This ensures uniform behavior across all \( j \).

### Section 6: Bottom-Line Conclusion

The Erdős–Turán-based argument works but requires bounding the partial quotients of \( \alpha_j / d \). Given the quadratic nature, the discrepancy grows polynomially with \( j \), necessitating a truncation to ensure uniformity.

**Conclusion:** Option (B) applies, with \( C(j) = O(j^\alpha) \) for some \( \alpha > 0 \).

### Section 7: Residual Gaps

Further work is needed to explicitly bound the partial quotients of \( \sqrt{2}/(2jd) \). This would provide precise constants and ensure the uniformity required for compactness.
