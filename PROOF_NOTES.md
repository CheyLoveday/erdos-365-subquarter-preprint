# Lamport proof notes

Read the [preprint](subquarter-preprint.pdf) and [current verification supplement](FORMAL_VERIFICATION.md). These generated notes reproduce the technical sections of the frozen companion, beginning with its goal. See the source snapshot for the dated introduction and historical references.

> Generated reading copy. Edit the authoring source to change the mathematical text.

<!-- Source: source/LAMPORT_COMPANION.md
Source SHA-256: 1183c603225fdb17f6008698b4218cc17c880dd36fe90faeada0ea61576e560a
Generation: python3 -B render.py
-->

## Goal and quantifier discipline

Put $`\theta=333/1400`$. For each $`\varepsilon>0`$ we seek one $`C_\varepsilon>0`$ such that

```math

\forall N\in\mathbb N,\quad N\ge1\implies
\#\{1\le n\le N:n,n+1\text{ powerful}\}
\le C_\varepsilon N^{\theta+\varepsilon}.

```

The identical constant works at every real $`X\ge1`$ by exact flooring. The cutoff bounds the **start** $`n`$, so a pair with $`n=N`$ is included even though $`n+1>N`$. Powerful means positive with every prime exponent at least two; 1 is included, 0 excluded. Squares, proper powers, possible 4-full endpoints, both charts and every Pell return stay in the population. The base exponent is below $`1/4`$; the final exponent is below $`1/4`$ when $`0<\varepsilon<17/1400`$. An arbitrary power loss does not prove the fixed-polylogarithmic Erdős conjecture.

Each uniform constant is chosen before the scales, boxes and finite source population that it bounds. A polynomial, factor, prime assignment or class relation may subsequently depend on the specified data. None may depend on one point while being asserted to hold for an entire class. All counts are upper bounds, so overlaps in covers are harmless; omissions are not.

## Dependency map

``` mermaid
flowchart TD
  S[LP00 Stewart] --> F[LP02–03 fixed fibres and complements]
  P[LP01 original sources] --> F
  P --> R[LP04 residual profile]
  N[LP05 numerical envelope] --> C[LP06–08 intervals and internal coarse polynomial]
  R --> C
  C --> Q[LP09–10 factors, singulars and good primes]
  Q --> V[LP11 modular minor]
  P --> D[LP12 real minor]
  C --> D
  N --> Z[LP13 zero minors and one class relation]
  V --> Z
  D --> Z
  Z --> G[LP14 graph and rulings]
  F --> G
  G --> A[LP15–16 resultant, content, axes and factors]
  A --> T[LP17–18 level and graph counts]
  S --> T
  T --> I[LP19–20 every class and residual box]
  G --> I
  Q --> I
  C --> I
  I --> B[LP21 complete actual box]
  F --> B
  B --> H[LP22 shell]
  H --> U[LP23 all natural starts and finite head]
  U --> X[LP24 real cutoff, same constant]
```

Section 10 of the article appears after its uses for exposition. Logically its scalar inequalities are LP05 and precede both determinant constructions. They use no box count, so there is no cycle. The detailed edge list and reverse consumers are in the generated map.

## LP00

**Established external input.** A primitive integral homogeneous binary form $`F`$ of degree $`3\le r\le11`$, with nonzero discriminant, has at most $`2800r^{1+\omega(|h|)}`$ primitive signed integer solutions of $`F(a,b)=h`$ for $`h\ne0`$.

**By.** Stewart, Theorem 1, printed p.795 and the $`g=|h|`$ specialization on p.796; see the [primary application ledger](FORMAL_VERIFICATION.md#stewarts-theorem). The formal interface expresses nonzero discriminant as separability of the rational affine section of full degree. It does not require irreducibility: the separable cubic used at LP03 may be reducible. This is one published input, not two separate “Stewart” and “Thue” assumptions. Its applications are proved locally; its proof is outside the selected scope.

For the ledger's four-point bound at fixed nonzero signed levels, use the factor selection in §9.2 and [LP16](#lp16). Equal-degree factors must be nonproportional over $`\mathbb Q`$. For a linear factor $`L`$ and a quadratic factor $`G`$, the required condition is $`G\notin\mathbb Q L^2`$.

**Used by:** LP03 and LP17. No external Reuss theorem is used.

## LP01

**Given:** an original positive start. **Assert:** there are unique positive coordinates

```math

n=b^3u^2,\qquad n+1=d^3v^2,\qquad d^3v^2-b^3u^2=1,

```

with $`b,d`$ squarefree, $`\gcd(b,d)=\gcd(u,v)=1`$. The ratios $`(b/d,v/u)`$ determine the start.

**By.** Split each prime exponent into its odd parity contribution and an even remainder. Consecutive endpoints are coprime; each reduced positive fraction recovers its numerator and denominator. There is **no** same-endpoint condition $`\gcd(b,u)=1`$: $`288=2^3\cdot6^2`$ is a counterexample to that extra assumption. The canonical population correspondence, including $`N=0`$, is proved before counting auxiliary objects. Early numerical pilot checks and legacy namespace correspondence are supplementary records, not the proof of this population theorem.

## LP02

**Given:** any fixed kernel product $`D`$, without a smallness assumption. **Assert:** starts $`n\le N`$ with $`bd=D`$ number at most $`1+\lfloor\log_2(2N+1)\rfloor`$.

**By.** The source equation gives
```math
(2n+1)^2-bd(2bduv)^2=1.
```
The proved Pell ordering and growth bound counts all positive returns. The square/kernel-one case is handled, not assumed nonsquare. A fixed reduced kernel ratio fixes $`b,d`$ and hence $`D`$. Summing $`D\le Y`$ pays $`Y`$ times this bound. Flooring real $`Y\ge0`$ and the logarithmic subpower estimate give $`O_\eta(Yx^\eta)`$ uniformly for $`n\le2x`$, $`x\ge32`$. Fixed fibres and aggregate complements are distinct statements; the latter cannot substitute for the former.

## LP03

**Given:** a fixed positive reduced multiplier ratio, hence fixed coprime $`u,v`$. **Assert:** there are at most 8400 starts in that fibre, and $`uv\le Y`$ costs $`O_\eta(Yx^\eta)`$ for $`x\ge32`$ and $`0\le Y\le4x`$.

**By.** The equation $`v^2d^3-u^2b^3=1`$ is a content-one separable cubic at level one. LP00 gives $`2800\cdot3=8400`$, uniformly in $`u,v`$. For natural $`Y\ge1`$, dyadic bins count at most $`Y(1+\lfloor\log_2Y\rfloor)`$ positive multiplier labels; $`Y=0`$ is empty. For a real cutoff use $`\lfloor Y\rfloor`$; the range $`0\le Y<1`$ has no positive labels. Pay the logarithm after summing. No coefficient-dependent Thue constant is acceptable here.

## LP04

**Given:** an inclusive actual box $`x\le n\le2x`$, $`B\le b\le2B`$, $`E\le d\le2E`$. Put $`P=BE=x^\psi`$ and the nominal scales $`U=x^{1/2}B^{-3/2}`$, $`V=x^{1/2}E^{-3/2}`$.

**Assert:** after paying $`bd\le x^\theta`$ and $`uv\le x^\theta`$, a nonempty residual box lies in a fixed compact positive profile range.

**By.** The actual source bounds give $`bd\le4P`$ and $`(uv)^2P^3\le6x^2`$. A uniform large threshold absorbs the fixed factors, yielding
```math
\theta/2\le\psi\le\tfrac23(1-\theta/2),\qquad1-\tfrac32\psi\ge\theta/2.
```
Thus $`m_0=\frac98\psi(1-\frac32\psi)\ge9\theta^2/32>0`$. Empty residual boxes need no witness and are counted as zero. No restriction on the skew $`B/E`$ has been introduced.

## LP05

**Given:** $`0\le\psi\le2/3`$, $`0<\delta\le1`$, $`x`$ above a uniform threshold. Define
```math

m_0=\tfrac98\psi(1-\tfrac32\psi),\quad m=(1+\delta)m_0,
\quad M=\lceil x^m\rceil,\quad T=x^{\theta+\delta}/M,
\quad W=\min(4+6\psi,12-14\psi).

```
**Assert:** the five mixed-error orders $`a_k=(28,21,16,13,12)`$ obey the strict comparison needed at LP13, and $`T`$ grows uniformly.

**By.** On the two sides of $`\psi=2/5`$, the proved continuous polynomial inequalities bound the five branches
```math
(W-k+(28-a_k)m_0)/28
```
by their seam values $`(8/35,333/1400,41/175,61/280,33/175)`$. The maximum is the one-error term. Also $`m_0\le3/16`$. For $`q=\theta+\delta-m`$ this implies
```math
q\ge141/2800+13\delta/16,\qquad
28q-(W-k-a_km)\ge25\delta.
```
Since $`x^m\le M\le2x^m`$, each mixed term divided by $`T^{28}`$ is at most $`2^{16}x^{-25\delta}`$. After increasing a threshold depending on $`\delta`$, $`T\ge x^{141/2800}\ge1`$. These are proved real-profile inequalities, not an extrapolation from sampled profiles. Exact rational controls in the alignment packet check the constants but do not replace those proofs.

## LP06

**Given:** one actual box and $`M\ge1`$. **Assert:** at most $`3M+1\le4M`$ closed original-ratio intervals cover all its sources, each of the form $`a\le b/d\le a(1+1/M)`$ with $`a>0`$.

**By.** Use the explicit finite interval labels in `actual_box_interval_cover`. Closed endpoints may overlap; cardinality subadditivity needs coverage, not disjointness. The same direct intervals determine both chart node ranges later. A separate inverse cover is unnecessary. The older half-open/closed endpoint adapter is retained support, not an additional missing premise of the current direct closed-interval producer.

## LP07

**Given:** a residual profile, one interval from LP06, and its actual finite sources. **Assert:** a rectangular integer evaluation matrix has all maximal square minors zero, with a uniformly bounded rectangle selected before the population.

**By, step 1 — weighted lattice inventory.** For natural exponent indices $`i,j`$, weights $`a,b>0`$ and threshold $`t\ge0`$, a finite positive-part summation gives
```math
\sum_{i<N,j<K}\max(0,t-ai-bj)\le(t+a+b)^3/(6ab).
```
Optimizing its consequence for any $`H`$ distinct exponent pairs gives
```math
\sum(ai+bj)\ge\tfrac23H\sqrt{2abH}-H(a+b).
```
When $`a\le b`$, the last error is at most $`2Hb`$. Numerical weights may tie; the pairs, not their weights, must be distinct.

**By, step 2 — finite column expansion.** Expand each polynomial column over its finite monomial support. A repeated exponent pair gives two identical columns and determinant zero. Apply step 1 only to surviving injective choices. Explicit finite support and coefficient bounds supply a constant depending on the rectangle. The root-column identities express the **actual** cleared entry as $`b^id^{A-i}v^ju^{C-j}`$ for $`0\le i\le A`$, $`0\le j\le C`$; they use the same source error coordinates for all columns.

**By, step 3 — height cancellation.** Put $`H=(A+1)(C+1)`$, $`L=\log x`$, $`a=\log M`$, and
```math
S=\psi L+\log16,\qquad T_{\log}=(1-\tfrac32\psi)L+\log16.
```
The four actual upper heights $`4B,4E,4U,4V`$ retain their ratio coupling. Row and column cancellation bounds each original integer determinant by
```math
K(A,C)\exp\left\{\tfrac H2(AS+CT_{\log})-
\left(\tfrac23H\sqrt{2aLH}-2HL\right)\right\}.
```
In particular the cancellation is valid for arbitrary kernel skew.

**By, step 4 — choose the rectangle before the varying data.** The uniform rectangular lemma assumes $`c_0L\le S,T_{\log}\le2L`$, $`a\le L`$, and
```math
\tfrac98(1+\sigma)S T_{\log}\le aL.
```
Here $`c_0>0`$ is fixed by the compact profile; actual logarithmic slack supplies $`\sigma=\delta/2`$ after absorbing $`\log16`$. Set $`g=\sqrt{1+\sigma}-1>0`$, choose $`C=\lceil3/(gc_0)\rceil+1`$ and $`A_{\max}=\lceil2C/c_0\rceil`$. For each varying profile choose $`A=\lfloor CT_{\log}/S\rfloor\le A_{\max}`$. Then
```math
H\ge C^2T_{\log}/S,\quad \tfrac H2(AS+CT_{\log})\le HCT_{\log},
```
and the square-root decay is at least $`HC\sqrt{1+\sigma}\,T_{\log}`$. Since $`Cgc_0\ge3`$, the net exponent is at most $`-HL\le-L`$. There are only finitely many $`K(A,C)`$, so one later threshold makes all $`K(A,C)e^{-L}<1`$.

**Conclusion.** Every such determinant is an integer of absolute value less than one, hence zero. Degrees and constants are fixed before $`x`$, the profile and the source population; choosing $`A`$ from the bounded range does not change that order. No external cover theorem or assumed rank deficiency supplies this result.

## LP08

**Given:** the actual integer rows of LP07. **Assert:** one nonzero integer polynomial vanishes at every point of the interval population, with degree $`\le D`$ and coefficient bound $`Kx^N`$, where $`D,N,K`$ are uniform.

**By.** Among nonsingular matrices completed with actual rows and standard unit rows, maximize the number of actual rows. At least one unit row remains, since every all-actual maximal minor is zero. Its nonzero adjugate column annihilates every actual row: otherwise replacement would increase the maximal number. Cofactors are bounded by $`(H-1)!L_{\rm entry}^{H-1}`$. Distinct rectangular monomials turn the nonzero coefficient vector into a nonzero polynomial. Empty populations, duplicate rows and every smaller rank are covered.

Choose $`D=A_{\max}+C`$, $`H_{\max}=(A_{\max}+1)(C+1)`$ and $`N=D(H_{\max}-1)`$. The actual entries are at most $`(3x)^D`$, so $`K=(H_{\max}-1)!3^N`$ suffices. The polynomial may depend on the population; these bounds do not. The dependency display following Proposition 4.2 orders these choices together with LP09–LP13: fixed $`\delta`$, finite rectangle range and constants, coarse/factor bounds, witness exponent and prime-list length, then one maximum threshold, all before varying boxes and populations. The rectangle varies only within that finite range; the polynomial may vary with the population. Prime values later vary with $`T`$, while their number and size multiples stay fixed. Uniformity is for fixed positive slack, with no assertion uniform as $`\varepsilon\downarrow0`$.

## LP09

**Given:** the nonzero polynomial from LP08. **Assert:** at most $`D`$ primitive rationally irreducible curve factors cover its rational zero set, with uniform polynomial height; each has at most $`2D^3`$ singular rational points.

**By.** Separate scalar content from positive-degree factors. The substitution $`(i,j)\mapsto i+(D+1)j`$ is injective on the required support, preserves divisibility and coefficient control, and has degree at most $`D(D+1)`$. Integral factor-height bounds therefore apply uniformly. For singular points, use a nonzero actual-degree derivative resultant of degree at most $`2D^2`$, then at most $`D`$ roots per fibre. The exceptional scalar-linear/vertical case cannot supply singular points. LP01 transfers the rational count to starts. Absolute irreducibility and a general plane Bézout premise are unnecessary.

## LP10

**Given:** one of these factors and a nonsingular actual source. **Assert:** every such source can be assigned to a good prime from one bounded list of primes of size comparable to $`T`$; the total smooth residue labels are $`O(T)`$.

**By.** Clear the nonzero selected partial derivative and multiply by $`du`$ to obtain a nonzero integer witness of polynomial height. A prime not dividing this witness preserves both denominators and the chosen unit partial. Repeated Bertrand intervals supply a fixed-length list with all $`p\ge T`$. If every prime were bad, their product would divide the nonzero witness and exceed its bound. Assign the first good prime. A nonzero reduced polynomial has at most $`Dp`$ zeros; a zero reduction has no smooth labels, since all its partials also vanish. Summing the bounded list costs $`O(T)`$.

Each class fixes the interval, factor, prime and residue label. No globally good prime, occupied-class saving or mixing of unrelated residue data is assumed.

## LP11

**Given:** eight members of one smooth class. **Assert:** $`p^{28}`$ divides their original integer row determinant, in either selected chart.

**By, step 1 — finite implicit correction.** Keep the original interval, coarse factor, prime and residue fixed. Work in $`R=\mathbb Z/p^{28}\mathbb Z`$ with the rational coordinates $`(b/d,v/u)`$, reducing their denominators by unit inverses, and select one actual source centre $`z_0`$ from the tuple. The free modular coordinate need not be a real root coordinate. Let $`i`$ be a unit-partial coordinate, let $`j`$ be the other coordinate, and fix $`a_i=(\partial_i F(z_0))^{-1}`$ in $`R`$. Starting with $`q_0(X)=0`$, define the ordered point $`Y_k(X)`$ by its two indexed coordinates and set
```math

(Y_k(X))_i=z_{0,i}+q_k(X),\qquad (Y_k(X))_j=z_{0,j}+X,\qquad
q_{k+1}(X)=q_k(X)-a_i F(Y_k(X)).

```
Here $`F`$ always takes its arguments in the original $`(s,t)`$ order. Since $`F(z_0)=0`$, induction gives $`q_k(0)=0`$. For another actual point $`z`$ of the class let $`x=z_j-z_{0,j}`$ and $`e_k=z_i-z_{0,i}-q_k(x)`$. Initially $`p\mid e_0`$, and $`Y_k(x)\equiv z_0\pmod p`$ since $`p\mid x`$. Expanding $`F(z)=0`$ about $`Y_k(x)`$ in coordinate $`i`$ gives, for some $`c\in R`$,
```math
e_{k+1}=\bigl(1-a_i\partial_iF(Y_k(x))-a_ic e_k\bigr)e_k.
```
Whenever $`p\mid e_k`$, the parenthesized factor vanishes modulo $`p`$. Thus $`p^{k+1}\mid e_k`$ by induction, and after 27 corrections the error is zero in $`R`$. One polynomial works for every point in that residue class; there is no infinite series or convergence premise.

**By, step 2 — evaluation determinant over a ring.** For eight parameter values $`z_i=pw_i`$, divide each column polynomial by the monic polynomial $`\prod_{i=1}^8(Z-z_i)`$. Remainders have degree less than eight and the same evaluations. Thus the evaluation matrix is the product of the Vandermonde matrix and an $`8\times8`$ coefficient matrix. Its order-$`j`$ Vandermonde column has factor $`p^j`$. The determinant has factor $`p^{0+1+\cdots+7}=p^{28}=0`$ in $`R`$. Repeated nodes and zero divisors cause no problem: no node difference is inverted or cancelled. No step excludes the primes 2 or 3.

**By, step 3 — restore the same integer matrix.** The direct and inverse row denominators are $`d^3u`$ and $`du^3`$; they are units since $`p\nmid du`$. Multiplying them back proves divisibility of the original integer determinant. Fractional real roots have not been used in this ring calculation. The centre may vary with the tuple; the conclusion is vanishing for every tuple, which is the input to LP13's single whole-class relation.

## LP12

**Given:** those same original integer rows and the common original interval. **Assert:**
```math
|\Delta|\le C_2\sum_{k=0}^4x^{W(\psi)-k}M^{-a_k}.
```

**By, step 1 — identify the original minor.** For the original interval start $`\alpha`$, set
```math
w_D=(s/\alpha)^{1/2},\quad\beta_D=t/\alpha^{3/2}-w_D^3,\qquad
w_I=(t/\alpha^{3/2})^{1/3},\quad\beta_I=s/\alpha-w_I^2.
```
Use the explicitly ordered rows $`r_D,r_I`$ in §6.1. Their exact normalization identities are
```math
\Delta_D=(\prod_i d_i^3u_i)\alpha^{18}\det(r_D)_i,\qquad
\Delta_I=(\prod_i d_i u_i^3)\alpha^{22}\det(r_I)_i.
```
The inverse generic scale is $`\alpha^{3/2}`$, whose column product is $`(\alpha^{3/2})^{44/3}=\alpha^{22}`$. The source equation gives $`w_I^6=(s/\alpha)^3(1+1/n)`$. Since $`1\le M\le x\le n`$, both chart nodes lie in $`[1,1+1/M]\subset[1,2]`$; both errors have absolute value at most $`8/x`$. Thus the same original cover supplies both compact chart ranges, including closed endpoints.

The exported `CF11ActualIntervalNodes` target records $`1\le w\le2`$ and $`w\le1+3/M`$, which suffice for the determinant estimate with a fixed constant. The local `hnodes` argument in `actual_interval_nodes` proves the sharper $`1+1/M`$ bound before relaxing it; this is a [sufficient formal variant](FORMAL_VERIFICATION.md#formal-variants), not a separate exported sharper theorem.

**By, step 2 — bound the normalized determinant.** A mixed determinant with $`k`$ error rows is divisible by the node differences within the main-row and error-row groups. Their number is $`\binom{8-k}{2}+\binom{k}{2}`$, giving the five orders in LP05. Error rows occupy four columns, so terms with at least five error rows vanish. No derivatives of a row-dependent error function are assumed.

The two clearing-scale calculations displayed in [§6.1 (PDF p. 9)](subquarter-preprint.pdf) substitute $`U=x^{1/2}B^{-3/2}`$ into $`E^{24}U^8(B/E)^{18}`$ and $`E^8U^{24}(B/E)^{22}`$, giving $`x^4P^6`$ and $`x^{12}/P^{14}`$; taking the better chart produces $`x^W`$. Both charts inherit bounded nodes from the original interval. All fixed factors enter $`C_2`$ uniformly; neither bounded skew nor a second interval family is needed.

## LP13

**Given:** LP05, LP11 and LP12. **Assert:** one nonzero integer relation of bidegree at most $`(3,1)`$ or $`(1,3)`$, with coefficients bounded by $`x^{14}`$, holds for every member of the class.

**By.** A uniform threshold makes $`5C_2\,2^{16}x^{-25\delta}<1`$, so $`|\Delta|<T^{28}\le p^{28}`$. Divisibility and size concern the same original determinant; hence every eight-row minor is zero. Apply the maximal actual/unit completion argument from LP08 with eight columns; the [integer relation lemma in Proposition 4.2 (PDF p. 5)](subquarter-preprint.pdf) gives its ordinary proof, including why every further row is annihilated. The actual row height is at most $`9x^{11/6}`$, so the cofactor bound is $`7!9^7x^{77/6}\le x^{14}`$ above one threshold. This includes empty classes, repeated rows, lower ranks and fewer than eight points. The relation is chosen before all class members, not fitted separately to each tuple.

## LP14

**Given:** the entire-class relation in its selected chart. **Assert:** every class source lies on one of at most three coordinate rulings or on a graph with uniformly bounded coprime sections; degree-zero graphs are another ruling.

**By.** Write $`G(s,t)=P_0(s)+tQ_0(s)`$, remove their primitive common integral factor $`D_0`$, and put $`P_0=-D_0A`$, $`Q_0=D_0B`$. Then $`A,B`$ are coprime over $`\mathbb Q[s]`$, have degree at most three, and have height at most $`x^{15}`$. A root of $`D_0`$ fixes one coordinate. A zero section leaves only ruling sources; off the common roots positivity makes both section evaluations nonzero. If the graph degree is zero it fixes the other coordinate. LP02 and LP03 pay all ruling orientations. This argument applies to every class without deciding whether $`F`$ divides $`G`$ or counting a coarse component just once globally.

## LP15

**Given:** a mixed graph with $`r=\max(\deg A,\deg B)\in\{1,2,3\}`$ and an actual canonical source on its graph branch, with its primitive parameter $`(x_1,y_1)`$ in the selected chart. **Assert:** its full-degree homogeneous resultant $`R\ne0`$ has $`|R|\le720x^{90}`$, and the positive evaluation gcd $`g`$ divides $`R`$. The primitive pullback level is nonzero and satisfies $`ch=\sigma g^\ell`$, with $`c>0`$, $`\ell\in\{2,3\}`$ and $`\sigma\in\{-1,1\}`$.

**By.** Homogenize both sections at the same actual maximum degree. Rational coprimality excludes finite common roots; a nonzero leading coefficient at degree $`r`$ excludes a common infinity root. Integral Sylvester adjugate identities give both $`R x_1^{2r-1}`$ and $`R y_1^{2r-1}`$ in the section ideal. Primitivity then gives $`g\mid R`$, including axis parameters. The determinant has size at most six, yielding the stated height bound. The $`288/289`$ inverse control uses $`A=6Z-5W`$, $`B=6W`$ at $`(17,6)`$: section values 72 and 36 give $`g=36`$, the full homogeneous resultant is 36, and the content-one pullback value is $`46656=g^3`$. The affine resultant of $`6T-5`$ and 6 would be only 6, so it cannot replace the full resultant.

The positive primitive partner is the signed evaluated section pair divided by $`g`$. Substitution into the source equation gives the direct form $`y_1^3A^2-x_1^3B^2=g^2`$ or the inverse form $`x_1^2B^3-y_1^2A^3=\sigma g^3`$. Fix the integer content $`c`$ and primitive part $`Q`$ of this form before varying parameters. At every admitted nonzero value, $`c>0`$ and $`cQ(x_1,y_1)=\sigma g^\ell`$. Thus $`h=Q(x_1,y_1)\ne0`$ and $`|h|\mid g^\ell`$.

The level identity requires the actual source equation. An arbitrary primitive parameter on a graph need not be admitted: for $`A=X`$, $`B=1`$, direct parameter $`(2,1)`$ has $`g=1`$ and pullback value $`-4`$, not $`\pm g^2`$. The resultant/gcd statement alone does not imply the level identity.

The assertion $`c\mid R`$ would be false. For $`A=2(X-1)`$, $`B=2(X-2)`$, $`R=-4`$ and parameter $`(3,1)`$, the values are $`(4,2)`$, $`g=2`$, and the inverse pullback has content 8 and reduced level 1. Negating both sections gives a negative reduced level. Both controls belong to the intended domain.

## LP16

**Given:** the pullback of LP15. **Assert:** a fixed primitive factor choice yields either a separable full-degree affine factor of degree 3–11 or a fixed low-degree pair of one of three types: two nonproportional linear factors; a linear factor $`L`$ and a quadratic factor $`G`$ with $`G`$ not rationally proportional to $`L^2`$; or two nonproportional quadratic factors. Homogeneous factors at infinity are included.

**By, step 1 — screen axes before using abc.** Mixed graphs have $`1\le r\le3`$ and both sections nonzero; zero-section cases and graphs with both sections constant have already gone to LP14's rulings. A mixed graph may have one nonzero constant section, as in the $`288/289`$ control of LP15. The nonzero homogeneous degrees are exactly $`N_D=2r+3\in\{5,7,9\}`$ and $`N_I=3r+2\in\{5,8,11\}`$. The direct orders $`2a`$ and $`3+2b`$ differ in parity; the inverse orders $`3a`$ and $`2+3b`$ differ modulo 3. Hence there is no cancellation. Coprimality and the actual maximum degree give axis multiplicities at most three directly and two inversely, including a missing leading affine term.

Suppose $`H=c_0G^k`$ with homogeneous degree $`d\in\{1,2\}`$. Nonzero $`H`$ and positive degree exclude zero scalar, zero form and zero exponent. Then $`dk=N`$. Directly, odd $`N`$ forbids $`d=2`$, while $`d=1`$ gives $`k\ge5>3`$. Inversely $`dk\ge5`$ gives $`k\ge3>2`$. Thus $`G`$ has neither axis factor. Only at this point do we obtain $`P(T)=G(T,1)`$ of full degree $`d`$ with $`P(0)\ne0`$, and $`H(T,1)`$ of full degree $`N`$.

**By, step 2 — exclude that pure power.** Put $`a=A(T,1)`$ and $`b=B(T,1)`$. Since $`H(0,1)\ne0`$, $`a(0)\ne0`$; rational coprimality of $`a,b`$ then makes $`a`$ coprime to $`Tb`$. The original summands $`a^2,T^3b^2`$, or $`T^2b^3,a^3`$, and their nonzero difference are pairwise coprime. Apply polynomial abc to this original triple. Its radical support lies in $`abTP`$, giving
```math
N+1\le\deg a+\deg b+1+d,\qquad N\le2r+2.
```
This contradicts $`N_D=2r+3`$ and $`N_I=3r+2`$ for $`r\ge1`$. The small form can be a reducible quadratic; no irreducibility premise is used.

**By, step 3 — exhaust factors.** Apply the five-case table in §9.2 to $`q(T)=Q(T,1)`$: high affine factor; infinity padding with a low affine factor; two nonassociate low affine factors; the forbidden sole low factor without padding; or the forbidden constant affine section $`Q=c_0W^N`$. Each chosen affine factor is homogenized at its full affine degree. In the infinity branch it is not divisible by $`W`$; otherwise nonassociation and irreducibility give nonproportionality, including the exclusion of a quadratic proportional to the square of the selected linear factor. These are fixed divisors of one $`Q`$, selected before signed levels or subsets. The explicit exclusions make the table exhaustive.

## LP17

**Given:** a nonzero signed level $`h`$ of the fixed primitive pullback. **Assert:** each factor branch has a coefficient-uniform bound.

**By.** In the high branch, Gauss's lemma supplies content one and rational irreducibility supplies separability of the full-degree affine factor. Its nonzero signed value divides $`h`$. LP00 and at most $`2\tau(|h|)`$ signed divisors give at most $`61600\tau(|h|)11^{\omega(|h|)}`$ points.

For a low pair, two fixed nonzero signed factor levels produce a nonzero homogeneous eliminant of degree at most two. It has at most two projective zero directions including infinity, with at most two primitive signs per direction. Thus there are at most four points per level pair (two in the linear-linear case). Paying both signed divisor lists gives at most $`16\tau(|h|)^2`$. Finiteness alone, or a constant depending on the factor coefficients, would not suffice.

## LP18

**Given:** one fixed graph/chart/content, a finite set of parameters admitted by actual canonical sources on that graph branch, and LP17. **Assert:** this set has at most $`123232\tau(|R|)^8`$ primitive parameters, hence the graph branch contains $`O_\eta(x^\eta)`$ original starts.

**By.** For each $`g\mid R`$ and sign $`\sigma`$, the fixed equation $`ch=\sigma g^\ell`$ permits at most one $`h`$, since $`c\ne0`$. There are at most $`2\tau(|R|)`$ labels. Moreover
```math
\tau(|h|)\le\tau(|R|)^3,\qquad
11^{\omega(|h|)}\le16^{\omega(|R|)}\le\tau(|R|)^4.
```
All graph/chart/pullback/content/factor choices precede these labels. The exact bound is
```math
2\tau(|R|)[16\tau(|R|)^6+61600\tau(|R|)^7]\le123232\tau(|R|)^8.
```
Here $`\tau(|R|)\ge1`$ pays the low branch into the seventh power before the label factor. A nonintegral reduced level yields an empty label, not another choice of $`h`$. Do not introduce an independent new list of reduced levels after fixing a label.

The locally proved divisor subpower estimate, with exponent $`\eta/720`$ before the eighth power and $`|R|\ll x^{90}`$, gives $`x^\eta`$. The graph parameter recovers both source ratios, so LP01 injects original starts into this count. Counting auxiliary points has not silently replaced the goal population.

## LP19

**Given:** the complete class of LP13. **Assert:** its starts cost $`O_\eta(x^\eta)`$ uniformly before the class data.

**By.** LP14 pays every ruling with LP02/LP03 and the mixed graph with LP18. The graph height and degree constants are uniform. Sum the bounded branch inventory. This is the conservative every-class route: there is no assumed proper-intersection saving and no unproved charge per common component.

## LP20

**Given:** one original interval and all its coarse factors. **Assert:** its starts cost $`O(Tx^\eta)`$; the residual box costs $`O(MTx^\eta)`$, hence also the manuscript's weaker $`O(MTx^\eta+M)`$.

**By.** LP09 pays boundedly many singular points; LP10 supplies $`O(T)`$ smooth labels, each paid by LP19. Since $`T\ge1`$, $`x\ge1`$, absorb the singular constant into $`Tx^\eta`$. There are boundedly many factors and at most $`4M`$ intervals by LP06. LP08 supplies a polynomial for every actual interval population, so no existence premise remains. Exact $`MT=x^{\theta+\delta}`$ then gives $`O(x^{\theta+\delta+\eta})`$.

The old `PaperTargets/IntervalCounts.lean` introductory comment calls the coarse producer and aggregation “still-open”. That is a historical status comment in hash-pinned source, superseded by the actual `GenericCoarse`, `BoxCounts` and `GlobalCounts` producers linked in the map. Its bytes are preserved with the native evidence; it is not a mathematical premise or a current gap.

## LP21

**Given:** any requested box loss $`e>0`$. **Assert:** every actual box has $`O_e(x^{\theta+e})`$ starts, including both complements and an empty residual set.

**By.** Set $`h=e/3`$, $`\delta=\min(1,h)`$ and class loss $`\eta=h`$. Then $`\delta+h\le2e/3\le e`$. LP02/LP03 pay the two small-product complements by $`O_h(x^{\theta+h})`$; LP04 and LP20 pay everything remaining. The union covers every actual source. Thresholds and constants precede all boxes and finite source functions. Intersections only overcount.

## LP22

**Given:** a shell loss $`s>0`$. **Assert:** all selected original starts in $`[x,2x]`$ cost $`O_s(x^{\theta+s})`$ for all sufficiently large $`x`$.

**By.** LP01 bounds the kernel ranges. Dyadic labels cover both kernel coordinates, including kernel one, with two logarithmic costs. Use LP21 with loss $`s/2`$ and pay each logarithm by $`x^{s/4}`$. Sum over all boxes, irrespective of skew. Uniformity before boxes is essential here.

## LP23

**Given:** final $`\varepsilon>0`$. **Assert:** the stated bound holds for every natural cutoff $`N\ge1`$ with one constant, including the finite initial range.

**By.** Request LP22 with $`s=\varepsilon/2`$: equivalently, box loss $`\varepsilon/4`$ and kernel-label losses $`\varepsilon/8`$ each. Cover every positive start $`n\le N`$ by its dyadic start shell. Each large shell is at most $`C_sN^{\theta+\varepsilon/2}`$. Each small shell is bounded by a fixed finite head, absorbed into that same coefficient since $`N\ge1`$. There are $`O(1+\log N)`$ start labels; pay this third logarithm by $`N^{\varepsilon/2}`$. LP01 identifies the resulting source count with `PairCount`. No sharper geometric shell sum or deleted finite head is required.

## LP24

**Given:** real $`X\ge1`$. **Assert:** the exact real population has the bound with the same constant.

**By.** Put $`N=\lfloor X\rfloor\ge1`$. The set of positive integer starts $`n\le X`$ is exactly that for $`n\le N`$. LP23 and monotonicity of the positive power, using $`N\le X`$, finish the argument. A ceiling or a restriction on the second endpoint would change the population and is not used.

## Alternative and failed-route register

| Historical shortcut or alternative | Current disposition |
|----|----|
| External Reuss cover (`EXT.R`) | Replaced by LP06–LP08's proved specialized finite-source construction. |
| General plane Bézout (`STD.BEZOUT`) | Replaced by actual-degree resultants and explicit low-degree elimination in LP09/LP17. |
| Proper/common intersection, bidegree and component inventories (`G.PROPER`, `G.BIDEGREE`, `I.PROPER`, `I.COMMON`, `I.CASES`) | Seven literals in total remain unused, not proved. LP14–LP20 count every class and pay the conservative inventory. |
| Irreducible-only Thue input | Insufficient for the selected fixed multiplier cubic; LP00 uses the published separable statement. |
| Assume content divides the resultant | False at the explicit content-8/resultant-4 example; LP15–LP18 fix content and charge admitted signed levels. |
| Remove axes, infinity, later returns or the finite head | Would change or incompletely count the goal. LP02/LP16/LP23 retain them. |
| One good prime for every point, or one relation for a selected tuple | Insufficient. LP10 assigns primes source by source; LP13 obtains one relation for the entire fixed class. |
| Fixed polylogarithmic bound from an arbitrary power loss | Not established. No problem closure, novelty or publication decision follows. |

The six missing historical figure assets and their old captions are not premises. The current dependency diagram is sourced by the map below this companion; it does not reconstruct or endorse those missing historical figures. All 78 historical nodes and 12 joins keep their individual dispositions in the map rather than being reclassified as 90 proved literal statements.
