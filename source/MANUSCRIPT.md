---
title: "A Subquarter Exponent for Consecutive Powerful Numbers"
author: "Chey Loveday"
date: "23 November 2026"
lang: en-GB
---

# Abstract

Let $S(X)$ count positive integers $n\le X$ for which each prime dividing $n$ or $n+1$ occurs with exponent at least two in the integer it divides. For every $\varepsilon>0$ we prove $S(X)\ll_\varepsilon X^{333/1400+\varepsilon}$, improving the exponent in Reuss's bound $X^{29/100+\varepsilon}$ and the $1/4+\varepsilon$ exponent of a contemporaneous preprint. An approximate determinant places the sources on an auxiliary curve on each interval of a common cover. Real and modular estimates of the same integer minor give a relation on each full smooth residue class. We count the sources on the resulting graphs and coordinate rulings using homogeneous resultants, Pell growth and Stewart's coefficient-uniform bound for primitive solutions of binary form equations. Erdős's fixed-power logarithmic question remains open.

# 1. Counting function and conclusion

A natural number $n$ is powerful when $n>0$ and every prime divisor $p$ satisfies $p^2\mid n$. Thus $1$ is powerful and $0$ is excluded. Define

$$
S(X)=\#\{n\in\mathbb Z:1\le n\le X,\ n\text{ and }n+1\text{ powerful}\}.
\tag{1.1}
$$

The cutoff applies to $n$, so $n+1$ may exceed $X$. For natural $N$, write $\operatorname{PairCount}(N)=S(N)$. For real $X\ge1$, the exact equality is $S(X)=\operatorname{PairCount}(\lfloor X\rfloor)$.

## Theorem 1.1

For every real $\varepsilon>0$, there exists $C_\varepsilon>0$, independent of the cutoff, such that

$$
\operatorname{PairCount}(N)\le C_\varepsilon N^{333/1400+\varepsilon}
\quad(N\in\mathbb N,\ N\ge1),
\tag{1.2}
$$

and the same constant satisfies

$$
S(X)\le C_\varepsilon X^{333/1400+\varepsilon}
\quad(X\in\mathbb R,\ X\ge1).
\tag{1.3}
$$

The constant includes the finite initial range. The displayed exponent is below $1/4$ for $0<\varepsilon<17/1400$.

Erdős records Mahler's observation that the positive solutions of $x^2-8y^2=1$ supply infinitely many pairs $(8y^2,x^2)$ of consecutive powerful integers [6, p. 31]. Erdős and Erdős–Graham asked about their number and how the pairs arise [6, 7]. The square-endpoint family is one source of examples. Both $12167=23^3$ and $12168=2^3\cdot39^2$ are nonsquares, and Walker gives infinite families with both endpoints nonsquare [8, §3]. The Pell identity in §3 associates a norm-one unit to every source by allowing the product of its squarefree kernels to vary.

The square–cube representation in §2 bounds the number of powerful integers up to $X$ by $\sum_{b\ge1}\sqrt{X/b^3}\ll X^{1/2}$. For pairs at positive shift $\ell$, Chan gives the bounds $O(d_3(\ell)X^{2/5}(\log X)^2)$ and $O_\ell(X^{7/19}\log X)$, where $d_3(\ell)$ counts ordered triples of positive integers with product $\ell$ [3, Theorems 3–4]. The fixed-fibre Pell and Thue counts already enter Chan's argument. Blomer and Schöbel obtain the exponent $61/180$ with arbitrary positive loss for squarefull pairs at fixed nonzero difference [9, Theorem 3]. Their cutoff on both endpoints amounts to shifting $X$ by one at difference one.

At shift one, Reuss gives $S(X)\ll_\varepsilon X^{29/100+\varepsilon}$ [1, Theorem 4], using the approximate determinant method developed by Heath-Brown [5]. Wongcharoenbhorn and Meemark use a determinant-to-Thue step for squarefull values of special quadratic polynomials, including $t^2+\alpha^2$ [10]. At $\alpha=1$, a squarefull value gives the consecutive pair $(t^2,t^2+1)$. Here the first determinant applies to actual finite sources in each interval, the second combines real and modular estimates, and the count covers every graph and ruling branch for all positive starts. The improvement over the exponent in Reuss's Theorem 4 is $73/1400$.

A contemporary preprint by Danny Plymesser, *Counting powerful products of consecutive integers* [11], publicly listed on 19 November 2026, obtains the exponent $1/4+\varepsilon$ for consecutive powerful pairs. Its pair argument uses Reuss's lattice-reduced coordinates and a lifted-curve integral-point estimate; it also treats products of longer blocks of consecutive integers. The present argument differs in its internal rectangular coarse polynomial, its same-integer-minor real and modular comparison, and its resultant/Thue count of every graph and coordinate ruling. The exponent $333/1400$ improves $1/4$ by $17/1400$. We record this contemporaneous work without making a priority assertion.

## 1.1 Proof architecture

Sections 2–3 identify each start by two reduced ratios and count the two small-product complements. A common interval cover carries the remaining sources onto bounded-degree curves (§4). Each nonsingular source is assigned a good prime and a residue (§5). Within each resulting class, the direct and inverse charts give clearing factors $x^{4+6\psi}$ and $x^{12-14\psi}$. Choosing the smaller and applying the modular estimate to the same integer minor yields one relation on the whole class (§§6–7). The scales meet at $\psi=2/5$, where §10 gives the exponent. Sections 8–9 bound every graph and coordinate ruling in that relation. Summing these class bounds over intervals, boxes and shells gives Theorem 1.1 (§§11–12).

# 2. Canonical sources and injection

## Lemma 2.1

Every positive powerful integer has a unique representation $n=b^3u^2$ with positive $b,u$ and squarefree $b$.

**Proof.** For each prime exponent $e\ge2$, put the prime in $b$ precisely when $e$ is odd. The remaining exponent is nonnegative and even. Parity determines $b$ uniquely, then determines the positive $u$. For $n=1$, take $b=u=1$. $\square$

Consequently a consecutive powerful pair has unique positive coordinates

$$
n=b^3u^2,\qquad n+1=d^3v^2,\qquad d^3v^2-b^3u^2=1,
\tag{2.1}
$$

with squarefree $b,d$. Consecutive integers are coprime, so $\gcd(bu,dv)=1$, in particular $\gcd(b,d)=\gcd(u,v)=1$. No condition on $\gcd(b,u)$ or $\gcd(d,v)$ is imposed. The genuine source $288=2^3\cdot6^2$ makes that distinction necessary.

## Lemma 2.2

The positive rational pair $(s,t)=(b/d,v/u)$ determines at most one source and starting integer.

**Proof.** Both fractions are reduced. Their positive numerators and denominators recover $b,d,v,u$, after which (2.1) recovers $n$. $\square$

This injection transfers rational-point and primitive-parameter bounds to original starts. Source choices outside the finite set being counted carry no mathematical hypothesis.

# 3. Fixed fibres, complements and actual boxes

The fixed-fibre bounds also give aggregate bounds after summing over small products. We use $\log$ for the natural logarithm and write $\lfloor\log_2(\cdot)\rfloor$ in exact finite counts.

## Lemma 3.1 — fixed kernel product and kernel ratio

For any natural $D,N$, the number of original starts $n\le N$ having $bd=D$ is at most

$$
1+\lfloor\log_2(2N+1)\rfloor.
\tag{3.1}
$$

There is no smallness assumption on $D$. The canonical source gives the positive Pell solution

$$
(2n+1)^2-bd\,(2bduv)^2=1.
$$

The fibre $D=0$ is empty because $b,d>0$. For $D>0$ put $a=2n+1$ and $y=2Duv$. When $D$ is a square, the positive integers $a-\sqrt D\,y$ and $a+\sqrt D\,y$ have product one, which forces $y=0$ and rules out a source. Otherwise order the positive solutions by $a$. The units $a+y\sqrt D$ increase in that order. The quotient of two successive units is $r_0+s_0\sqrt D>1$ with $r_0,s_0\in\mathbb Z$ and norm one, since the inverse of an integral norm-one unit is its conjugate. Its conjugate is positive and less than one, so $s_0>0$ and $r_0>1$. Thus the next first coordinate is $r_0a+Ds_0y\ge2a$. The number of possible $a\le2N+1$ is at most (3.1), and $a$ determines the start. This covers all Pell returns. A fixed primitive ratio $b/d$ fixes $b,d$, hence $D$, and satisfies the same bound.

Summing over $D\le Y$ gives $Y(1+\lfloor\log_2(2N+1)\rfloor)$ for natural $Y$. In real shell notation, for each $\eta>0$ there is a uniform constant such that the starts $n\le2x$ with $bd\le Y$ cost

$$
O_\eta(Yx^\eta),\qquad x\ge32,\quad Y\ge0.
\tag{3.2}
$$

This also includes fractional and zero $Y$ by flooring. A small-product aggregate alone would not prove the arbitrary fixed-fibre statement (3.1).

## Lemma 3.2 — fixed multiplier ratio and multiplier complement

A fixed positive primitive ratio $v/u$ fixes $u,v$. The binary cubic

$$
F(Z,W)=v^2 W^3-u^2 Z^3
\tag{3.3}
$$

has content one because $\gcd(u,v)=1$. Its affine section $F(Z,1)$ has degree three and is separable because $u,v>0$ and its only possible repeated root is zero, where its value is $v^2$. Equation (2.1) gives $F(b,d)=1$. Applied at this level, the precise Stewart input in Section 9 gives at most $2800\cdot3=8400$ primitive signed kernel pairs, hence at most 8400 original starts. The external statement permits separable reducible cubics, so no irreducibility restriction or separate reducible-case deletion is needed.

Positive multiplier labels with $uv\le Y$ number at most $Y(1+\lfloor\log_2Y\rfloor)$ for integers $Y\ge1$. Indeed, each dyadic $u$-bin has at most $Y$ labels, and there are at most $1+\lfloor\log_2Y\rfloor$ bins. For $Y=0$ there are no labels. For $Y\ge1$ the original starts with $uv\le Y$ cost at most $8400Y(1+\lfloor\log_2Y\rfloor)$. For real $0\le Y\le4x$ this is $O_\eta(Yx^\eta)$, uniformly for $x\ge32$.

## 3.3 Residual boxes

Use inclusive boxes

$$
x\le n\le2x,\qquad B\le b\le2B,\qquad E\le d\le2E,
\tag{3.4}
$$

with $B,E>0$. Closed boundaries may be overcovered in an upper bound; every original start is retained. Put

$$
P=BE=x^\psi,\quad U=x^{1/2}B^{-3/2},\quad
V=x^{1/2}E^{-3/2},\quad UV=xP^{-3/2},\quad
\theta=333/1400.
\tag{3.5}
$$

The source equations and actual box give $bd\le4P$ and $(uv)^2P^3\le6x^2$. Pay $bd\le x^\theta$ and $uv\le x^\theta$ separately using the preceding complements. For all sufficiently large $x$, any remaining nonempty box has one common profile in the compact interval

$$
\theta/2\le\psi\le\tfrac23(1-\theta/2),\qquad
1-\tfrac32\psi\ge\theta/2,\qquad
m_0(\psi)\ge9\theta^2/32,
\tag{3.6}
$$

where $m_0(\psi)=\frac98\psi(1-\frac32\psi)$. The relaxed endpoints pay the fixed factors in the actual inequalities, rather than asserting the ideal nominal bounds literally. An empty residual box costs zero and requires no chosen source or profile.

# 4. Internal finite-source coarse polynomials

Fix $0<\delta\le1$, and set

$$
M=\left\lceil x^{(1+\delta)m_0(\psi)}\right\rceil,
\qquad T=\frac{x^{\theta+\delta}}M.
\tag{4.1}
$$

## Lemma 4.1 — one original interval family

The actual ratios in a box lie in $B/(2E)\le s\le2B/E$. There is a common finite family of positive interval starts $a$, of cardinality at most $3M+1$, whose closed intervals $[a,a(1+1/M)]$ cover that range. The family is selected before individual sources. Each source may be charged through a covering interval; overlap only enlarges an upper bound. The inverse chart uses this same family.

**Proof.** Take $a_j=(B/(2E))(1+j/M)$ for $0\le j\le3M$. Consecutive starts differ by $B/(2EM)\le a_j/M$, and the last start is $2B/E$. Thus the intervals cover the closed range. $\square$

## Proposition 4.2 — specialized internal producer

For each fixed $\delta$, there are a degree bound $D\ge1$, a natural height exponent $H$, a positive constant $C$ and a starting height $x_0\ge32$, before all varying profiles, boxes, intervals and finite source populations, with the following property. For $x\ge x_0$ in the range (3.6), every actual finite source population on one interval of Lemma 4.1 lies on a nonzero integer polynomial $C_I(s,t)$ such that

$$
\deg C_I\le D,\qquad |\operatorname{coeff}_e(C_I)|\le Cx^H.
\tag{4.2}
$$

The polynomial may depend on that finite population. Its degree, height exponent and constants do not. The conclusion is precisely what the finite counting argument needs; it asserts no single polynomial covering an unbounded or arbitrary infinite interval population.

**Integer relation lemma (also used in Section 7).** If an integer matrix with $h\ge1$ columns has entries bounded by $L\ge1$ and every $h$-row determinant vanishes, there is an integer relation $c\ne0$ annihilating every row, with

$$
|c_j|\le(h-1)!L^{h-1}.
\tag{4.3}
$$

**Proof.** Work over $\mathbb Q$. Choose a maximal independent set of $r<h$ actual rows and extend it to an invertible $h\times h$ matrix using standard unit rows. Such an extension exists because the unit rows span $\mathbb Q^h$. Delete one of the added unit rows and take its signed cofactor vector $c$. Its pairing with that unit row is the nonzero determinant of the completed matrix, so $c\ne0$; its pairing with every other completed row is zero. Every actual row lies in the span of the first $r$ rows by maximality, hence is annihilated by this same $c$. Each coefficient is an $(h-1)$-row determinant with entries bounded by $L$, since $L\ge1$, giving (4.3) by the determinant expansion. If $r=0$, the completion is the identity matrix and a unit vector works; this also covers empty populations and $h=1$. $\square$

**Proof of Proposition 4.2.** Fix an interval $[a,a(1+1/M)]$. For a source on it put

$$
z=(s/a)^{1/2}-1,\qquad \beta=t/a^{3/2}-(1+z)^3.
$$

The source equation gives $t^2=s^3(1+1/n)$, so

$$
\beta=(s/a)^{3/2}\bigl(\sqrt{1+1/n}-1\bigr).
$$

Since $n\ge x$ and $1\le s/a\le1+1/M\le2$, we have $0\le z\le1/M$ and $0\le\beta\le8/x$. These bounds hold at the closed endpoints.

Take rectangular columns $(i,j)$ with $0\le i\le A$ and $0\le j\le C_{\rm rect}$, where the degrees will be chosen below. Write $h=(A+1)(C_{\rm rect}+1)$. The source row has the integer entry

$$
b^i d^{A-i}v^j u^{C_{\rm rect}-j}
=d^Au^{C_{\rm rect}} a^{\,i+3j/2}
(1+z)^{2i}\bigl((1+z)^3+\beta\bigr)^j.
$$

In any determinant of $h$ such rows, pull out the factors $d^Au^{C_{\rm rect}}$ from the rows and the factors $a^{i+3j/2}$ from the columns. The product of the latter factors is $a^{h(A/2+3C_{\rm rect}/4)}$. Put

$$
S=\log(16BE),\qquad J=\log(16UV),\qquad
L=\log x,\qquad \lambda=\log M.
$$

The bounds $d\le2E$, $u\le\sqrt{2}\,U$ and $a\le 2B/E$, together with $(B/E)^{3/2}=V/U$, give

$$
d^A a^{A/2}\le(16BE)^{A/2},\qquad
u^{C_{\rm rect}} a^{3C_{\rm rect}/4}\le(16UV)^{C_{\rm rect}/2}.
$$

The total clearing factor is therefore at most $\exp(h(AS+C_{\rm rect}J)/2)$. In particular, the estimate depends on the products of the box scales even for arbitrarily skew boxes.

To bound the normalized determinant, expand each column into its finite sum of monomials $z^p\beta^q$. A choice with a repeated exponent pair gives two equal monomial columns and contributes zero. Distinct pairs can have the same weight. For instance $(1,0)$ and $(0,1)$ tie when the two weight coefficients are both one. Give $(p,q)$ the weight $\lambda p+Lq$, where $\lambda,L>0$ by (3.6) and $x>1$. For any set of $h$ distinct pairs and any $w\ge0$,

$$
\sum_{(p,q)}(\lambda p+Lq)
\ \ge\ hw-\sum_{p,q\ge0}(w-\lambda p-Lq)_+.
$$

On the cell $[p,p+1]\times[q,q+1]$ the function $(w+\lambda+L-\lambda y-Lz')_+$ is at least $(w-\lambda p-Lq)_+$. Its integral over the nonnegative quadrant is $(w+\lambda+L)^3/(6\lambda L)$. Choosing $w=\sqrt{2\lambda Lh}-\lambda-L$ yields

$$
\sum_{(p,q)}(\lambda p+Lq)
\ \ge\ \frac23 h\sqrt{2\lambda Lh}-h(\lambda+L).
$$

If that choice of $w$ is negative, the right-hand side is nonpositive and the inequality follows directly. The normalized entries of a monomial column satisfy $|z^p\beta^q|\le8^q\exp(-\lambda p-Lq)$. The determinant expansion, summed over the finitely many column choices, and the clearing factor above thus give

$$
|\Delta|\le K(A,C_{\rm rect})\exp\!\left(
\frac h2(AS+C_{\rm rect}J)
-\frac23 h\sqrt{2\lambda Lh}
+h(\lambda+L)\right).
$$

Here $K(A,C_{\rm rect})$ absorbs the fixed coefficients, powers of eight and the determinant-expansion factor $h!$. It depends only on the rectangle.

It remains to choose that rectangle uniformly. On (3.6) both $\psi$ and $1-3\psi/2$ are at least $c_*=\theta/2>0$. Hence $S,J$ lie between $c_*L$ and $2L$ for large $x$. By (4.1),

$$
\lambda L\ge\tfrac98(1+\delta)(\psi L)((1-3\psi/2)L).
$$

The ratio of $SJ$ to $(\psi L)((1-3\psi/2)L)$ is at most $(1+\log(16)/(c_*L))^2$. Thus, for $x$ beyond a threshold depending only on $\delta$, we have $\lambda L\ge\tfrac98(1+\delta/2)SJ$. The quadratic $m_0$ has maximum $3/16$, so $M\le2x^{3/8}\le x$ for $x\ge4$ and $\lambda+L\le2L$.

Set $\gamma=\sqrt{1+\delta/2}-1$. Choose an integer $C_{\rm rect}\ge1$ with $C_{\rm rect}\gamma c_*\ge3$, and set $A_{\max}=\lceil 2C_{\rm rect}/c_*\rceil$. For each profile at height $x$, choose $A=\lfloor C_{\rm rect}J/S\rfloor$. This single rectangle serves every interval and tuple in the box and satisfies $0\le A\le A_{\max}$. Since $h\ge C_{\rm rect}^2J/S$ and $AS\le C_{\rm rect}J$,

$$
\frac23 h\sqrt{2\lambda Lh}\ \ge\
hC_{\rm rect}J\sqrt{1+\delta/2}.
$$

The exponent in the bound for $|\Delta|$ is at most $-hC_{\rm rect}J\gamma+2hL\le-hL$. There are finitely many values of $K(A,C_{\rm rect})$. Taking $x$ larger than their maximum makes $|\Delta|<1$ for every tuple. Each $\Delta$ is an integer, hence every such minor vanishes.

Set $D=A_{\max}+C_{\rm rect}$ and $h_{\max}=(A_{\max}+1)(C_{\rm rect}+1)$. The source coordinates $b,d,u,v$ are bounded by $3x$, so each integer matrix entry is at most $(3x)^D$. By (4.3) there is a single integer vector $(c_{ij})\ne0$ annihilating all source rows. Dividing at each row by $d^Au^{C_{\rm rect}}>0$ gives $C_I(s,t)=\sum_{i,j}c_{ij}s^i t^j=0$. The monomials are distinct, so this polynomial is nonzero. Its degree is at most $D$, and (4.2) follows with $H=D(h_{\max}-1)$ and $C=(h_{\max}-1)!\,3^H$. If the population is empty, the relation lemma still gives a nonzero polynomial and the vanishing assertion is vacuous. $\square$

The [proof companion, LP07–LP08](LAMPORT_COMPANION.md#lp07), records the correspondence with the maintained proof sources.

The complete order of choices, including the later prime subdivision, is

$$
\begin{aligned}
\delta &\longrightarrow(C_{\rm rect},A_{\max})
  \longrightarrow\{K(A,C_{\rm rect}):0\le A\le A_{\max}\}\\
&\longrightarrow(D,H,C_{\rm ht})\longrightarrow(K_{\rm wit},L_p)
  \longrightarrow x_0\\
&\longrightarrow(x,\psi,\text{box},\text{interval},\text{population}).
\end{aligned}
$$

Here $C_{\rm rect}$ is the fixed rectangular side degree, $C_{\rm ht}$ the coefficient constant in (4.2), $K_{\rm wit}$ a witness-height exponent and $L_p$ the prime-list length. The chosen $A$ can vary with the profile within its fixed finite range, and the polynomial can vary with the finite population. Factor-height bounds are propagated before $K_{\rm wit},L_p$ are selected. The prime values vary with $T(x,\psi)$; their number and multiplicative range do not. Take the maximum of the finitely many fixed thresholds for coarse production, factor heights, prime assignment, real/modular comparison and the relation height. This order is for each fixed positive slack. No constant uniform as $\varepsilon\downarrow0$, unbounded degree choice, or power of the population size is hidden in it.


## Lemma 4.3 — factors and singular sources

The rational zeros of $C_I$ lie on at most $D$ primitive positive-degree factors irreducible over $\mathbb Q$. Each factor has coefficient height bounded by a fixed multiple of $x^H$, with the multiple determined by $D$ and $C$ in Proposition 4.2. Each such curve has at most $2D^3$ singular rational points.

**Proof.** Factor over $\mathbb Q[s,t]$ and choose primitive integral representatives using Gauss's lemma. Scalar content contributes no zeros, and the sum of the degrees of the distinct positive-degree factors is at most $D$. Write $\operatorname{ht}(P)$ for the largest absolute coefficient of $P$. Under the substitution $s=w$, $t=w^{D+1}$, the exponent $i+(D+1)j$ identifies $(i,j)$ on the degree-$D$ support. The substitution preserves heights on that support and gives polynomials of degree at most $K=D(D+1)$. If $F$ is a primitive factor, its image is an integral factor of the image of $C_I$.

For an integral univariate polynomial $P(w)=a\prod_\alpha(w-\alpha)$ put $\mathcal M(P)=|a|\prod_\alpha\max(1,|\alpha|)$. This quantity is multiplicative and is at least one for a nonzero integer polynomial. The elementary symmetric coefficient formula gives $\operatorname{ht}(P)\le2^{\deg P}\mathcal M(P)$. Jensen's formula gives $\mathcal M(P)$ as the exponential of the mean of $\log|P|$ on the unit circle, so $\mathcal M(P)\le(\deg P+1)\operatorname{ht}(P)$. Applied to an integral factor and its integral quotient, these inequalities bound the factor height by $2^K(K+1)\operatorname{ht}(C_I)$ after substitution. This proves the required height bound.

For the singular count, if $F$ is independent of $t$, every root of the irreducible polynomial in $s$ is simple in characteristic zero. Otherwise let $m=\deg_t F>0$. Viewed as a polynomial in $t$ over $\mathbb Q[s]$, $F$ is primitive by irreducibility, so it is irreducible in $\mathbb Q(s)[t]$. Its derivative $F_t$ is nonzero and coprime to it there. Thus $D_F(s)=\operatorname{Res}_t(F,F_t)$ is nonzero. The Sylvester matrix, taken at the actual degrees $m$ and $m-1$, has size $2m-1$. Its entries have degree in $s$ at most $D$, so $\deg D_F\le(2m-1)D\le2D^2$.

The adjugate of this matrix gives a polynomial identity $D_F=P_F F+Q_F F_t$ with $P_F,Q_F\in\mathbb Q[s,t]$. Hence at a singular rational point $(s_0,t_0)$ one has $D_F(s_0)=0$, including when specialization at $s=s_0$ drops the degree in $t$. For each of at most $2D^2$ such $s_0$, the polynomial $F(s_0,t)$ is nonzero. Indeed, if it vanished identically, $s-s_0$ would divide $F$, contradicting irreducibility and $\deg_t F>0$. Each fibre therefore has at most $D$ possible rational roots. This gives $2D^3$ singular rational points using only irreducibility over $\mathbb Q$. Lemma 2.2 transfers the count to original starts, and the interval and factor inventories give $O_\delta(M)$ singular starts in total. $\square$

# 5. A source-wise bounded union of good primes

For a nonsingular source on $F$, choose a partial derivative $F_i$ with $F_i(b/d,v/u)\ne0$. If $D$ is the uniform degree bound, the number $du\,d^D u^D F_i(b/d,v/u)$ is a nonzero integer. Its magnitude is at most $C_1x^{H_1}$ with $C_1,H_1$ fixed by the degree and height bounds, since each source coordinate is at most $3x$.

Select a fixed bounded list of distinct primes at controlled constant multiples of $T$, with each prime at least $T$ and with product greater than the witness bound. Such a bounded list is possible because Section 10 proves a uniform positive power lower bound for $T$; repeated Bertrand intervals give both the lower and upper size bounds. The list length and interval constants precede the individual source and factor coefficients within the fixed bounds.

If every listed prime were bad for a nonsingular source, all would divide its nonzero witness, contradicting the product bound. Assign the source to its first good prime. Goodness means $p\nmid du$ and a relevant reduced partial is nonzero. For each selected prime, the nonzero reduced degree-$D$ curve has $O_D(p)$ smooth labels. If the polynomial reduction is identically zero, all its partials vanish and there are no smooth labels; no degree-times-prime bound is asserted for all zeros of the zero polynomial. The bounded union therefore has $O_\delta(T)$ assigned labels per factor.

One smooth class has one fixed original interval, one fixed coarse factor $F$, one fixed selected prime $p$ and one common residue $z_0\in\mathbb F_p^2$. Its members are the sources assigned to that prime whose two reduced ratio coordinates equal $z_0$. Only sources in this common class are combined in a minor. Source-wise prime selection does not authorize a determinant mixing different primes, factors or residues. The construction never assumes a prime good for every source simultaneously.

# 6. The same integer minor in two estimates

The direct and inverse integer rows are

$$
R_{31}=(d^3u,bd^2u,b^2du,b^3u,d^3v,bd^2v,b^2dv,b^3v),
\tag{6.1}
$$

$$
R_{13}=(du^3,du^2v,duv^2,dv^3,bu^3,bu^2v,buv^2,bv^3).
\tag{6.2}
$$

Choose the direct matrix when $4+6\psi\le12-14\psi$, and the inverse matrix otherwise. The real and modular bounds both apply to the integer determinant $\Delta$ of that chosen matrix.

<a id="real-bound"></a>

## 6.1 Real bound

Fix an original interval $[\alpha,\alpha(1+1/M)]$, with $\alpha>0$, and an ordered eight-tuple in the selected smooth class. Write $s_i=b_i/d_i$, $t_i=v_i/u_i$. Define

$$
\begin{aligned}
w_{D,i}&=(s_i/\alpha)^{1/2},&
\beta_{D,i}&=t_i/\alpha^{3/2}-w_{D,i}^3,\\
w_{I,i}&=(t_i/\alpha^{3/2})^{1/3},&
\beta_{I,i}&=s_i/\alpha-w_{I,i}^2.
\end{aligned}
$$

The ordered normalized rows, in the column orders of (6.1) and (6.2), are

$$
\begin{aligned}
r_D(w,\beta)&=(1,w^2,w^4,w^6,w^3+\beta,w^5+\beta w^2,w^7+\beta w^4,w^9+\beta w^6),\\
r_I(w,\beta)&=(1,w^3,w^6,w^9,w^2+\beta,w^5+\beta w^3,w^8+\beta w^6,w^{11}+\beta w^9).
\end{aligned}
$$

Taking row and column factors gives the exact identities

$$
\begin{aligned}
\Delta_D&=\left(\prod_i d_i^3u_i\right)\alpha^{18}\det(r_D(w_{D,i},\beta_{D,i}))_i,\\
\Delta_I&=\left(\prod_i d_i u_i^3\right)\alpha^{22}\det(r_I(w_{I,i},\beta_{I,i}))_i.
\end{aligned}
$$

The generic inverse normalization uses the coordinate $t$ with scale $\alpha^{3/2}$: its column-scale product is $(\alpha^{3/2})^{44/3}=\alpha^{22}$. It must not be normalized with scale $\alpha$ merely because the original interval is in $s$.

Let $z_i=s_i/\alpha$. The exact source equation gives
$w_{D,i}^2=z_i$ and $w_{I,i}^6=z_i^3(1+1/n_i)$. In the range used here $1\le M\le x\le n_i$ and $1\le z_i\le1+1/M$. Thus both node sets lie in $[1,1+1/M]\subset[1,2]$: for the inverse chart, $w_{I,i}^6\le(1+1/M)^4\le(1+1/M)^6$.

Moreover

$$
\beta_{D,i}=w_{D,i}^3\bigl((1+1/n_i)^{1/2}-1\bigr),\qquad
\beta_{I,i}=w_{I,i}^2\bigl((1+1/n_i)^{-1/3}-1\bigr).
$$

For finite sources their signs are $\beta_{D,i}>0$, $\beta_{I,i}<0$ and absolute value at most $8/x$. Both charts thus use the same original intervals. In either chart write the normalized row as $r_0(w)+\beta r_1(w)$, with $r_1$ supported on the last four columns. By multilinearity choose the $k$ error rows and take out their $\beta$ factors. The remaining determinant is a polynomial alternating in the nodes of the $8-k$ smooth rows and separately alternating in the nodes of the $k$ error rows. It vanishes when two nodes within either block coincide. The distinct linear differences within the two blocks therefore divide it as a product. The quotient polynomial is bounded on $[1,2]^8$, uniformly over the finitely many row choices and both charts. Because the nodes lie in an interval of width $1/M$, this product gives the powers

$$
a_k=\binom{8-k}{2}+\binom{k}{2}\quad(0\le k\le4),
\qquad (a_0,\ldots,a_4)=(28,21,16,13,12).
\tag{6.3}
$$

At least five perturbation rows force determinant zero because those rows occupy a four-dimensional subspace. Each of the remaining terms has size $O(x^{-k}M^{-a_k})$. To restore the integer scale, use $d_i\le2E$, $u_i\le\sqrt2\,U$ and $\alpha\le s_i\le2B/E$ for a nonempty tuple. With $U=x^{1/2}B^{-3/2}$ from (3.5), the two positive prefactors satisfy

$$
\begin{aligned}
\left(\prod_i d_i^3u_i\right)\alpha^{18}
&\ll E^{24}U^8(B/E)^{18}=x^4(BE)^6=x^4P^6,\\
\left(\prod_i d_i u_i^3\right)\alpha^{22}
&\ll E^8U^{24}(B/E)^{22}=x^{12}(BE)^{-14}=x^{12}P^{-14}.
\end{aligned}
$$

The implicit factors here are absolute. The powers of $B$ and $E$ cancel into their product, so no bound on $B/E$ is needed. Thus, with

$$
W(\psi)=\min(4+6\psi,12-14\psi),
$$

the selected chart satisfies

$$
|\Delta|\le C_2\sum_{k=0}^4x^{W(\psi)-k}M^{-a_k}.
\tag{6.4}
$$

The two chart scales meet at $\psi=2/5$. There is no bounded-skew assumption on $B/E$. Actual interval widths and fixed upper-height factors are included in $C_2$, uniformly over the original boxes.

## 6.2 Modular bound

Fix the interval, factor $F$, prime $p$ and residue label $z_0\in\mathbb F_p^2$ from §5. Work in $R=\mathbb Z/p^{28}\mathbb Z$ and reduce $(s,t)$ using the inverses of $d,u$. For an eight-tuple in the class choose a centre $c\in R^2$ from one of its actual sources. Then $F(c)=0$ and $c$ reduces to $z_0$. Choose the coordinate $i$ with unit partial derivative and write $\iota=(\partial_iF(c))^{-1}$ in $R$. Let $j$ be the other coordinate, and use the original coordinate order in the recurrence

$$
\begin{aligned}
q_0(X)&=0, & (Y_k(X))_i&=c_i+q_k(X), & (Y_k(X))_j&=c_j+X,\\
q_{k+1}(X)&=q_k(X)-\iota F(Y_k(X)).
\end{aligned}
$$

Induction gives $q_k(0)=0$, since $F(c)=0$. For any actual class member $z\in R^2$, put $X=z_j-c_j$ and $e_k=z_i-c_i-q_k(X)$. Both $X$ and $e_0$ belong to $pR$. At this $X$ we have $Y_k(X)\equiv c\pmod p$. Polynomial expansion in coordinate $i$ gives

$$
0=F(z)=F(Y_k(X))+e_k\partial_iF(Y_k(X))+e_k^2 B_k
$$

for some $B_k\in R$. Substitution in the recurrence gives

$$
e_{k+1}=\bigl(1-\iota\partial_i F(Y_k(X))-\iota e_k B_k\bigr)e_k.
$$

If $e_k\in p^{k+1}R$, the parenthesis belongs to $pR$, giving $e_{k+1}\in p^{k+2}R$. After 27 corrections $e_{27}=0$ in $R$, so the coordinates of every member of this class are given by the same polynomials in its free displacement. The centre and these polynomials may be chosen afresh for a different tuple.

Divide each original row by its unit denominator $d^3u$ or $du^3$ from (6.1) or (6.2). After substituting the two coordinate polynomials, every column is the evaluation of one polynomial in $X$. Reduce it by the monic product $\prod_{\nu=1}^8(X-X_\nu)$ of the eight parameter-node factors. Monic division works over $R$, including zero divisors, and preserves its evaluations even at repeated nodes. The evaluation matrix is therefore the product of the Vandermonde matrix with columns $1,X,\ldots,X^7$ and the matrix of remainder coefficients. Since every $X_\nu\in pR$, the determinant has the factor $p^{0+1+\cdots+7}=p^{28}$. Multiplying back the row denominators gives the claim for the original integer determinant:

$$
p^{28}\mid\Delta.
\tag{6.5}
$$

The ring argument uses the rational coordinates for either choice of partial, including at $p=2$ and $p=3$. Monic reduction limits each column to eight coefficients for this computation. Section 7 uses divisibility for every tuple and bounds the class relation using the original integer rows.

# 7. One bounded relation for the entire class

Section 10 makes the right side of (6.4) strictly smaller than $T^{28}\le p^{28}$. Hence every eight-row minor vanishes. Rank is at most seven. Use the entire finite class in the maximal actual/unit row completion of Proposition 4.2. Its nonzero cofactor vector annihilates every actual row, since a nonzero pairing with any further member would increase the maximal number of actual rows. This yields one relation even for lower ranks, repeated rows, empty classes and classes with fewer than eight sources; a ninth member is covered by the same maximality argument.

Since $b,d\le(3x)^{1/3}$ and $u,v\le(3x)^{1/2}$, the entries of (6.1) and (6.2) are at most $(3x)^{11/6}\le9x^{11/6}$. The cofactor bound (4.3) is therefore at most $7!\,9^7x^{77/6}\le x^{14}$ for $x$ beyond a fixed threshold. The resulting polynomial $G$ has bidegree at most $(3,1)$ or $(1,3)$ in the original coordinates $(s,t)$, according to the chart. One $G$ vanishes on the complete fixed class.

# 8. Count every class through its graph and rulings

We apply graph/ruling arithmetic to every class relation $G$, without asking whether it shares the coarse factor $F$.

## Lemma 8.1 — bounded graph/ruling decomposition

Use graph coordinates $(\xi,\zeta)=(s,t)$ in the direct chart and $(\xi,\zeta)=(t,s)$ in the inverse chart. Write $G=P_0(\xi)+\zeta Q_0(\xi)$ with degrees at most three and coefficients bounded by $x^{14}$. The two sections are not both zero. Remove their primitive integral common factor $D_0$ and write

$$
P_0=-D_0A,\qquad Q_0=D_0B,
\qquad \gcd_{\mathbb Q[\xi]}(A,B)=1.
\tag{8.1}
$$

There are at most three rational roots of $D_0$, giving coordinate rulings. Off those roots the equation is $-A(\xi)+\zeta B(\xi)=0$. If either value $A(\xi)$ or $B(\xi)$ vanishes, the other vanishes as well because $\zeta>0$. This would contradict coprimality. Thus every remaining source satisfies $\zeta=A(\xi)/B(\xi)$ with both section values nonzero. If a section vanishes identically, all permitted sources are in the ruling branch. If $\max(\deg A,\deg B)=0$, the graph is constant and gives a ruling of the other coordinate.

The univariate factor-height estimate in Lemma 4.3 bounds each nonzero factor or quotient of $P_0,Q_0$ here by $2^3(3+1)x^{14}\le x^{15}$ for $x\ge32$. All sections have degree at most three. Both charts use the same interval family from Lemma 4.1.

## Lemma 8.2 — uniform ruling counts

For a fixed $b/d$, Lemma 3.1 bounds original starts up to $N$ by $1+\lfloor\log_2(2N+1)\rfloor$, independently of that ratio. For a fixed $v/u$, Lemma 3.2 gives 8400, independently of that ratio. Thus either coordinate ruling has the common envelope $8401+\lfloor\log_2(2N+1)\rfloor$. For $N\le2x$, this is $O_\eta(x^\eta)$ for every $\eta>0$ with a constant before the ratio. The same statement handles constant graphs. No aggregate small-product estimate is substituted for a fixed large-product fibre.

Mixed graphs of positive actual degree are handled next. The result is a uniform $O_\eta(x^\eta)$ bound for each full class, with no coefficient-family enumeration.

# 9. Resultants, admitted levels and the precise Stewart input

Fix a mixed graph from Lemma 8.1. Its two nonzero sections are coprime over $\mathbb Q[\xi]$. Set $r=\max(\deg A,\deg B)$, so $1\le r\le3$, and homogenize both sections to degree $r$. Denote the homogeneous forms again by $A(Z,W),B(Z,W)$. There is no common projective root over $\overline{\mathbb Q}$. At finite points this follows from coprimality, and at $[1:0]$ at least one section has nonzero coefficient of $Z^r$ by the choice of $r$.

The Sylvester matrix of the map $(U,V)\mapsto UA+VB$, from two copies of the degree-$(r-1)$ binary forms to the degree-$(2r-1)$ binary forms, is an integer matrix of size $2r$. Since $A,B$ are coprime, $UA+VB=0$ would imply $A\mid V$ and $B\mid U$. Both $U,V$ must then be zero by their degree bounds. The matrix is therefore invertible over $\mathbb Q$, and its determinant $R$ is the full homogeneous resultant in the chosen monomial bases. The determinant expansion bounds $|R|$ by the number of terms $(2r)!$ times $x^{15(2r)}$, giving

$$
1\le|R|\le720x^{90}.
\tag{9.1}
$$

Apply the adjugate to the basis vectors for $Z^{2r-1}$ and $W^{2r-1}$. This expresses both $RZ^{2r-1}$ and $RW^{2r-1}$ as integral polynomial combinations of $A,B$. At a primitive parameter pair $(Z,W)$ on the graph, set $g=\gcd(|A(Z,W)|,|B(Z,W)|)>0$. Then $g$ divides both specialized expressions. Primitivity of $(Z,W)$ gives $\gcd(Z^{2r-1},W^{2r-1})=1$, hence $g\mid|R|$. The choice of common homogeneous degree is essential to this argument at infinity.

For a concrete actual-source control, $288=2^3\cdot6^2$, $289=1^3\cdot17^2$. In the inverse chart take $A=6Z-5W$, $B=6W$ and $(Z,W)=(17,6)$. Their values are 72 and 36, so $g=36$. The full degree-$(1,1)$ resultant is $R=36$, whereas the affine resultant of $6T-5$ and the constant 6 is only 6. The inverse pullback has content one and value $46656=g^3$. Replacing the full resultant by the affine one would lose $g\mid R$ on this admitted source.

## 9.1 Source reconstruction and content

The direct and inverse pullback polynomials have the forms

$$
H_D(Z,W)=W^3A(Z,W)^2-Z^3B(Z,W)^2,\qquad
H_I(Z,W)=Z^2B(Z,W)^3-W^2A(Z,W)^3.
\tag{9.2}
$$

In the direct chart an original source gives $(Z,W)=(b,d)$. Its partner ratio $v/u=A(Z,W)/B(Z,W)$ is positive and reduced. Thus $(A(Z,W),B(Z,W))=\sigma g(v,u)$ for a common sign $\sigma=\pm1$. Substituting into (9.2) gives $H_D(b,d)=g^2(d^3v^2-b^3u^2)=g^2$. In the inverse chart $(Z,W)=(v,u)$ and the partner ratio is $b/d=A(Z,W)/B(Z,W)$. Now the same argument gives $(A(Z,W),B(Z,W))=\sigma g(b,d)$ and $H_I(v,u)=\sigma g^3(d^3v^2-b^3u^2)=\sigma g^3$. Primitivity of both original pairs follows from §2.

Fix $H=H_D$ or $H_I$ with the graph and chart. An empty source fibre contributes zero. On a nonempty fibre the identity just proved gives a nonzero value of $H$, so its coefficient content $c$ is positive. Put $Q=H/c$ and write $h=Q(Z,W)$ at an original source. The source equation now gives

$$
g\mid|R|,\qquad c\mid g^\ell,\qquad
c h=\pm g^\ell,\qquad h\ne0,\qquad |h|\mid g^\ell,
\quad\ell\in\{2,3\}.
\tag{9.3}
$$

There is no assertion $c\mid R$. On the actual $8/9$ inverse graph, $A=2(Z-W)$, $B=2(Z-2W)$ at $(Z,W)=(3,1)$ gives values $(4,2)$ and $g=2$, with $R=-4$. The inverse pullback has content $c=8$ and value $g^3=8$, so its reduced level is 1. Thus $c\nmid|R|$ but $c\mid g^3$, as required. Negating both sections gives reduced level $-1$ on the same graph. An arbitrary graph parameter is not automatically admitted: for $A=Z$, $B=W$, the direct parameter $(2,1)$ has $g=1$ and pullback value $-4$, which is not $g^2$. Only the actual source equation supplies (9.3).

## 9.2 Factor dispatch including axes and infinity

Both sections are nonzero: a zero section with rational coprimality would force the other to be constant, already a ruling in Section 8. The nonzero pullbacks have exact homogeneous degrees

$$N_D=2r+3\in\{5,7,9\},\qquad N_I=3r+2\in\{5,8,11\}.$$

At $Z=0$, write $a,b$ for the orders of $Z$ in $A,B$. The two summands have orders $2a,3+2b$ in $H_D$ and $2+3b,3a$ in $H_I$. These orders differ modulo 2 or 3, respectively, so the order of the difference is the smaller one. At least one of $a,b$ is zero by coprimality. At $W=0$ the corresponding orders are $3+2a,2b$ and $3b,2+3a$, where at least one of the orders $a,b$ in $W$ is zero by the choice of $r$. This proves the bounds 3 and 2 at both axes, including when one affine section has degree below $r$.

Suppose $H=c_0G^k$ for a homogeneous $G$ of degree $d\in\{1,2\}$. Since $H\ne0$ and $N>0$, the scalar, form and exponent are nonzero and $dk=N$. Directly, odd $N$ excludes $d=2$, while $d=1$ gives $k=N\ge5>3$. Inversely, $dk=N\ge5$ gives $k\ge3>2$. Any axis factor of $G$ would therefore exceed the corresponding axis bound in $H$. Consequently $P(T)=G(T,1)$ has full degree $d$ and nonzero constant coefficient, and $H(T,1)$ has full degree $N$. This full-degree conclusion precedes abc.

Put $a(T)=A(T,1)$, $b(T)=B(T,1)$. The identity at zero now forces $a(0)\ne0$. Together with $\gcd_{\mathbb Q[T]}(a,b)=1$, this makes $a$ coprime to $Tb$. Thus the original summands $a^2,T^3b^2$ in the direct case and $T^2b^3,a^3$ in the inverse case are coprime. Their nonzero difference is $c_0P^k$ and is coprime to both. The polynomial $abc$ inequality of Mason and Stothers [4] bounds its degree by the degree of the radical of the product minus one. For coprime $f,g$ with nonconstant $h=f-g$, the polynomial $fg'-f'g$ is nonzero since $f/g$ is nonconstant in characteristic zero. Each repeated factor contributes all but one of its copies to it, using $fg'-f'g$ for $f,g$ and $hg'-h'g$ for $h$. Since $f,g,h$ are pairwise coprime, their product divided by its radical divides $fg'-f'g$. Comparing degrees with $\deg f+\deg g-1$ gives $\deg h+1\le\deg\operatorname{rad}(fgh)$. Here the radical is supported on $abTP$, so

$$
N+1\le\deg a+\deg b+1+d,\qquad
N\le\deg a+\deg b+d\le2r+2.
$$

This contradicts $N_D=2r+3>2r+2$ and $N_I=3r+2>2r+2$ for $r\ge1$. The argument excludes reducible quadratic powers too; no irreducibility of $G$ was used.

For the content-one homogeneous pullback $Q$, exhaustive fixed-factor selection then gives either a primitive rationally irreducible factor whose full affine degree is between 3 and 11, or two fixed low-degree factors. In the second branch the exact alternatives are: two nonproportional linear factors; a linear and a quadratic factor with the latter not proportional to the square of the former; or two nonproportional quadratics. The factor-selection proof derives these hypotheses and handles constant affine sections and infinity padding; they are not free assumptions about arbitrary factors.

Here is the exhaustive decision for $q(T)=Q(T,1)$. Its integral primitive factorization is taken once, before signed levels or subsets of points are chosen.

| Case | Fixed selection or exclusion |
| --- | --- |
| An affine irreducible factor has degree at least 3 | Homogenize that factor at its own full affine degree; it divides $Q$ and supplies the high branch. |
| All affine factors have degree 1 or 2, and $\deg q<N$ | Select the infinity factor $W$ and the full-degree homogenization of one affine factor. The latter is not divisible by $W$. |
| No infinity padding, with two nonassociate affine factors | Select their full-degree homogenizations. Irreducibility and nonassociation give the stated low-pair conditions. |
| No infinity padding, with only one affine irreducible factor | $Q$ is a scalar power of that low-degree homogenization, excluded above. |
| Constant affine section | $Q=c_0W^N$, also an excluded linear power. |

In the infinity case the chosen affine factor exists unless the last row applies. A quadratic irreducible factor cannot be proportional to the square of the selected linear factor. For two linears or two quadratics, nonassociation gives nonproportionality. These facts, rather than a generic-position assumption, are what make the following eliminants nonzero.

For two equal-degree low factors $F_1,F_2$ at fixed nonzero signed levels $h_1,h_2$, the polynomial $h_1F_2-h_2F_1$ vanishes at every solution and is nonzero by nonproportionality. In the linear–quadratic case the eliminant is $h_L^2G-h_GL^2$, which is nonzero because $G\notin\mathbb Q L^2$. Both eliminants have degree at most two. A nonzero homogeneous polynomial of degree $d$ has at most $d$ projective zeros. This follows by dehomogenization, counting infinity once if the affine degree is below $d$. Each rational projective zero has at most two signed primitive representatives. Thus there are at most four primitive signed points at any such level pair, including the axes.

The [axis-first argument and exhaustive factor dispatch in LP16](LAMPORT_COMPANION.md#lp16) detail why the low-degree pure-power case is excluded before the signed-level count.

## 9.3 Established external input

For a positive integer $m$, let $\omega(m)$ count its distinct prime divisors and $\tau(m)$ count its positive divisors. Use Stewart [2], Theorem 1 and its primitive-pair specialization on printed pages 795–796. For every integer polynomial $f$, homogenized at its full affine degree $d$, assume coefficient content one, rational separability and $3\le d\le11$. For any nonzero signed integer $h$, the number of primitive signed integer pairs satisfying $F(z)=h$ is at most

$$
2800d^{1+\omega(|h|)}.
\tag{9.4}
$$

To obtain the numerical constant, use the full divisor $g_{\rm St}=|h|$ in Stewart's Theorem 1. For discriminant $\Delta_F\ne0$, the estimate on printed p. 796 is

$$
G(|h|,d,\Delta_F)\le |h|^{(d-2)/d}|\Delta_F|^{1/(d(d-1))},
$$

where $G$ is the factor in Stewart's condition (8). Consequently

$$
\frac{|h|^{1+e}|\Delta_F|^{1/(d(d-1))}}{G(|h|,d,\Delta_F)}
\ge |h|^{2/d+e}
\qquad(e>0).
$$

Theorem 1 therefore gives $2800(1+1/(8ed))d^{1+\omega(|h|)}$ for the same set of coprime integer pairs for every $e>0$. Letting $e\to\infty$ gives (9.4). This uses signed nonzero levels, including $h=\pm1$.

Full affine degree rules out a root at infinity and separability gives simple roots at finite points, so the forms used here have nonzero discriminant. Stewart's theorem includes the separable, possibly reducible cubics in Lemma 3.2 and the selected irreducible high-degree factors of §9.2. The count is over all coprime integer pairs, including axes and both signs when they satisfy the equation.

## 9.4 Divisor inventory and transfer to original starts

The graph, chart, resultant $R$, content $c$ and factors of $Q$ are fixed before choosing levels. For each $g\mid|R|$ and sign allowed by (9.3), the equation $ch=\sigma g^\ell$ determines at most one nonzero integer $h$. The direct chart has $\sigma=+1$ and the inverse chart allows both signs. Thus there are at most $2\tau(|R|)$ labels.

At an admitted level $Q(Z,W)=h$, every selected integral factor divides $Q$ with integral quotient, and its value is a nonzero signed divisor of $h$. If two low factors were selected, each has at most $2\tau(|h|)$ possible values. The bound of four per value pair from §9.2 gives at most $16\tau(|h|)^2$ primitive signed pairs in total. If a high factor $F$ was selected, its affine section has full degree $3\le d\le11$ and is separable by irreducibility in characteristic zero. For each signed divisor $k$ of $h$, (9.4) bounds the solutions of $F(Z,W)=k$ by $2800d^{1+\omega(|k|)}\le30800\,11^{\omega(|h|)}$. Summing over the signed divisors gives at most $61600\tau(|h|)11^{\omega(|h|)}$ pairs.

For $p^a\parallel |R|$, (9.3) bounds the exponent of $p$ in $|h|$ by $3a$ and excludes primes outside $R$. It follows that

$$
\tau(|h|)\le\prod_{p^a\parallel |R|}(3a+1)\le\tau(|R|)^3,
\qquad
11^{\omega(|h|)}\le16^{\omega(|R|)}\le\tau(|R|)^4.
$$

Summing the two uniform branch bounds over the possible gcd and sign labels yields

$$
2\tau(|R|)\bigl[16\tau(|R|)^6+61600\tau(|R|)^7\bigr]
\le123232\tau(|R|)^8=O_\eta(x^\eta)
\tag{9.5}
$$

For every $\rho>0$, $\tau(m)\ll_\rho m^\rho$. To see this, use $a+1\le2^a\le p^{\rho a}$ at primes with $p^\rho\ge2$, and at each of the finitely many other primes take the finite supremum of $(a+1)/p^{\rho a}$. Using $\rho=\eta/720$ in (9.5) gives the asserted $O_\eta(x^\eta)$ by (9.1).

Each positive primitive graph parameter from an original source fixes the free ratio and determines its partner by the graph equation, so Lemma 2.2 makes the transfer to original starts injective. The other signed primitive pairs counted by the upper bound need not arise from starts. There are at most three common-factor rulings and at most one remaining graph or constant-coordinate ruling. Adding their bounds from Lemma 8.2 and (9.5) gives $O_\eta(x^\eta)$ for the complete class, uniformly in its relation and coefficients.

# 10. Profile optimization and rounded determinant comparison

The scalar profile inequalities established here are logically independent of the class-counting and determinant-vanishing conclusions of §§5–9. The calculation uses the box profile $m_0$, the row-height exponents defining $W$, the fixed mixed-term weights $a_k$ and the scalar parameters defined below. These inequalities can be proved before their uses in §§4–7.

For $0\le\psi\le2/3$, define $W$ as in Section 6 and $m_0$ as in Section 3. The exact zero-slack envelope is

$$
\max\left\{m_0(\psi),\max_{0\le k\le4}
\frac{W(\psi)-k+(28-a_k)m_0(\psi)}{28}\right\}\le\theta.
\tag{10.1}
$$

The quadratic $m_0$ has maximum $3/16$ at $\psi=1/3$. Its derivative is $m_0'=9/8-27\psi/8$, which is $-9/40$ at $\psi=2/5$. Since $0\le28-a_k\le16$, the derivative of each branch numerator in (10.1) is at least $6-16(9/40)>0$ to the left of $2/5$. To the right it is at most $-14$, because $m_0'<0$ there. At the common maximum $\psi=2/5$, we have $m_0=9/50$, $W=32/5$, and the five branch values are

$$
8/35,\quad333/1400,\quad41/175,\quad61/280,\quad33/175.
\tag{10.2}
$$

The one-error branch attains the maximum $\theta=333/1400$. For $m=(1+\delta)m_0$ and $q=\theta+\delta-m$, the bound $m_0\le3/16$ gives the first inequality below. For the second, the zero-slack gap from (10.1) increases by $\delta(28-(28-a_k)m_0)\ge25\delta$. Thus

$$
q\ge141/2800+13\delta/16>0,\qquad
28q-(W-k-a_km)\ge25\delta>0.
\tag{10.3}
$$

The actual ceiling in (4.1) satisfies $x^m\le M\le2x^m$. Uniformly in the profile, $T\ge x^{141/2800}$ at a sufficiently large height by the first inequality of (10.3). Since $T=x^{\theta+\delta}/M$, the ratio of $x^{W-k}/M^{a_k}$ to $T^{28}$ is

$$
x^{W-k-a_km-28q}(M/x^m)^{28-a_k}.
$$

The gap in (10.3) bounds the first factor by $x^{-25\delta}$, and the ceiling costs at most $2^{16}$ in the second. Hence

$$
\frac{x^{W-k}}{M^{a_k}}
\le2^{16}x^{-25\delta}T^{28}.
\tag{10.4}
$$

For fixed $\delta>0$ and $C_2$, one threshold makes the sum of all five terms, multiplied by $C_2$, strictly less than $T^{28}$. Since each selected prime is at least $T$, every original integer minor in Section 6 vanishes. All thresholds precede the varying profile, prime and source population.

# 11. Conservative interval and box inventory

Fix $0<\delta\le1$ as in (4.1) and a class loss $\eta>0$. Coarse degree and height constants are fixed by Proposition 4.2. Every interval has boundedly many factors. For one factor, singular sources cost $O_\delta(1)$; the bounded prime union supplies $O_\delta(T)$ smooth classes; each class costs $O_\eta(x^\eta)$ by Sections 8–9. Hence the factor and interval costs are

$$
O_{\delta,\eta}(Tx^\eta+1).
$$

The common interval family has at most $3M+1\le4M$ members. The residual box count therefore satisfies

$$
N_{\mathrm{residual\ box}}(x)
\ll_{\delta,\eta}MTx^\eta+M.
\tag{11.1}
$$

There is no once-per-common-component saving in this proof: the $x^\eta$ charge is paid for every smooth class. Because $T\ge1$ for the chosen large-height range and $x\ge1$, the singular term is absorbed. The exact identity $MT=x^{\theta+\delta}$ gives

$$
N_{\mathrm{residual\ box}}(x)
\ll_{\delta,\eta}x^{\theta+\delta+\eta}.
\tag{11.2}
$$

The two complements are included in the actual box theorem. For a prescribed box loss $e>0$, take $h=e/3$ and $\delta=\min(1,h)$, and use class loss $h$. Then $\delta+h\le2e/3\le e$, while each small-product complement costs $O_h(x^{\theta+h})$. The union covers every original source; any overlap is only an overcount. Thus every actual box has $O_e(x^{\theta+e})$ sources, with constants before all boxes and finite source functions. Empty residual boxes are already included.

# 12. Boxes, shells, finite head and real cutoff

Fix the final natural-count loss $\varepsilon>0$. First obtain the shell theorem with loss $\varepsilon/2$. Within that shell theorem, apply the actual box count with loss $\varepsilon/4$ and pay each of the two dyadic kernel-label counts by $x^{\varepsilon/8}$. Their product yields a uniform shell bound

$$
\#\{\text{selected original starts in }[x,2x]\}
\le C_s x^{\theta+\varepsilon/2}
\tag{12.1}
$$

for every sufficiently large real $x$, with one threshold and constant before all selected finite source populations. The dyadic labels cover all original kernels, including kernel one; no skew restriction is imposed.

Now cover positive starts $n\le N$ by their dyadic start labels. For a large shell, bound its contribution by $C_sN^{\theta+\varepsilon/2}$. For a shell below the fixed threshold, bound its starts by one fixed finite head and enlarge the same coefficient; this is valid also for $N=1$. There are $O(1+\log N)$ labels. Pay this third logarithm by $N^{\varepsilon/2}$. The result is (1.2), with one constant before every $N\ge1$. This deliberately conservative shell sum matches the maintained implementation; it needs no sharper geometric-sum argument.

For $X\ge1$, let $N=\lfloor X\rfloor\ge1$. Equation (1.2), $N\le X$ and $\theta+\varepsilon>0$ give (1.3) with the same constant. The finite head is included, and the real population remains exactly the original start count. $\square$

# 13. What the exponent measures

The one-error term attains the maximum of the five-term envelope in §10 at $\psi=2/5$. Its angular order is sharp in the enlarged real model, where the error amplitudes are bounded and have the chart's sign, and zero amplitudes are allowed. At the selected prime scale, the full determinant already vanishes by §§6–7. The witness below isolates one error row. The seven unperturbed rows have zero error in the model, whereas the formulas for $\beta_{D,i}$ and $\beta_{I,i}$ in §6.1 give strictly signed errors for finite canonical sources. The witness therefore leaves open whether arithmetic improves the one-error estimate before modular vanishing. Other covers and monomial sets may give different bounds. Sections 9–12 charge their positive losses to the final $\varepsilon$. Erdős's fixed-power logarithmic estimate remains open.

**An explicit enlarged-model witness.** Put $w_i=1+h\xi_i$ with fixed distinct $0\le\xi_0<\cdots<\xi_6\le1$, $0\le\xi_7\le1$ and $h\downarrow0$. Set the first seven error amplitudes to zero and the eighth to a nonzero allowed amplitude $\lambda$ (positive directly, negative inversely). This is a choice in the enlarged analytic model, not a construction of canonical sources. For the ordered smooth exponents

$$e_D=(0,2,4,6,3,5,7,9),\qquad e_I=(0,3,6,9,2,5,8,11),$$

let $J_e$ have first seven rows $(\binom{e_j}{k})_{j=0}^7$, $k=0,\ldots,6$, and last row $(0,0,0,0,1,1,1,1)$. Exact determinant expansion gives

$$\det J_{e_D}=2240,\qquad\det J_{e_I}=393660.$$

Indeed, expanding the seven smooth rows in powers of $h$, a nonzero determinant requires seven distinct Taylor orders; their least sum is $0+\cdots+6=21$. At that order the error row is its value at $w=1$, and the Taylor coefficients give precisely $J_e$. The coefficient of $\lambda$ is therefore

$$h^{21}\!\left(\prod_{0\le i<j\le6}(\xi_j-\xi_i)\right)\det J_e+O(h^{22}),$$

which is nonzero to order 21. All rows are fixed polynomials on a compact node range, so this remainder follows directly from their finite expansions. Taking $\xi_7=\xi_0$ makes the all-smooth determinant zero. For any fixed admissible $\lambda\ne0$, the full determinant then has this nonzero leading term multiplied by $\lambda$, realizing order 21 in the enlarged model.

# 14. Formal correspondence and remaining acceptance

The Lean developments include `original_shell_source_count`, `natural_pair_count` and `real_pair_count` in the namespace `P0365Subquarter`. Each takes the quantitative Thue bound (9.4) as the explicit premise `StewartPrimitiveThue`. On 23 November 2026, all 35 predeclared controls qualified and an independently operated clean Linux replay returned `COMPLETE / PASS`. The run reconciled the exports from 152 candidate and 44 reference modules, passed all six checkers, completed strict whole-export and target-transitive axiom audits, and matched fourteen theorem interfaces and four protected definition bodies with no definition holes. The formal result proves the counting bounds given the stated premise. The ordinary argument invokes Stewart's published theorem to supply it. The [supplement](SUPPLEMENT.md) records the exact scope, including the common-constant witness.

AI systems assisted the mathematical research, Lean formalization, manuscript preparation and critique. The author is responsible for the mathematical claims. Independent specialist review remains pending.

# References and supporting proof sources

1. T. Reuss, *Pairs of k-free numbers, consecutive square-full numbers*, arXiv:1212.3150v2, revised 19 March 2014. [Theorem 4](https://arxiv.org/pdf/1212.3150v2#page=4).
2. C. L. Stewart, *On the number of solutions of polynomial congruences and Thue equations*, Journal of the American Mathematical Society 4 (1991), 793–835. [DOI 10.1090/S0894-0347-1991-1119199-X](https://doi.org/10.1090/S0894-0347-1991-1119199-X) · [Theorem 1 and its specialization, printed pp. 795–796](https://uwaterloo.ca/pure-mathematics/sites/default/files/uploads/documents/s0894-0347-1991-1119199-x_0.pdf#page=3).
3. T. H. Chan, *Twin squareful numbers*, Journal of the Australian Mathematical Society 93 (2012), 43–51, Theorems 3–4. [DOI 10.1017/S144678871200016X](https://doi.org/10.1017/S144678871200016X).
4. W. W. Stothers, *Polynomial identities and Hauptmoduln*, The Quarterly Journal of Mathematics 32 (1981), 349–370. [Journal article](https://doi.org/10.1093/qmath/32.3.349).
5. D. R. Heath-Brown, *Sums and differences of three kth powers*, Journal of Number Theory 129 (2009), 1579–1594. [DOI 10.1016/j.jnt.2009.01.012](https://doi.org/10.1016/j.jnt.2009.01.012).
6. P. Erdős, *Problems and results on number theoretic properties of consecutive integers and related questions*, 1976, p. 31. [Author's paper](https://combinatorica.hu/~p_erdos/1976-39.pdf).
7. P. Erdős and R. L. Graham, *Old and New Problems and Results in Combinatorial Number Theory*, Monographie de L'Enseignement Mathématique 28, 1980, p. 68. [Monograph](https://mathweb.ucsd.edu/~ronspubs/80_11_number_theory.pdf#page=64).
8. D. T. Walker, *Consecutive integer pairs of powerful numbers and related Diophantine equations*, The Fibonacci Quarterly 14 (1976), 111–116. [Journal article](https://fq.math.ca/Scanned/14-2/walker.pdf).
9. V. Blomer and A. Schöbel, *Twins of powerful numbers*, Functiones et Approximatio Commentarii Mathematici 49 (2013), 349–356, Theorem 3. [DOI 10.7169/facm/2013.49.2.12](https://doi.org/10.7169/facm/2013.49.2.12).
10. W. Wongcharoenbhorn and Y. Meemark, *Square-full values of quadratic polynomials*, Bulletin of the Australian Mathematical Society 113 (2026), 40–54. [DOI 10.1017/S0004972725000255](https://doi.org/10.1017/S0004972725000255) · [Author preprint](https://arxiv.org/abs/2405.06968v2).
11. D. Plymesser, *Counting powerful products of consecutive integers*, Hexagon preprint `hexagon:2611.00602v1` (public version listed 19 November 2026). [Preprint landing page](https://hexagonmath.org/2611.00602v1).
