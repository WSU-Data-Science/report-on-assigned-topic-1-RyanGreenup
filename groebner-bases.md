---
author:
- Ryan Greenup
bibliography: ref.bib
title: Groebner Bases
---

Groebner bases is one of the main practical tools for solving systems of
polynomial equations.

# Summary {#sec:org73c5bea}

Much of the theory of Groebner Basis is buried under needless amounts of
abstract algebra, this is for the most part unnecessary and if I were to
begin this investigation again I would first implement Buchberger's
Algorithm, manually, using *Sympy* by referring to:

-   Lectures 14 and 15 of Andreas Schulz OCW Integer Programming Course
    [@andreasschulzIntegerProgrammingCombinatorial]

-   Chapters 1-2 of *Ideals, Varieties and Algorithms*
    [@coxIdealsVarietiesAlgorithms1997]

-   Lecture 15 of Judy Holdenner's course on Algebraic Geometry
    [@judyholdenerAlgebraicGeometry2013]

-   Lecture 14 of Pablo Parrilo's course on Algebraic Techniques
    [@pabloparriloAlgebraicTechniquesSemidefinite]

-   The *Sympy* source code for:

    -   `polys.roebnertools`
        [@sympydevelopmentteamSympyPolysGroebnertools]

    -   `solvers.polysys` [@sympydevelopmentteamSympySolversPolysys]

-   The *Sympy* documentation for *Polynomial Manipulation*
    [@sympydevelopmentteamGrobnerBasesTheir2021]

Unfortunately this was not an option for me as these resources were not
known to me until very late in the investigation. I hope that this
report can serve as a guide for others who pick up this topic such that
they can:

-   Come to grips with the core concepts and practical applications
    quickly without wasting time on abstract algebra that is poorly
    explained [^1]

-   Identify useful resources that are written well and written with
    accessibility in mind

-   Avoid material that serves as, for lack of a better word, as a red
    herring.

Although `sympy` is probably not the best tool for studying commutative
algebra specifically (and the implementation may not be battle tested
either, see e.g. [@WrongGroebnerBasis]), the simple and accessible
nature of `sympy` made it's documentation by far the most valuable
resource for grappling with this topic.

An extension to this investigation would be to:

-   Try and implement Buchberger's Algorithm from scratch using
    functions and iterations in *Python* in order to return a Reduced
    Groebner Basis

    -   See Definition 4 of [@coxIdealsVarietiesAlgorithms1997 §7]

-   Try to demonstrate, in good detail, the relationship between the
    Euclidean Algorithm and Buchberger's Algorithm

    -   See [@coxIdealsVarietiesAlgorithms1997 p. 95]

-   Try to implement Buchberger's Algorithm using *Normal Selection
    Strategy* [@hibiGrobnerBasesStatistics2014 §3.1.2], see also
    [@sympydevelopmentteamSympyPolysGroebnertools; @prof.berndsturmfelsIntroductionGrobnerBases2017].

## Further Resources {#sec:org91084bd}

The following resources may be useful as reference material, but I would
advice against using these as any sort of primary material, in order of
recommendation (but not necessarily relevance)

1.  Judson, T. W., & Open Textbook Library, Abstract algebra theory and
    applications [@judsonAbstractAlgebraTheory2016]

2.  Howlett, R., An undergraduate course in Abstract Algebra: Course
    notes for MATH3002 [@roberthowlettUndergraduateCourseAbstract]

3.  Lee, G., Abstract Algebra [@gregoryleeAbstractAlgebra2018]

4.  Grillet, P. A., Abstract Algebra [@grilletAbstractAlgebra2007]

5.  Hibi, T., Grobner Bases: Statistics and Software Systems
    [@hibiGrobnerBasesStatistics2014]

6.  Adams, W. W., & Loustaunau, P., An introduction to Gröbner bases
    [@adamsIntroductionGrobnerBases1994]

7.  Nicodemi, O., Sutherland, M. A., & Towsley, G. W., An introduction
    to abstract algebra with notes to the future teacher
    [@nicodemiIntroductionAbstractAlgebra2007a]

Further material that I haven't had a chance to look throughA: includes:

-   Becker, T., Weispfenning, V., & Kredel, H., Gröbner bases: a
    computational approach to commutative algebra
    [@beckerGrobnerBasesComputational1993]

# Introduction {#sec:org381cde0}

A Groebner Basis is a set of polynomials that spans the solution space
of another set of polynomials, they are of interest to us because they
are useful for solving systems of polynomial equations and provide a
generalized theory that shows the relationships between:

-   Polynomial Long Division with multiple variables and divisors, see
    e.g. [@coxIdealsVarietiesAlgorithms1997 §3]

-   The Division Algorithm see e.g. [@coxIdealsVarietiesAlgorithms1997
    §3] and [@nicodemiIntroductionAbstractAlgebra2007a]

-   The LCM and GCD [@coxIdealsVarietiesAlgorithms1997 §2.6]

-   The Euclidean Algorithm and Gaussian Elimination

    -   Both of which provide output that are special cases of Groebner
        Bases.

The theory of Groebner Bases even provides a framework to re-express the
Fundamental Theorem of Algebra
[@prof.berndsturmfelsIntroductionGrobnerBases2017] .

# Polynomials {#sec:org39547bd}

Let $K$ be some field (typically $\mathbb{Q}, \mathbb{R},
\mathbb{C}$, see §[9.1.1.6](#sec:org5f09c06){reference-type="ref"
reference="sec:org5f09c06"} for more information)

## Monomials {#sec:org6536914}

A *monomial* in the variables $x_1, x_2, \ldots x_n$ is given by:
[@hibiGrobnerBasesStatistics2014 p. 3]

$$\begin{aligned}
   \prod^n_{i=1} \left[ x_i^{a_i} \right] = x_1^{1_1} \cdot x_2^{a_2} \cdot
   x_3^{a_3} \ldots x_n^{a_n} \quad : a \in \mathbb{Z^+}
   \end{aligned}$$

Note however that $a$ must be a non-negative integer
[@e.h.connellElementsAbstractLinear2001 p. 48]

### Degree {#sec:orga195d13}

The degree is given by the sum of the exponents, so:

$$\mathrm{deg}\left(   \prod^n_{i=1} \left[ x_i^{a_i} \right]   \right) =
    \sum^{n}_{i= 1}   \left[ a_i \right]$$

### Terms {#sec:orgb84041e}

A term is a monomial with a non-zero coefficient, so for example:

$$17 \cdot x_1^3 \cdot x_2^5 \cdot x_3^{13}$$

Is a term with degree 21 $(3+5+13)$ and a coefficient of 17.

### Polynomials {#sec:org2429ee0}

A polynomial is a finite sum of terms, the degree of which is defined to
be the maximum degree of any of the terms.

#### Exception {#sec:org3332be8}

The polynomial:

$$f = 0$$

Has an undefined degree. Terms only have a **non-zero** coefficient,
hence $0$ doesn't have any terms and so the definition of degree doesn't
work for it.

Whereas $f=c, \quad \exists c \in \mathbb{C}$ does have 1 term, for
which the degree is 0.

#### Support of a polynomial {#sec:org61c2f60}

The support of a polynomial $f$ is the set of monomials appearing in
$f$, e.g. for the following 6th degree polynomial in 2 variables, the
support of that polynomial is given by:

$$f(x) = x^2+3x^3+4y \implies \mathrm{supp}\left(f\right) =
     \left\{x^2, 3x^3, 4y\right\}$$

The initial of the support $\mathrm{in}_{\prec}\left(f\right)$ is the
polynomial with the highest ranking with respect to some ordering of the
monomials (see §) [@hibiGrobnerBasesStatistics2014 1.1.5].

##### Other Terminology {#sec:orgd96e70d}

The following terms are commonly used:
[@coxIdealsVarietiesAlgorithms1997 §2.2]

-   The $\mathrm{multidegree}\left(f\right)$, is the largest power of
    any variable of any monomial in a polynomial

-   The Leading coefficient $\mathrm{LC}\left(f\right)$ is the term
    corresponding to the monomial containing the variable that
    corresponds to the multidegree

-   The Leading monomial $\mathrm{LM}\left(f\right)$ is the monomial
    corresponding containing the variable that corresponds to the
    multidegree

-   The Leading term $\mathrm{LT}\left(f\right)$ is the product of the
    leading coefficient and the leading monomial

So for example, in the polynomial:

$$f= 4x^2y^2 + 3x^3 + 7xy$$

-   The initial is $4x^2y^2$

-   The Leading Coefficient is 3

-   The Leading Monomial is $x^3$

-   The Leading Term [^2] is $x^3$

#### Homogenous Polynomial {#sec:org197934c}

If all terms of a polynomial have an equal degree (say $\exists q
     \in \mathbb{N}$ Then that polynomial is said to be a *homogenous
polynomiial of degree $q$*, e.g.

$$x_1^{3}\cdot x_2^{4} \cdot x_3^{2} + x_1^{6}\cdot x_5^{2} \cdot x_7$$

is a homogenous polynomial of degree 7.

#### The Polynomial Ring {#sec:orgde6dd2c}

The Rings, Vectors and Polynomials

Let $K\left[x_1, x_2, x_3, \ldots x_n\right]=K\left[\mathbf{X}_n\right]$
denote the set of all polynomials in the variables
$x_1, x_2, x_3, \ldots x_n$ with coefficients in some field $K$.

If $f$ and $g$ are polynomials from $K\left[x_1, x_2, x_3,
     \ldots x_n\right]$ with addition and multiplication defined in the
ordinary way (i.e. just normal algebra), then $K\left[x_1,
     x_2, x_3, \ldots x_n\right]$ forms an algebraic structure known as
a Ring.

Readers may be familiar with the axioms of a vector space, for which the
set of polynomials in $K\left[x_1\right]$ of degree less than $n$ also
satisfies [@larsonElementaryLinearAlgebra1991a §4.4], a ring structure
is much the same concept, it's a set with specific characteristics. One
of the main differences is that while a vector space requires a scalar
multiplicative identity, a ring structure does not.

On the other hand not all vector spaces are necessarily rings because
they are not necessarily closed under multiplication (although defining
multiplication by element-wise product would remedy this), see
§[9.1.1.4](#sec:orgb572ffe){reference-type="ref"
reference="sec:orgb572ffe"} for more information.

# Ideals and Varieties {#sec:org2ee65a9}

## Affine Space {#sec:org32570f6}

The affine $n$-space of some field $K$ is given by:
[@coxIdealsVarietiesAlgorithms1997 §1.1]

$$K^n=\left\{\left(a_1, a_2, a_3, \ldots, \a_n\right) \mid a_i \in K, \forall i \in \mathbb{Z}^+\right\}$$

For example if $K$ was given by $\mathbb{R}$ the resulting affine
$n$-space would be the *Cartesian Plane*.

## Zero Point {#sec:org08d0ea0}

The zero-point of some function $f\in K\left[\mathbf{X}_n\right]$ is a
point in $K^n$: [@hibiGrobnerBasesStatistics2014]

$$\begin{aligned}
      f\left( a_1, a_2, a_3 \ldots a_n \right) =0
.\end{aligned}$$

In the broader context of equations rather than specifically functions,
these points are often referred to as roots.

These points are often referred to as roots
[@judsonAbstractAlgebraTheory2016 §17.2], however this is usually in the
context of equations more broadly rather than functions specifically.
[@82645]

## Variety {#sec:org7e52766}

Consider a set of functions $F=\left\{ f_{1},f_{2},f_{3},\ldots
   f_{s}\right\}$, the variety of this set of functions is denoted
$\mathbf{V}\left(F\right)$ and is the set of all zero-points of all the
functions:

$$\boldsymbol{V}\left(F\right)=\left\{ \left(a_{1},a_{2},a_{3},\ldots a_{n}\right)\in K^{n}\mid f_{i}\left(a_{1},a_{2},a_{3},\ldots a_{n}\right),\forall i\in\mathbb{Z}^{+}<s\right\}$$

The convention is that all functions in $F$ are set to be equal to 0,
and if this convention is taken, the variety of that set is the set of
solutions corresponding to that set of equations.

### Example {#sec:org869ba3a}

Consider for example the set $\left\{ -y+x^{2}-1,-y+1\right\}$, the
solution to this system can be found by substitution:

$$\begin{aligned}
    -y + x^{2}-1    &=0=-y+1 \\
    x^{2}-1 &=y=1 \\
    x^{2}   &=2   \\
    x   &=\pm\sqrt{2}\end{aligned}$$

and so:

$$\boldsymbol{V}\left(\left\{ -y+x^{2}-1,-y+1\right\}\right)=\left\{ \left(-\sqrt{2},1\right),\left(\sqrt{2},1\right)\right\}$$

## Ideals {#sec:org4222d78}

Ideals are a set with a particularly convenient property, given
functions $f,g\in K\left[\mathbf{X}_n\right]$, a subring
$I\subset K\left[\textbf{X}\right]$ is said to be an ideal if it is
closed under addition and admits other functions under multiplication:
[@hibiGrobnerBasesStatistics2014 §1.1.3]

1.  $f\in I \land g \in I \implies f+g \in I$

2.  $f\in I \land g \in k\left[ \textbf{X} \right] \implies gf \in I$

So for example, $\left\{0\right\}$ is an ideal of the polynomial ring in
all variables, and as a matter of fact $0\in I$ for all ideals of
polynomial rings in all variables.

A subring is a subset that is itself a ring, so $I$ would be a subset
that is closed under addition and multiplication and contains an
additive identity (i.e. $0 \in I$). [^3] As a matter of fact it can be
shown that:

-   $0\in I$

-   $\left\{0\right\}$ is an ideal

for all ideals in all variables and that is an ideal (because otherwise
the result would not be admitted to $I$).

### Example {#sec:org7443404}

Let $R = \mathbb{Z}$ and $I=2\mathbb{Z}$, the set of $\mathbb{Z}$ is a
commutative ring with unity, $2\mathbb{Z}
    \subset \mathbb{Z}$ is:

1.  $2\mathbb{Z} \neq \emptyset$

2.  closed under multiplication and addition

3.  admits any other integer under multiplication (i.e. even $\times$
    anything is even)

## Ideals and Varieties {#sec:orga11e9e1}

If we have a variety of $V \subset K^n$, we denote, $I\left( V \right)$
as the set of all polynomials $f_i\in k\left[ \textbf{X} \right]$ :
[@hibiGrobnerBasesStatistics2014 §1.1.3]

$$\begin{aligned}
      f_i\left( a_1, a_2, a_3, \ldots a_n \right) =0, \quad \forall \left( a_1, a_2, a_3, \ldots a_n \right) \in V
.\end{aligned}$$

this set of functions satisfies the properties of an ideal and is known
as the ideal of V [@coxIdealsVarietiesAlgorithms1997].

In other words, the ideal of the variety of a set of functions,
$I\left( \mathbf{V}\left(F\right) \right)$, is the set of, polynomials,
that have the same zero-points as the simultaneous zero points of all
functions in $F$.

## Generating Ideals {#sec:org509471c}

The ideal generated by $F$ is:

$$\left\langle F\right\rangle =\left\{
    p_{1}f_{1}+p_{2}f_{2}+p_{3}f_{3}+\ldots p_{n}f_{n}\mid f_{i}\in
    F,p_{i}\in K\left[\boldsymbol{X}\right],\forall
    i\in\mathbb{Z}^{+}\right\}$$

Such a set satisfies the properties of an ideal and is a subset of the
functions that share the zero-points with $F$:
[@coxIdealsVarietiesAlgorithms1997 p. 34]

$$\left\langle F \right\rangle \subseteq
    I\left(\boldsymbol{V}\left(F\right)\right)$$

$\left\langle F \right\rangle$ is the set of all the linear combinations
of elements in $F$ with polynomials in $K\left[\mathbf{X}_n\right]$,
another way to phrase it would be that $\left\langle F\right\rangle$ is
the set of polynomial consequences of $F$
[@coxIdealsVarietiesAlgorithms1997 p. 30].

If some **finite** set of polynomials $F$, can generate an ideal $I$, it
is said that $I$ is finitely generated and that $F$ is a basis for $I$.
Every ideal in $K\left[\mathbf{X}_n\right]$ is finitely generated
[@coxIdealsVarietiesAlgorithms1997 p. 77], this is known as *Hilbert's
Basis Theorem*, this is important because it means we if we had an
algorithm that involved taking different polynomials from such a basis,
that algorithm would eventually end.

If two sets are bases of the same ideal, they will have the same
variety, i.e. if two sets can generate the same set of functions,
they'll have the same solutions (assuming that the set of functions is
an ideal), this also implies

### Initial Ideal {#sec:org445b6b1}

The initial ideal:

$$\left\langle
  \mathrm{in}_{\prec}\left(I\right)\right\rangle =\left\langle
  \left\{ \mathrm{in}_{\prec}\left(f\right):0\neq f\in I\right\}
  \right\rangle$$

is generated by infinitely many monomials, namely the initial monomials,
for the infinitely many polynomials in the ideal I.
[@hibiGrobnerBasesStatistics2014 §1.1.5]

It's common also to see a similar definition for the ideal generated by
the leading terms is denoted $\left\langle
  \mathrm{LT}\left(f\right)\right\rangle$
[@coxIdealsVarietiesAlgorithms1997 §2.5].

### Comparison with Linear Algebra {#sec:org76c6b95}

If $S$ is some set of vectors and every vector in a vector subspace $V$
can be written as a linear combination of the elements of $S$ is is said
that $S$ spans $V$, so for example
$S=\left\{ \left\langle 1,0\right\rangle ,\left\langle
    0,1\right\rangle \right\}$ spans $\mathbb{R}^2$ or
$S=\left\{1, x, x^2\right\}$ spans $P_2$.

Ideals for rings are similar in nature to vector subspaces and normal
subgroups. It's worth drawing attention to the fact that that the term
basis in the context of an ideal (which could be more accurately called
a generating set [@sturmfelsSolvingSystemsPolynomial2002]) is quite
different from a linear basis [@coxIdealsVarietiesAlgorithms1997 p. 35].

In linear algebra a basis spans and is linearly independent, the basis
of an ideal however only spans, there is no independence, for example:

$$\begin{aligned}
  f_{1}\left(x,y\right)=y\quad  \quad & \vec{v}_{1}=\left\langle 0,1\right\rangle \\
  f_{2}\left(x,y\right)=x \quad \quad & \vec{v}_{2}=\left\langle
  1,0\right\rangle \end{aligned}$$

Linear independence is generally satisfied if linear combination is
equal to zero, only if the multiplying terms are zero, i.e. $f_1$ and
$f_2$ are linearly independent only if:

$$\begin{aligned}
  0 & =a\left\langle 0,1\right\rangle +b\left\langle 1,0\right\rangle ,\quad\forall a,b\in\mathbb{R}\\
  & =\left\langle a,b\right\rangle \\
  & \implies a=b=0\end{aligned}$$

This clearly doesn't work for polynomials, however, because setting
$g_{i}=x$ and $g_{j}=-y$ satisfies such an equation.

$$0=g_{i}y+g_{j}x,\quad\not\!\!\!\implies g_i=g_j=0, \quad \forall g_{i}g_{j}\in
    k\left[\mathbf{X}\right]$$

So linear independence doesn't have a lot of meaning with polynomials,
it's only the spanning property that is meaningful.

# Initials and Leading Monomials {#sec:orgec30a02}

## Monomial Ordering {#sec:orga3337ef}

Monomials are ordered by degree, e.g. $x \prec x^2$ or $xyz
   \prec x^2yz$, however in many variables it isn't always clear which
order should be chosen, for example the following monomials have the
same degree and if they are ordered by the value on first variable:

$$xy^3 \prec x^2yz$$

If however they are ordered by trying to minimize the last variable:

$$x^2yz \prec xy^3$$

Recall from polynomial long division that the first term in a polynomial
important to the algorithm, for a similar reason it is necessary to
decide before hand on an ordering, and generally in this report the
lexicographic order (i.e. alphabetical) will be used.

This isn't as important as many texts make it out to be and so further
discussion appears further below in
§[9.2](#sec:org5a0a339){reference-type="ref"
reference="sec:org5a0a339"}.

# Groebner Bases {#sec:orgd4f4ac5}

A finite subset $G$ of an ideal $I$ is a Grobner Basis, (with respect to
some term order $\prec$, if:
[@berndsturmfelsIntroductionGrobnerBases2017a; @hibiGrobnerBasesStatistics2014]

$$\left\{ \mathrm{in}_{\prec}\left(g\right)\mid g\in G\right\}$$

generates $\left\{ \mathrm{in}_{\prec}\left(I\right)\right\}$

It's common also to see this definition reformulated with respect to
leading terms as opposed to initial monomials, in which case $G$ is said
to be a Groebner Bases if: [@coxIdealsVarietiesAlgorithms1997 2.5]

$$\mathrm{LT}\left(I\right)=\left\langle \mathrm{LT}\left(g_{1}\right),\mathrm{LT}\left(g_{2}\right),\mathrm{LT}\left(g_{3}\right),\ldots\mathrm{LT}\left(g_{n}\right)\right\rangle$$

there are many such generating sets, we can add any element to G to get
another Groebner Basis, so in practice we may be more concerned with
reduced Groebner Basis. Note also that even though the leading term is
different from the initial monomial, either can be used to define a
Groebner Bases, however it is not yet clear to me if the Groebner Bases
will depend on the monomial ordering $\prec$ only if the initial is used
to define it.

The variety of a set of functions depends only on the ideal of $F$, if
two sets generate the same ideal they have the same variety and if $G$
is a Grobner Basis for F, then $V(G)=V(F)$.

The reason we care about a Groebner Bases more generally is because the
set tends to provide more information of the solution space.

# Buchberger's Criterion {#sec:orgb4fdca1}

$G$ is a Groebner basis, if and only if, every $S$-polynomial formed by
any two pairs from $G$ has a remainder of 0, where the S-polynomial is
given by: [@coxIdealsVarietiesAlgorithms1997 §2.6]

$$S\left(f,g\right)=\mathrm{lcm}\left(\mathrm{LM}\left(f\right),\mathrm{LM}\left(g\right)\right)\times\left(\frac{f}{\mathrm{LT}\left(f\right)}-\frac{g}{\mathrm{LT}\left(g\right)}\right)$$
The remainder that we are concerned with is:

$$r = {\overline{S(f,g)}^{_G}} = S(f,g) \mod \prod_{g\in G} \left(G \right)$$

# Bucherger's Algorithm {#sec:org5742e82}

Buchberger's Algorithm takes a set of polynomials, $F$ and eventually
returns another set $G$ which is a Groebner Bases.

To do this the algorithm tests every pair of polynomials in F with the
criterion above, if the remainder for any pair is non zero, it is placed
into $F$ as another polynomial. Once every combination has been
considered, the original set $F$ will be a Groebner Basis.

## Reduced Groebner Basis {#sec:org8d408a4}

A reduced Groebner Basis is a Groebner Basis that has needless
polynomials discarded, I have not had time to investigate these yet.

## Examples {#sec:orge2124cf}

for examples of Buchberger's Algorithm, refer to the attached *Jupyter
Notebook*, this is quite sparse as resources to understand the algorithm
were discovered quite late in the investigation as was the realisation
that use `sympy` had a significant amount of documentation on the
algorithm.

# Abstract Algebra {#sec:org3828c0d}

The following are concepts that are *nice to have* in understanding the
topic, but are not strictly necessary to get a broad understanding of
the topic.

They were needlessly investigated early on because accessible resources
(e.g.
[@coxIdealsVarietiesAlgorithms1997; @andreasschulzIntegerProgrammingCombinatorial; @sympydevelopmentteamSympyPolysGroebnertools])
had not yet been discovered.

## Background {#sec:orga0d603b}

### Algebra {#sec:orgc7a5871}

#### Relations {#sec:org743ec47}

A relation on a set $A$ is a subset $R$ of the Cartesian product:

$$A\times A=\left\{ \left(a,b\right):\enspace a,b\in A\right\}$$

If $(a,b)\in R$ it is written that $a\enspace R \enspace b$.

##### Example {#sec:orga52d81f}

The example most relevant to the theory of Groebner bases [^4] is the
`<` relation. If we had the set $A = \left\{ 1,\ 2,\ 3 \right\}$

The cartesian product would be:

$$\begin{aligned}
A\times A=\Bigg\{   &\left(1,1\right),\left(1,\ 2\right),\left(1,3\right), \\
            &\left(2,1\right),\left(2,2\right),\left(2,3\right), \\
            &\left(3,\
1\right),\left(3,2\right),\left(3,3\right)\quad\Bigg\}\end{aligned}$$

The set corresponding to the relation \< would be:

$\left\{ \left( 1,2 \right),\ \left( 1,3 \right),\ \left( 2,3 \right) \right\}$

and so it is said that:

-   $1<2$

-   $1<3$

-   $2<3$

##### Types of Relations {#sec:org6926688}

-   **Reflexive** relations are relations where

    -   $\ \forall\ a \in A, a\enspace R \enspace a$

-   **Symmetric** relations are such that

    -   $\forall\ a,b \in A, a\ R\ b \Rightarrow b\ R\ a$

-   **Transitive** relations are such that

    -   $a\ R\ b \land \ \ b\ R\ c \Rightarrow \ a\ R\ c$

        -   $\forall\ a,b,c \in A$

If all of these are satisfied, the relation is said to be *an
equivalence relation*.

##### Why? {#sec:org8b897fd}

Although this might seem needlessly pedantic, the algorithm we hope to
use to find solutions to systems of polynomial equations, Buchberger's
Algorithm, require us to decide on a way to order polynomials, for
example in a quadratic equation it's pretty straight forward:

$$f(x) = ax^2 + bx +c$$

But for multiple variables it gets confusing, for example we could order
the terms by degree, but if multiple terms are of the same degree then
we could make sure that the left most variable has an exponent that is
descending, or, we could try and make sure that the right most term is
ascending:

$$\begin{aligned}
 f\left(w,x,y,z\right)  &=wz+xy \\
             &=xy+wz\end{aligned}$$

This is already pretty confusing so having a firm definition of ordering
is important.

#### Congruence {#sec:org613b72d}

##### Equivalence Classes {#sec:orge6d7a52}

The set of all elements of $A$ that satisfy the relation for $a$ is said
to be the /equivalence class of $a$ with respect to $R$:

$$\left\lbrack a \right\rbrack_{R} = \left\lbrack a \right\rbrack = \left\{ b \in A:b\ R\ a \right\}$$

So returning to the example from
§[9.1.1.1.1](#sec:orga52d81f){reference-type="ref"
reference="sec:orga52d81f"}, we would have:

-   $[1]_<=\emptyset$

-   $[2]_<=\left\{1\right\}$

-   $[3]_<=\left\{1, 2\right\}$

##### Congruence Modulo $n$ {#sec:org8e95ae6}

It is said that $a$ and $b$ are *congruent modulo $n$* if
$n\mid \left(a-b\right)$ and it is written:

$$a\equiv b \pmod{n}$$ It is common to see $\mod$ used as an operator:

$$a \mod b = r$$

The congruence class of $a$ modulo $n$ is expressed $\left[a\right]_n$
and is the equivalence class of $a$ whereby the relation is congruence
in modulo $n$:

$$\left\lbrack a \right\rbrack_{n} = \{ b\mathbb{\in Z\ :}b \equiv a\ \left( \text{mod\ n} \right)\}$$

1.  Example [\[sec:org35225fe\]]{#sec:org35225fe label="sec:org35225fe"}
    Clock time is a congruence class, for example 11 O'clock + 3 hours =
    2 PM:

    $$\left[11\right]_{12}+\left[3\right]_{12}=\left[2\right]_{12}$$

    Another example could be binary:

    $$\left[1\right]_{2}+\left[3\right]_{2}=\left[0\right]_{2}$$

    See also [@roberthowlettUndergraduateCourseAbstract §4c]

2.  Congruence generalised with Groups
    [\[sec:org618b634\]]{#sec:org618b634 label="sec:org618b634"} If $G$
    is a group and $H$ a subgroup, if we have:

    $$a^{-1}b \in H$$

    then it is said:

    $$a \equiv b \pmod{H}$$

    the use of \"$\equiv$\" is appropariate because the relationship is:

    -   reflexive

    -   symmetric

    -   transitive

    and is hence an equiv class.

    consider for example:

    $$12 \mathbb{Z} \leqslant \mathbb{Z}$$

    so we have 5-17 $\in$ 12

    So we write:

    $$5 \equiv 17 \pmod{12\mathbb{Z}}$$

    See [@gregoryleeAbstractAlgebra2018 §3.7].

3.  Congruence Modulo an Ideal [\[sec:orgb24e478\]]{#sec:orgb24e478
    label="sec:orgb24e478"} Congruence can be extended to an ideal on
    any ring structure, that's why we needed to generalise this
    structure, in order to use these theoryies.

    congruence modulo an ideal is

    If I is an ideal in a ring R

    $$a\equiv b\pmod{I}\iff a-b\in I$$

    The use of justified because this is an equivalence relation

    The equivalence class is the set of all elements that satisfy that
    relation for $a$:

    $$\begin{aligned}
          \forall a \in A,& \\
                          &\left[ a \right]_R = \left[ a \right] = \left\{b \in A : b r a \right\}
    .\end{aligned}$$

    So in the context of congruence:

    $$\begin{aligned}
          \foral a \in G &\\
                         & \left[ a \right] = \left\{b\in G : b\equiv a \pmod{H}\right\} 
    .\end{aligned}$$

    if we wanted to find $b$ :

    $$\begin{aligned}
          b &\equiv a \pmod{H}\\
          a^{-1}b &\in H \\
          a^{-1}b &= h, \quad \exists h \in H \\
          b &= ah
    .\end{aligned}$$

    So we have:

    $$\begin{aligned}
          \left[ a \right] = \left\{ah : h \in H\right\} 
    .\end{aligned}$$

    This is known as the left coset [@judsonAbstractAlgebraTheory2016
    §6.1]. The left cosets of $H$ in $G$ partition G:
    [@gregoryleeAbstractAlgebra2018 §3.3]

    1.  Each $a\in G$ is in onlyone left coset, which is $aH$

    2.  $aH \cap bH = \emptyset$ or $aH=bH$

    This can be used to show:

    $$\begin{aligned}
          H \leq G \implies \left\lvert H \right\rvert \mid \left\lvert G \right\rvert
    .\end{aligned}$$

    this is known as Lagranges Theorem. [@gregoryleeAbstractAlgebra2018
    §3.7]

    1.  Normal Subgroups [\[sec:org9dc7199\]]{#sec:org9dc7199
        label="sec:org9dc7199"}

        A normal subgroup is a subgroup $N \leq G$ :

        $$\begin{aligned}
              aN= Na \quad \forall a \in G
        .\end{aligned}$$

        This is not so strict as to require all elements be commutative
        (although commutative groups are of course normal)

4.  Congruence Classes for Polynomials
    [\[sec:org2adce8d\]]{#sec:org2adce8d label="sec:org2adce8d"} If $f$
    and $g$ are in an ideal $I$, then [@coxIdealsVarietiesAlgorithms1997
    p. 240]:

    $$f-g \in I \implies f \equiv g \pmod{I}$$

#### Groups {#sec:org5e14bec}

A set $G$ is a group, if there in a binary operation, $\star$, defined
on that set such that:

1.  The binary operation is closed on the set
    $$a,b \in G \implies a\star b \in G$$

2.  The binary operation is associative

    $$a,b,c \in G \implies a\star (b\star c) = (a\star b)\star c$$

3.  There is an element that doesn't do anything under the binary
    operation, this is known as an identity element, for example 1 is an
    identity element to the multiplication operation.

    $$\begin{aligned}
    \exists e \in G:&\\
            & a\star e = e \star a = a\end{aligned}$$

4.  Every element has an inverse

    $$\begin{aligned}
      \forall a \in G,\enspace \exists a^{-1} \in G:    &\\
                               & a\star a^{-1} = e\end{aligned}$$

    -   For operations that are additive in nature, it is common to use
        the notation: $-a$ [@gregoryleeAbstractAlgebra2018 §3.3]

5.  If the binary operation is also commutative, the group is said to be
    abelian:

    $$\begin{aligned}
    \forall a,b \in G,& \nonumber \\
            & a \star b = b \star a \iff G \text{ is abelian.} \end{aligned}$$

##### Example {#sec:orgb09c6ab}

An example of a group is a set of all matrices of a given size under
addition, this can be seen because:

1.  Adding matrices gives back matrices of the same size,

2.  Introducing brackets in addition doesn't change the result

3.  A matrix with all 0's is an identity

4.  Any matrix $\mathbf{A}$ has an inverse (namely $-\mathbf{A}$)

This example would also be an abelian group because addition is
commutative.

Note that if the operation was matrix multiplication, $\cdot$ (denoted
as `%%` in ***R*** [@rcoreteamLanguageEnvironmentStatistical2020]), only
square matrices with a non-zero determinant (e.g.
$\left\lvert\mathbf{A}\right\rvert \neq 0$) could be a group. This is
because the matrix would need to be invertible. [^5]

##### But Why? {#sec:orgcb36d8d}

The reason groups are interesting is because many natural structures can
be described by a set and a binary operation, obvious examples are sets
of numbers, vectors, matrices and equations, but more generally Group
theory can be used to describe puzzles like *Rubik's Cube*
[@joynerAdventuresGroupTheory2002], chemical structures
[@GroupTheoryIts2013] and has been used in the theory of quantum
mechanics [@tinkhamGroupTheoryQuantum2003]. [^6]

#### Rings {#sec:orgb572ffe}

Examples, equivalence class ring [@judsonAbstractAlgebraTheory2016 Ch.
3] see also §2.4 of nicodemii [@nicodemiIntroductionAbstractAlgebra2007a
§2.4]

Rings are an abelian group under addition $+$, with a second binary
operation that corresponds to multiplication $\times$, this operatuion
must be closed, associative and distributive, but there is no need for
an inverse or identity [@gregoryleeAbstractAlgebra2018 §8.1]. So a ring
structure is a set $\mathcal{R}$, with two closed binary operations,
that satisfies the following axioms of a ring
[@nicodemiIntroductionAbstractAlgebra2007a §§2.4-2.6]:

1.  Associativity of Addition

    $\left( \forall a,b,c \in \mathcal{R} \right) \left( a+ b \right) +  c = a +  \left(  b +  c    \right)$

```{=html}
<!-- -->
```
1.  Commutativity of Addition

    $\left( \forall a,b \in \mathcal{R}  \right) a +  b = b +  a$

2.  Additive Elements Exist

    $\left( \forall a \in \mathcal{R} \right) \wedge \left( \exists 0 \in \mathcal{R} \right) a +  0= 0 +  a =  a$

3.  Additive Inverse Exists

    $\left( \forall a \in \mathcal{R} \right)\wedge \left( \exists b \in \mathcal{R} \right) a +  b =  b +  a = 0$

    -   This can be equivalently expressed:

    $\left( \forall a \in \mathcal{R} \right)\wedge \left( \exists \left( - a\right)\in \mathcal{R} \right) a +  \left( - a \right) = \left( - a \right) +  a = 0$

4.  Associativity of Multiplication

    $\left( \forall a,b,c, \in \mathcal{R} \right)\left( a \cdot  b \right)\cdot c = a \cdot  \left( b \cdot  c \right)$

5.  Distributivity of Multiplication over Addition

    -   $\left( \forall a,b,c, \in \mathcal{R} \right) \left( a\cdot  \left( b+ c \right)=  \left( a \cdot   b  \right) +  \left( a \cdot   c  \right) \right)$,
        AND

    -   $\left( \forall a,b,c, \in \mathcal{R} \right)\left( a +  b \right)\cdot   c = \left( a \cdot   c  \right)+  \left( b \cdot   c \right)$

##### Further Axioms {#sec:orgea4f752}

Other conditions that correspond to different classes of rings are:

1.  Commutativity of Multiplication

    -   A ring that satisfies this property is called a **commutative
        ring**

        $\left( \forall a,b \in \mathcal{R} \right) a \cdot  b = b \cdot  a$

2.  Existence of a Multiplicative Identity Element (A ring with Unity)

    -   A ring that satisfies this property is called a **ring with
        identity** or

    equivalently a **ring with unity** (the multiplicative identity,
    often denoted by $1$, is called the **unity** of the ring.

    $\left( \exists 1 \in \mathcal{R} \right) \left( \forall a \in \mathcal{R} \right) 1 \cdot  a = a \cdot  1 = a$

##### Example {#sec:orge6fc582}

An obvious example of a ring is the set of all integers $\mathbb{Z}$
with the ordinary meaning of addition and multiplication. A more
insightful example would be a congruence class, for example
$\mathbb{Z}_{12}$, this satisfies the axioms of a ring, but some values
are zero divisors. If two elements of a ring multiply to give 0, those
values are said to be zero divisors, for example 3 and 4 are zero
divisors in ~12~:

$$\left[3\right]_{12}\times\left[4\right]_{12}=\left[0\right]_{12}$$

An element that has an inverse is said to be a unit, for example:

$$\left[2\right]_{9}\times\left[5\right]_{9}=\left[1\right]_{9}$$ An
element can't both be a unit and a zero divisor, because one multiplies
to give 0 and the other to give 1, however, in many algebraic structures
(e.g. $\mathbb{Q}, \mathbb{R}$ or $\mathbb{C}$) every element has a
multiplicative inverse, and this motivates the next algebraic structure.

#### Integral Domains {#sec:org75b9387}

An integral domain is a commutative ring with identity that has no zero
divisors.

##### Example {#sec:orgce15308}

The obvious example of an integral domain is $\mathbb{Z}$, but any
$\mathbb{Z}_p$ where $p$ is a prime number, will also be an integral
domain.

Another example is the set of all polynomials with real coefficients,
this will be explored in greater detail below, but for the moment
observe that this algebraic structure conforms to the axioms of a ring
and has no zero divisors.

It can be clearly seen that the set of polynomials has no zero divisors
because:

$$\begin{aligned}
f \times g &= 0 \\
&\implies f = 0, \lor g = 0 \ \\\end{aligned}$$

in either case $f$ or $g$ is not a non-zero divisor.

Note however that not every element of the polynomials has an inverse,
for example the function $f(x)=x$ would have an inverse
$f^{-1}(x)=\frac{1}{x}$, but this is not a polynomial.

This leads to the final algebraic structure that will be considered
here. [^7]

#### Fields {#sec:org5f09c06}

A field is a commutative ring with identity in which all non-zero
elements are units.

Because every element of a field is a unit, it implies that every
element is not a zero-divisor, and so hence a field is:

-   a special case of an integral domain, which is in turn

-   a special case of a ring, which is in turn

-   a special case of a group.

#### Rings and Integral Domains {#sec:org44ae102}

It seems that the reason the theory of Groebner Bases is concerned with
the ring of polynomials over a field is related to the irreducibility of
the polynomial, see generally [@EquivalenceDefinitionsIrreducible].

Note also that the Ring of polynomials over an integral domain (a
property satisfied also by a field) is more accurately an integral
domain
[@sympydevelopmentteamBasicFunctionalityModule; @RingPolynomialForms],
not merely a ring.

##### Why aren't Polynomials fields {#sec:orgb4f303f}

A field is an integral domain, for which every element has an inverse,
so consider some function, say $g(x)=x$, if the set of polynomials was a
field, there would have to exist some $f(x)$ such that:

$$x \cdot f(x) = 1$$

however if we evaluate this at $x=0$

$$0 \cdot f(0) = 1$$

well... this clearly doesn't work, so it's clear that this $f(x)$
doesn't exist and so the set of polynomials is not a field, see
generally [@billdubuqueAbstractAlgebraWhy]

One might wonder if there's a good reason why $f(x)=\frac{1}{x}$ isn't
considered a polynomial, notwithstanding the fact that it doesn't quite
fix this example with 0:

-   All polynomials over the real numbers are continuous, that would
    make this membership inconvenient.

    -   On the other hand there are discontinuities of arbitrary
        polynomials over certain fields, what's a good example of a such
        a field though?

The easy and uninformative answer is that $\frac{1}{x}$ does not have
positive indices, outright violating the definition.

### Vector Spaces {#sec:orgb05a40f}

The ring of polynomials over a field $K$:

$$K\left[x_1, x_2, x_3, \ldots, x_n\right]$$

is a $n$-vector space with a basis given by the set of all power
products:

$$\left\{x_1^{\beta_1}, x_2^{\beta_2}, x_3^{\beta_3}, \ldots x_n^{\beta_n} \right\}$$

#### Basis {#sec:org0905961}

A basis is a set of vectors that [@axlerLinearAlgebraDone2014 p. 39]
are:

-   Linearly independent

-   Spans an $n$-dimensional vector space??

##### Linear Independence {#sec:org6448a14}

a set of vectors are linearly independent if:

$$a_{1}v_{1}+a_{2}v_{2}+a_{3}v_{3}\ldots=0 \iff a_{1}=a_{2}=a_{3}=\ldots=a_{m}$$

##### Span {#sec:orgbadae51}

The span of a set of vectors, is the set of all possible linear
combinations of those vectors.

So for example: $$\begin{aligned}
\mathbb{R}^2&=\mathrm{span}\left( \left\{\left(0,1\right), \left(1, 0\right)\right\}  \right)\\
        &=\mathrm{span}\left( \left\{\left(0,2\right), \left(2, 0\right)\right\}  \right)\\
        &=\mathrm{span}\left( \left\{\left(1,1\right), \left(1, -1\right)\right\}  \right)\\\end{aligned}$$

To visualize this in $\mathbb{R}^2$, imagine that by varying the scaling
value of each vector, any point on $\mathbb{R}^2$ can be reached.

#### Vectors {#sec:org1f848e4}

A ring with unity is a vector space, however a vector space only needs
to be closed under scalar multiplication. This means vector spaces are
not necessarily rings unless the multiplication operation is closed, an
example of a closed vector multiplication is element-wise
multiplication, this is known as the hadamard product (think like
mutliplying 'numpy' arrays.)

## Monomial Orders {#sec:org5a0a339}

[groebner bases of a system of
equations](20210406222024-groebner_bases_of_a_system_of_equations.org) A
partial order on a set is a relation $R$:

-   $x R x$

    -   reflexivity

-   $x R y \land y R x \implies x = y$

    -   Antisymmetry

-   $x R y \land y R z \implies x R z$

    -   Transitivity

So for example, the set of integers has $\leq$ as a relation such that
$n_1\in \mathbb{Z}:$

-   $n\leq n$

-   $n_1\leq n_2 \land n_2 \leq n_1 \implies n_1=n_2$

-   $n_1\leq n_2 \land n_2 \leq n_3 \implies n_1\leq n_3$

A partially ordered set is one with a relation that is a partial order.

-   partial order

    -   a relation

-   partially ordered set

    -   a set

A total order is a partial order such that $\forall x,y$ either $x R y$
or $y R x$, the obvious example is $<$, consider for example
$\mathbb{C}$, this has a partial order if the the modulus is considered,
it's only a partial order because, e.g.
$\left\lvert i+i \right\rvert= \left\lvert i-i \right\rvert$. not all
sets will have a partial ordering, e.g. the somewhat contrived example
has no (at least obvious) partial order.

$$\left\{\square, \triangle, \sqrt{-1} x^{e^x} \right\} 
.$$

$k\left[ \mathbf{X} \right]$ is a polynomial ring in $n$ variables and
$\mathcal{M}_n$ is the set of amonomials in the variables
$x_1, x_2, x_3, \ldots x_n$.

A monomial order on $k\left[ \mathbf{X} \right]$ is a total order on
$\prec$ on $\mathcal{M}_n$:

1.  $i \prec u, \quad \forall 1\in u\in \mathcal{M}_n$

2.  $u, v\in \mathcal{M}_n \land u \prec v \implies uw \prec vw, \forall w \in \mathcal{M}_n$

#### Lexical monomial order {#sec:orgca3f61a}

Let:

$$\begin{aligned}
     u &= x_1^{a_1} x_2^{a_2} x_3^{a_3} \ldots x_n^{a_n} \\
     v &= x_1^{b_1} x_2^{b_2} x_3^{b_3} \ldots x_n^{b_n}
 .\end{aligned}$$ The lexicographic order on
$k\left( \mathbf{X} \right)$ is given by the total order
$<_{\mathrm{lex}}$ on $\mathcal{M}_n$ by setting:

$$\begin{aligned}
     u <_{\mathrm{lex}} v
 .\end{aligned}$$

if:

1.  $\sum^{n}_{i=1}\left[ a_i  \right] \leq \sum^{n}_{i=1}\left[ b_i  \right]$

2.  the leftmost non-zero term in the following vector is positive:

    -   b~1~-a~1~, b~2~-a~2~, b~3~-a~3~ ...b~n~-a~n~

Reverse lexicographic is:

1.  $\sum^{n}_{i=1}\left[ a_i  \right] \leq \sum^{n}_{i=1}\left[ b_i  \right]$

2.  the **rightmost** non-zero term in the following vector is
    **negative**:

    -   b~1~-a~1~, b~2~-a~2~, b~3~-a~3~ ...b~n~-a~n~

These should be combined into one statement $\uparrow$

So for example consider: $$x_1x_4-x_2x_3
 .$$

by lexicographic we have

$$x_2x_3\prec x_1x_4
 .$$

because the leftmost entry is positive in the vector described before:

$$\left\langle 1, -1, -1, 1\right \rangle
 .$$

by reverse lexicographic we have

$$x_1x_4 \prec x_2x_3
 .$$

because the **rightmost** entry is **negative** in the vector described
before:

$$\left\langle -1, 1, 1, -1\right \rangle
 .$$

This may be discussed more in the org mode note.

an interesting property that comes back in the buchberger algorithm and
polynomial long division is:

$$\mathrm{in}_{\prec}\left( f \cdot g \right) = \mathrm{in}_{\prec}\left( f \right) \mathrm{in}_{\prec}\left( g \right) 
 .$$

#### Colloquial {#sec:org93e3f5b}

##### Lexicographic {#sec:org3730d87}

The highest variable is so expensive that it makes the entire monomial
expensive.

##### Reverse Lexicographic {#sec:org6c77df3}

The lowest variable is so chap that it makes the entire monomial cheap.

## Dickson's Lemma {#sec:org71762fc}

### Divisors {#sec:org2b3dd0c}

For *monomials*:

-   $u= \prod^n_{i=1}\left[ x_i^a_i \right] \quad a \in \mathbb{Z^+}$

-   $v= \prod^n_{i=1}\left[ x_i^b_i \right] \quad b \in \mathbb{Z^+}$

$u$ is said to divide $v$ if
$a_i \leq b_i \quad \forall i \in \left[ 1, n \right]$

#### Example {#sec:org85e8673}

Consider:

-   $u = x^2y^3z^5$

-   $v = x^1y^2z^3$

In this case $v \mid u$ because:

$$\begin{aligned}
      1 &< 2 \\
      2 &< 3 \\
      3 &< 5 \\
      \ \\
      \frac{u}{v} &= \frac{x^2}{x^1} \cdot \frac{y^3}{y^2} \cdot  \frac{z^5}{z^3}
.\end{aligned}$$

### Minimal Element {#sec:org5f6d987}

let $\mathcal{M}_n$ be the set of a all monomials in the variables
$x_1, x_2, x_3, \ldots x_n$ and $M \subset \mathcal{M}_n$ be a nonempty
subset thereof.

The following condition describes a minimal element $u\in M$:

$$\left(v \in M \land v \mid u\right) \implies v = u$$

In other words, $u$ is a minimal element if the only way that $v
    \mid u$ is if $v = u$.

#### Example {#sec:orgef073aa}

Consider $\mathcal{M}_2$:

$$\begin{aligned}
{3}
  \mathcal{M}_2 &= \{&x  y, &x  y^2, &x  y^3, \ldots         \\
                &    &      &x^2y,   &x^2y^2, x^2y^3, \ldots \\
                &    &      &x^3y,   &x^3y^2, x^3y^3, \ldots \\
                &    &      & \vdots &                       \\
          \}\end{aligned}$$

and let's have the subset $M = \left\{ x^2y, x^2y^2, x^2y^3 \ldots
     \right\}$, the minimum elements are:

$$\left\{x^2y\right\}$$

clearly $\left\lvert M \right\rvert = \infty$, however this number of mi
um elements will always be finite, this is known as **Dickson's Lemma**.

### Dickson's Lemma {#sec:orga0a8af0}

> /Dickson's Lemma is the main result needed to prove the termination of
> Buchberger's algorithm for computing Groebner basis of polynomial
> ideals/ [@martin-mateosFormalProofDickson2003].

Let

-   $\mathcal{M}_n$ be the set of all monomials in variables
    $x_1, x_2, x_3 \ldots x_n$.

-   $M$ be a nonempty subset of $\mathcal{M}_n$

> *The set of minimal elements of a nonempty subset $M \subset
>     \mathcal{M}_n$ is at most finite.*

This intuitively makes sense, I can't have an infinite number of
minimums, otherwise they wouldn't be minimums, the proof is very
difficult though.

#### In one Variable {#sec:org77f5313}

By definition, a monomial is raised to the power of a non-zero integer,
in a single variable monomial the smallest index will correspond to the
minimal element (by the definition of the minimal element) and hence the
existence of a minimum element in implies the existence of a minimum
element in $M\subset \mathcal{M}_n$.

#### In Two Variables {#sec:orgc4d2085}

Assume that there is an infinite number of minimal elements:

$$\begin{aligned}
      u_1 &= x^{a_1}y^{b_1} \\
      u_2 &= x^{a_2}y^{b_2} \\
      u_3 &= x^{a_3}y^{b_3} \\
      u_4 &= x^{a_4}y^{b_4} \\
      u_5 &= x^{a_5}y^{b_5} \\
      \ldots \nonumber\end{aligned}$$ Let's order the values by the
first exponential such that $a_1 \leq a_2 \leq a_3 \ldots$.

If $a_i=a_{i+1}$, then either:

-   $u_1 = u_{i+1}$

    -   We can't have this because set's do not contain repeated
        elements.

-   $y^{b_i} \neq y^{b_{i+1}}$

    -   But this would mean that either $u_i$ or $u_{i+1\}$ is not a
        minimal element, so this can't occur either.

This means that each $a_i$ must be different and so:

$$\begin{aligned}
a_i < a_2 < a_3 \ldots\end{aligned}$$

If $u_i | u_{i+1}$ one of them is not a minimal element and so we must
have $b_i > b_{i+1}$, hence $b_i > b_2 > b_3 \ldots$.

This means that $b_i$ represents an upper bound for the number of
different minimal elements, hence the number of minimal elements must be
finite.

#### In $n$ variables[induction]{.smallcaps} {#sec:orgb0a1960}

If the number of minimal elements is finite for $M_n \subset
     \mathcal{M}_n$ we would expect $M_{n+1}$ to be finite as well,
adding an extra variable should not make the number of minimal elements
infinite because the integers in the index will still behave as an upper
bound.

I need to formalise this as per [@hibiGrobnerBasesStatistics2014
§1.1.2].

[^1]: In the absence of better materials a lot of time was wasted (yes,
    wasted, not spent) on complex algebraic concepts when all I needed
    was an algorithm to experiment with, an algorithm that the complex
    texts would not provide.

[^2]: This also lines up with `sympy`'s `LT()` function, beware not to
    confuse the initial with the leading term, different algorithms or
    ways to calculate an $S$-polynomial seem to use either and it
    doesn't matter, I'm not sure why yet, but I am sure that there is a
    difference between the initial monomial and the leading term.

[^3]: It would also be sufficient to show that the $I$ is closed under
    both addition and subtraction [@judsonAbstractAlgebraTheory2016
    §16.1]

[^4]: Relevant because we need to decide on an ordering relation in
    order to use Buchberger's algorithm, which is needed to find a
    Groebner Basis.

[^5]: although the element-wise product, $\odot$, would not present this
    issue.

[^6]: See generally this [@19328] *Stack Exchange Discussion*.

[^7]: There are other algebraic structures that could be interesting,
    for example polynomials can also be considered as vectors, see e.g.
    [@larsonElementaryLinearAlgebra1991a], as a matter of fact all
    vector spaces are rings if multiplication is defined element-wise by
    the *Hadamard product* ($\odot$), this could be an interesting
    relationship to investigate further.
```bibtex
@ONLINE{82645,
  AUTHOR = {(https://math.stackexchange.com/users/5887/ilya), Ilya},
  URL = {https://math.stackexchange.com/q/82645},
  EPRINT = {https://math.stackexchange.com/q/82645},
  HOWPUBLISHED = {Mathematics Stack Exchange},
  TITLE = {Root or Zero...Which to Use When?},
}

@BOOK{adamsIntroductionGrobnerBases1994,
  AUTHOR = {Adams, William W. and Loustaunau, Philippe},
  LOCATION = {Providence, R.I},
  PUBLISHER = {American Mathematical Society},
  DATE = {1994},
  ISBN = {978-0-8218-3804-4},
  KEYWORDS = {Gröbner bases},
  NUMBER = {v. 3},
  PAGETOTAL = {289},
  SERIES = {Graduate Studies in Mathematics},
  TITLE = {An Introduction to {{Gröbner}} Bases},
}

@ONLINE{19328,
  AUTHOR = {{Alex B.}},
  URL = {https://math.stackexchange.com/q/19328},
  EPRINT = {https://math.stackexchange.com/q/19328},
  HOWPUBLISHED = {Mathematics Stack Exchange},
  TITLE = {Why Should We Care about Groups at All?},
}

@ONLINE{andreasschulzIntegerProgrammingCombinatorial,
  ABSTRACT = {The course is a comprehensive introduction to the theory, algorithms and applications of integer optimization and is organized in four parts: formulations and relaxations, algebra and geometry of integer optimization, algorithms for integer optimization, and extensions of integer optimization.},
  AUTHOR = {{Andreas Schulz}},
  ORGANIZATION = {MIT OpenCourseWare},
  URL = {https://ocw.mit.edu/courses/sloan-school-of-management/15-083j-integer-programming-and-combinatorial-optimization-fall-2009/},
  FILE = {/home/ryan/Zotero/storage/L4YBT428/15-083j-fall-2009.zip;/home/ryan/Zotero/storage/LVWBWABH/andreasschulzIntegerProgrammingCombinatorial.pdf;/home/ryan/Zotero/storage/YBMJ6ZJP/15-083j-integer-programming-and-combinatorial-optimization-fall-2009.html},
  LANGID = {english},
  TITLE = {Integer {{Programming}} and {{Combinatorial Optimization}}},
  URLDATE = {2021-04-08},
}

@BOOK{axlerLinearAlgebraDone2014,
  AUTHOR = {Axler, Sheldon},
  LOCATION = {New York},
  PUBLISHER = {Springer},
  DATE = {2014},
  ISBN = {978-3-319-11079-0},
  TITLE = {Linear Algebra Done Right},
}

@BOOK{beckerGrobnerBasesComputational1993,
  AUTHOR = {Becker, Thomas and Weispfenning, Volker and Kredel, Heinz},
  LOCATION = {New York},
  PUBLISHER = {Springer-Verlag},
  DATE = {1993},
  ISBN = {978-0-387-97971-7 978-3-540-97971-5},
  KEYWORDS = {Algebra,Data processing,Gröbner bases},
  NUMBER = {141},
  PAGETOTAL = {574},
  SERIES = {Graduate Texts in Mathematics},
  SHORTTITLE = {Gröbner Bases},
  TITLE = {Gröbner Bases: A Computational Approach to Commutative Algebra},
}

@VIDEO{berndsturmfelsIntroductionGrobnerBases2017a,
  ABSTRACT = {Using Grobner bases to perform Gaussian elimination on non-linear systems, apply the Euclidean algorithm to multivariate systems and run the Simplex algorithm in a minimisation problem.},
  EDITOR = {{Bernd Sturmfels}},
  URL = {https://www.youtube.com/watch?v=TNO5WuxuNak},
  DATE = {2017-01-21},
  EDITORTYPE = {director},
  TITLE = {Introduction to {{Grobner Bases}} - {{Prof}}. {{Bernd Sturmfels}}},
  URLDATE = {2021-04-12},
}

@ONLINE{billdubuqueAbstractAlgebraWhy,
  AUTHOR = {{Bill Dubuque}},
  ORGANIZATION = {Mathematics Stack Exchange},
  URL = {https://math.stackexchange.com/a/2523},
  FILE = {/home/ryan/Zotero/storage/EXPAEFUF/why-cant-the-polynomial-ring-be-a-field.html},
  TITLE = {Abstract Algebra - {{Why}} Can't the {{Polynomial Ring}} Be a {{Field}}?},
  URLDATE = {2021-04-12},
}

@BOOK{coxIdealsVarietiesAlgorithms1997,
  AUTHOR = {Cox, David A. and Little, John B. and O'Shea, Donal},
  LOCATION = {New York},
  PUBLISHER = {Springer},
  DATE = {1997},
  EDITION = {2nd ed},
  ISBN = {978-0-387-94680-1},
  KEYWORDS = {Commutative algebra,Data processing,Geometry; Algebraic},
  PAGETOTAL = {536},
  SERIES = {Undergraduate Texts in Mathematics},
  SHORTTITLE = {Ideals, Varieties, and Algorithms},
  TITLE = {Ideals, Varieties, and Algorithms: An Introduction to Computational Algebraic Geometry and Commutative Algebra: With 91 Illustrations},
}

@BOOK{e.h.connellElementsAbstractLinear2001,
  AUTHOR = {{E. H. Connell}},
  PUBLISHER = {University of Miami},
  URL = {http://www.math.miami.edu/~ec/book/},
  DATE = {2001-03-30},
  TITLE = {Elements of {{Abstract}} and {{Linear Algebra}}},
}

@ONLINE{EquivalenceDefinitionsIrreducible,
  URL = {https://proofwiki.org/wiki/Equivalence_of_Definitions_of_Irreducible_Polynomial_over_Field},
  FILE = {/home/ryan/Zotero/storage/4QIAYSA5/Equivalence_of_Definitions_of_Irreducible_Polynomial_over_Field.html},
  TITLE = {Equivalence of {{Definitions}} of {{Irreducible Polynomial}} over {{Field}} - {{ProofWiki}}},
  URLDATE = {2021-04-12},
}

@BOOK{gregoryleeAbstractAlgebra2018,
  AUTHOR = {{Gregory Lee}},
  LOCATION = {New York, NY},
  PUBLISHER = {Springer Berlin Heidelberg},
  DATE = {2018},
  ISBN = {978-3-319-77648-4},
  TITLE = {Abstract Algebra},
}

@BOOK{grilletAbstractAlgebra2007,
  AUTHOR = {Grillet, Pierre A.},
  LOCATION = {New York, NY},
  PUBLISHER = {Springer},
  ANNOTATION = {OCLC: 255964387},
  DATE = {2007},
  EDITION = {2. ed},
  FILE = {/home/ryan/Zotero/storage/YN5U3F5G/grilletAbstractAlgebra2007.pdf},
  ISBN = {978-0-387-71568-1 978-0-387-71567-4},
  LANGID = {english},
  NUMBER = {242},
  PAGETOTAL = {669},
  SERIES = {Graduate Texts in Mathematics},
  TITLE = {Abstract Algebra},
}

@ONLINE{GroupTheoryIts2013,
  ORGANIZATION = {Chemistry LibreTexts},
  URL = {https://chem.libretexts.org/Bookshelves/Physical_and_Theoretical_Chemistry_Textbook_Maps/Supplemental_Modules_(Physical_and_Theoretical_Chemistry)/Group_Theory/Group_Theory_and_its_Application_to_Chemistry},
  DATE = {2013-10-02T16:55:55Z},
  FILE = {/home/ryan/Zotero/storage/PTWG4AXF/Group_Theory_and_its_Application_to_Chemistry.html},
  LANGID = {english},
  TITLE = {Group {{Theory}} and Its {{Application}} to {{Chemistry}}},
  URLDATE = {2021-04-10},
}

@BOOK{hibiGrobnerBasesStatistics2014,
  AUTHOR = {Hibi, Takayuki},
  URL = {http://www.vlebooks.com/vleweb/product/openreader?id=none&isbn=9784431545743},
  ANNOTATION = {OCLC: 1100912580},
  DATE = {2014},
  ISBN = {978-4-431-54574-3},
  LANGID = {english},
  SHORTTITLE = {Grobner {{Bases}}},
  TITLE = {Grobner {{Bases}}: {{Statistics}} and {{Software Systems}}},
  URLDATE = {2021-03-03},
}

@BOOK{joynerAdventuresGroupTheory2002,
  AUTHOR = {Joyner, David},
  LOCATION = {Baltimore},
  PUBLISHER = {Johns Hopkins University Press},
  ANNOTATION = {OCLC: ocm48013200},
  DATE = {2002},
  ISBN = {978-0-8018-6945-7 978-0-8018-6947-1},
  KEYWORDS = {Group theory,Mathematical recreations},
  PAGETOTAL = {262},
  SHORTTITLE = {Adventures in Group Theory},
  TITLE = {Adventures in Group Theory: {{Rubik}}'s {{Cube}}, {{Merlin}}'s Machine, and Other Mathematical Toys},
}

@BOOK{judsonAbstractAlgebraTheory2016,
  ABSTRACT = {This text is intended for a one- or two-semester undergraduate course in abstract algebra. Traditionally, these courses have covered the theoretical aspects of groups, rings, and fields. However, with the development of computing in the last several decades, applications that involve abstract algebra and discrete mathematics have become increasingly important, and many science, engineering, and computer science students are now electing to minor in mathematics. Though theory still occupies a central role in the subject of abstract algebra and no student should go through such a course without a good notion of what a proof is, the importance of applications such as coding theory and cryptography has grown significantly. Until recently most abstract algebra texts included few if any applications. However, one of the major problems in teaching an abstract algebra course is that for many students it is their first encounter with an environment that requires them to do rigorous proofs. Such students often find it hard to see the use of learning to prove theorems and propositions; applied examples help the instructor provide motivation. This text contains more material than can possibly be covered in a single semester. Certainly there is adequate material for a two-semester course, and perhaps more; however, for a one-semester course it would be quite easy to omit selected chapters and still have a useful text. The order of presentation of topics is standard: groups, then rings, and finally fields. Emphasis can be placed either on theory or on applications. A typical one-semester course might cover groups and rings while briefly touching on field theory, using Chapters 1 through 6, 9, 10, 11, 13 (the first part), 16, 17, 18 (the first part), 20, and 21. Parts of these chapters could be deleted and applications substituted according to the interests of the students and the instructor. A two-semester course emphasizing theory might cover Chapters 1 through 6, 9, 10, 11, 13 through 18, 20, 21, 22 (the first part), and 23. On the other hand, if applications are to be emphasized, the course might cover Chapters 1 through 14, and 16 through 22. In an applied course, some of the more theoretical results could be assumed or omitted. A chapter dependency chart appears below. (A broken line indicates a partial dependency.).},
  AUTHOR = {Judson, Thomas W and {Open Textbook Library}},
  URL = {https://open.umn.edu/opentextbooks/textbooks/217, http://abstract.pugetsound.edu/},
  ANNOTATION = {OCLC: 1151064240},
  DATE = {2016},
  FILE = {/home/ryan/Zotero/storage/UWR3XHJM/Judson - Abstract Algebra.pdf},
  ISBN = {978-1-944325-02-2},
  LANGID = {In English.},
  TITLE = {Abstract Algebra Theory and Applications},
  URLDATE = {2021-04-10},
}

@MISC{judyholdenerAlgebraicGeometry2013,
  AUTHOR = {{Judy Holdener}},
  URL = {http://pi.math.cornell.edu/~dmehrle/notes/old/alggeo/},
  DATE = {2013},
  FILE = {/home/ryan/Zotero/storage/PX46QLIT/out.html},
  TITLE = {Algebraic {{Geometry}}},
}

@BOOK{larsonElementaryLinearAlgebra1991a,
  AUTHOR = {Larson, Ron and Edwards, Bruce H.},
  LOCATION = {Lexington, Mass},
  PUBLISHER = {D.C. Heath},
  DATE = {1991},
  EDITION = {2nd ed},
  ISBN = {978-0-669-24592-9},
  KEYWORDS = {Algebras; Linear},
  PAGETOTAL = {592},
  TITLE = {Elementary Linear Algebra},
}

@INPROCEEDINGS{martin-mateosFormalProofDickson2003,
  ABSTRACT = {.Dickson’s Lemma is the main result needed to prove the termination of Buchberger’s algorithm for computing Gröbner basis of polynomial ideals. In this case study, we present a formal proof of Dickson’s Lemma using the ACL2 system. Due to the limited expressiveness of the ACL2 logic, the classical non-constructive proof of this result cannot be done in ACL2. Instead, we formalize a proof where the termination argument is justified by the multiset extension of a well-founded relation.},
  AUTHOR = {Martın-Mateos, F. J. and Alonso, J. A. and Hidalgo, M. J. and Ruiz-Reina, J. L.},
  EDITOR = {Vardi, Moshe Y. and Voronkov, Andrei},
  LOCATION = {Berlin, Heidelberg},
  PUBLISHER = {Springer},
  BOOKTITLE = {Logic for {{Programming}}, {{Artificial Intelligence}}, and {{Reasoning}}},
  DATE = {2003},
  DOI = {10.1007/978-3-540-39813-4_3},
  FILE = {/home/ryan/Zotero/storage/2QE2HIQQ/Martın-Mateos et al. - 2003 - A Formal Proof of Dickson’s Lemma in ACL2.pdf},
  ISBN = {978-3-540-39813-4},
  KEYWORDS = {Common Lisp,Constructive Proof,Formal Proof,Recursive Call,Reducible Pattern},
  LANGID = {english},
  PAGES = {49--58},
  SERIES = {Lecture {{Notes}} in {{Computer Science}}},
  TITLE = {A {{Formal Proof}} of {{Dickson}}’s {{Lemma}} in {{ACL2}}},
}

@BOOK{nicodemiIntroductionAbstractAlgebra2007a,
  AUTHOR = {Nicodemi, Olympia and Sutherland, Melissa A. and Towsley, Gary W.},
  LOCATION = {Upper Saddle River, NJ},
  PUBLISHER = {Pearson Prentice Hall},
  ANNOTATION = {OCLC: 253915717},
  DATE = {2007},
  ISBN = {978-0-13-101963-8},
  LANGID = {english},
  PAGETOTAL = {436},
  TITLE = {An Introduction to Abstract Algebra with Notes to the Future Teacher},
}

@ONLINE{pabloparriloAlgebraicTechniquesSemidefinite,
  ABSTRACT = {This research-oriented course will focus on algebraic and computational techniques for optimization problems involving polynomial equations and inequalities with particular emphasis on the connections with semidefinite optimization. The course will develop in a parallel fashion several algebraic and numerical approaches to polynomial systems, with a view towards methods that simultaneously incorporate both elements. We will study both the complex and real cases, developing techniques of general applicability, and stressing convexity-based ideas, complexity results, and efficient implementations. Although we will use examples from several engineering areas, particular emphasis will be given to those arising from systems and control applications.},
  AUTHOR = {{Pablo Parrilo}},
  ORGANIZATION = {MIT OpenCourseWare},
  URL = {https://ocw.mit.edu/courses/electrical-engineering-and-computer-science/6-972-algebraic-techniques-and-semidefinite-optimization-spring-2006/},
  FILE = {/home/ryan/Zotero/storage/DZ4MR7XB/lecture_13.pdf;/home/ryan/Zotero/storage/WFJHQ7E9/6-972-spring-2006.zip;/home/ryan/Zotero/storage/42Y8TNGS/index.html},
  LANGID = {english},
  TITLE = {Algebraic {{Techniques}} and {{Semidefinite Optimization}}},
  URLDATE = {2021-04-08},
}

@VIDEO{prof.berndsturmfelsIntroductionGrobnerBases2017,
  ABSTRACT = {Using Grobner bases to perform Gaussian elimination on non-linear systems, apply the Euclidean algorithm to multivariate systems and run the Simplex algorithm in a minimisation problem.},
  EDITOR = {{Prof. Bernd Sturmfels}},
  URL = {https://www.youtube.com/watch?v=TNO5WuxuNak},
  DATE = {2017-01-20},
  EDITORTYPE = {director},
  TITLE = {Introduction to {{Grobner Bases}} - {{Prof}}. {{Bernd Sturmfels}}},
  URLDATE = {2021-04-12},
}

@ONLINE{RingPolynomialForms,
  URL = {https://proofwiki.org/wiki/Ring_of_Polynomial_Forms_is_Integral_Domain},
  FILE = {/home/ryan/Zotero/storage/YICHLU7S/Ring_of_Polynomial_Forms_is_Integral_Domain.html},
  TITLE = {Ring of {{Polynomial Forms}} Is {{Integral Domain}} - {{ProofWiki}}},
  URLDATE = {2021-04-12},
}

@BOOK{roberthowlettUndergraduateCourseAbstract,
  AUTHOR = {{Robert Howlett}},
  URL = {https://www.maths.usyd.edu.au/u/bobh/UoS/},
  TITLE = {An Undergraduate Course in {{Abstract Algebra}}: {{Course}} Notes for {{MATH3002}}},
}

@BOOK{sturmfelsSolvingSystemsPolynomial2002,
  EDITOR = {Sturmfels, Bernd},
  LOCATION = {Providence, R.I},
  PUBLISHER = {Published for the Conference Board of the Mathematical Sciences by the American Mathematical Society},
  ANNOTATION = {OCLC: ocm50273026},
  DATE = {2002},
  EVENTTITLE = {{{CBMS Conference}} on {{Solving Polynomial Equations}}},
  ISBN = {978-0-8218-3251-6},
  KEYWORDS = {Congresses,Equations,Numerical solutions,Polynomials},
  NUMBER = {no. 97},
  PAGETOTAL = {152},
  SERIES = {Conference {{Board}} of the {{Mathematical Sciences}} Regional Conference Series in Mathematics},
  TITLE = {Solving Systems of Polynomial Equations},
}

@ONLINE{sympydevelopmentteamBasicFunctionalityModule,
  AUTHOR = {{SymPy Development Team}},
  ORGANIZATION = {Sympy Documentation},
  URL = {https://docs.sympy.org/latest/modules/polys/basics.html},
  FILE = {/home/ryan/Zotero/storage/A6KUTH88/basics.html},
  TITLE = {Basic Functionality of the Module — {{SymPy}} 1.8 Documentation},
  URLDATE = {2021-04-11},
}

@ONLINE{sympydevelopmentteamGrobnerBasesTheir2021,
  AUTHOR = {{SymPy Development Team}},
  ORGANIZATION = {Sympy Documentation},
  URL = {https://mattpap.github.io/masters-thesis/html/src/groebner.html},
  DATE = {2021-04-09},
  FILE = {/home/ryan/Zotero/storage/LIX9PLRR/groebner.html},
  TITLE = {Gröbner Bases and Their Applications — {{Polynomials Manipulation Module}} v1.0 Documentation},
  URLDATE = {2021-04-11},
}

@ONLINE{sympydevelopmentteamSympyPolysGroebnertools,
  AUTHOR = {{SymPy Development Team}},
  ORGANIZATION = {Sympy Documentation},
  URL = {http://www.caacle.com/sympy-docs-html-1.4/_modules/sympy/polys/groebnertools.html},
  FILE = {/home/ryan/Zotero/storage/PMBGID2K/groebnertools.html},
  TITLE = {Sympy.Polys.Groebnertools — {{SymPy}} 1.4 Documentation},
  URLDATE = {2021-04-12},
}

@ONLINE{sympydevelopmentteamSympySolversPolysys,
  AUTHOR = {{SymPy Development Team}},
  ORGANIZATION = {Sympy Documentation},
  URL = {http://man.hubwiz.com/docset/SymPy.docset/Contents/Resources/Documents/_modules/sympy/solvers/polysys.html},
  FILE = {/home/ryan/Zotero/storage/2E29FENT/polysys.html},
  TITLE = {Sympy.Solvers.Polysys — {{SymPy}} 1.4 Documentation},
  URLDATE = {2021-04-11},
}

@SOFTWARE{rcoreteamLanguageEnvironmentStatistical2020,
  AUTHOR = {Team, R Core},
  LOCATION = {Vienna, Austria},
  ORGANIZATION = {R Foundation for Statistical Computing},
  URL = {http://www.R-project.org/},
  DATE = {2020},
  TITLE = {R: {{A Language}} and {{Environment}} for {{Statistical Computing}}},
}

@BOOK{tinkhamGroupTheoryQuantum2003,
  AUTHOR = {Tinkham, Michael},
  LOCATION = {Mineola, N.Y},
  PUBLISHER = {Dover Publications},
  DATE = {2003},
  ISBN = {978-0-486-43247-2},
  KEYWORDS = {Group theory,Quantum theory},
  PAGETOTAL = {340},
  TITLE = {Group Theory and Quantum Mechanics},
}

@ONLINE{WrongGroebnerBasis,
  ABSTRACT = {In [17]: from sympy.polys.polytools import groebner In [18]: groebner([0.144*x*y+0.018*x**2+0.05*x-1.577,0.072*y**2+0.036*x*y+0.05*y-1.423], [x, y]) Out[18]: GroebnerBasis([1.0], x, y, domain=ℝ, or...},
  ORGANIZATION = {GitHub},
  URL = {https://github.com/sympy/sympy/issues/11623},
  FILE = {/home/ryan/Zotero/storage/5Q5UTUBV/11623.html},
  LANGID = {english},
  TITLE = {Wrong Groebner Basis · {{Issue}} \#11623 · Sympy/Sympy},
  URLDATE = {2021-04-11},
}

```
