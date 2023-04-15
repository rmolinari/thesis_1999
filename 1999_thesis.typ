//
#let thesis_title = "Properties of relative recursive enumerability"
#let author = "Rory Molinari"

#let setdiff(a, b) = $#a tilde.op #b$
#let turinginterval(a, b) = $[#a, #b]_T$
#let leqt = $lt.eq_T$
#let emptyset = $nothing$

#let restr(a, b) = $#a harpoon.tr #b$
#let concat(a, b) = $#a paren.t #b$

#let reIn(z) = $"r.e."[#z]$
#let reInAbove(z) = $"REA"[#z]$
#let dreInAbove(z) = $"d"reInAbove(#z)$

#let phi = sym.phi.alt

// Global formatting
#set par(justify: true)

// Title page
#align(horizon + center)[
    #[
        #set text(weight: "bold", size: 16pt)
        #thesis_title
    ]
    #v(1in)
    by \
    #author

    #v(1in)
    A dissertation submitted in partial fulfillment \
    of the requirements for the degree of \
    Doctor of Philosophy \
    (Mathematics) \
    in The University of Michigan \
    1999

    #v(1in)
    #box(
        width: 3in
    )[
        #align(left)[
            #set par(hanging-indent: 0.5in)
            Doctoral Committee: \
            Professor Peter Hinman, Chair \
            Professor Andreas Blass, \
            Professor Philip Hanlon, \
            Assistant Professor Peter Selinger, \
            Associate Professor Jamie Tappenden
        ]
    ]

    #pagebreak()
    #pagebreak()
    #box(width: 2in)[
        #sym.copyright
        #h(3em)
        #box[
            #align(horizon + left)[
              #underline[Rory Molinari] #h(1em) 1999 \
              All Rights Reserved
             ]
        ]
    ]
    #pagebreak()
]

#heading(numbering: none, "ACKNOWLEDGEMENTS")

#v(0.5in)
I would first like to thank my adviser, Peter Hinman, without whose patience, encouragement, and help this thesis would not exist.

Thanks also go to all my friends, both inside and outside the Department, and to my family. Without their constant support these
past six years would have been long indeed.

Finally, I will be eternally grateful to the people of Michigan and the other United States, whose generosity made by studies at the
University possible, and whose unfailing hospitality made me feel welcome.

#pagebreak()
#outline()

#pagebreak()

// Experimental. Based on something I found it in the Discord from user Heinenen 04/05/2023
#show heading.where(level: 1): it => {
    pagebreak()
    v(2in)
    set text(weight: "bold")
    align(center)[
      CHAPTER #counter(heading).display()\
      #v(0.5em)
      #it.body
      #v(0.2em)
    ]
}

= Introduction
== Definitions and notation

The notation used in this paper is largely standand, and the reader is directed to @Soare1987 for an exposition. We note the
following.

Uppercase Greek letters, $Phi, Psi, dots$ will denote recursive functionals, with associated uses $phi, psi, dots$ where the
oracle will be understood from context. Without loss of generality we assume that $phi(x, s)$ is increasing in both arguments.

We use $subset$ to denote the subset relation, and $subset.neq$ to denote a proper subset. Set difference is denoted
$setdiff(X, Y)$. It will be convenient to use the notation $turinginterval(X, Y) = { Z bar.v X leqt Z leqt Y }$.

We will make frequent use of Lachlan's hat-trick. Given an enumeration ${C_s}_(s gt.eq 0}$ of an r.e. set $C$ define for each stage
$s gt.eq 0$
$
c_s = cases(
    min(setdiff(C_s, C_(s-1))) #h(1em) & "if" setdiff(C_s, C_(s-1)) eq.not emptyset,
    max(C_s union {s})         & "otherwise,"
)
$
where we take $C_(-1) = emptyset$. We say that the stage $s$ is $C$-_true_ if $restr(C_s, c_s) = restr(C, c_s)$. Now for the
$C$-recursive function $Phi(C)$ we define
$
hat(Phi)_s(C; x) = cases(
    Phi_s(C_s; x) #h(1em) & "if this computation converges and" phi(x, s) < c_s,
    "undefined"           & "otherwise,"
)
$
and
$
hat(phi)(x,s) = cases(
    phi(x, s) #h(1em) & "if" hat(Phi)(C_s; x) arrow.b,
    0                 & "otherwise."
)
$
The point of all this is the following. If $Phi(C; x) arrow.b$, then confinitely often $hat(Phi)_s(C; x) arrow.b$, and for every
$C$-true stage $s$, $hat(Phi)_s(C_s; x) arrow.r.double hat(Phi)(C; x) arrow.b$. The hattrick serves to weed out at $C$-true stages
all but the correct computations.

Finte sequences are denoted variously with parentheses, $(x_0, dots, x_(n-1))$ and angle brackets $angle.l x_0, dots, x_(n-1)
angle.r$. The length of the sequence $alpha$ is denonted $|alpha|$. The empty sequence, $angle.l angle.r$, is written as $nothing$.
The concatenation of the finite sequences $sigma$ and $gamma$ is written as $concat(sigma, gamma)$. For $e lt.eq |alpha|$,
$restr(alpha, e)$ is the initial segment of $alpha$ of length $e$.

We will commonly be constructing a set, $X$, to be recursively enumerable relative to a given set, C ("$X$ is $reIn(C)$".) The most
convenient way to do this is as follows. We actually construct an r.e. set, $U$, of _axioms_. Each axiom is (a code for) an ordered
triple $(D, x, e)$ where $D$ is a finite set and $x$ and $e$ are both natural numbers. Then the set
$
X = U^C = { x bar.v (exists e)[ (restr(C, e), x, e) in U] }
$
is $reIn(C)$. The axiom $(restr(C, e), x, e)$ _witnesses_ the fact that $x in U^C$, and $e$ is the _use_ of the enumeration. All
$reIn(C)$ sets are realizable in this way (up to degree).

Note that, once it is defined, $U$ does not depend essentially in any way on $C$. Thus we may consider, for _any_ set $Y$, the
$reIn(Y)$ set $U^Y$. $U$ then becomes a _pseudojump operator_, $U : Y arrow.r.bar Y plus.circle U^Y$. These operators will appear in
(TBD).

A set $Y$ is _recursively enumerable in, and above_ $X$ ("Y is $reInAbove(X)$") if $Y$ is $reIn(x)$ and $X leqt Y$.
If, instead, $Y$ is the difference of two $reIn(x)$ sets, and $X leqt Y$ then Y is said to be $dreInAbove(X)$.

#bibliography("works.yml")
