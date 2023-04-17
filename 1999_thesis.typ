//
#let thesis_title = "Properties of relative recursive enumerability"
#let author = "Rory Molinari"

////////////////////////////////////////
// Theorem envinroment
// https://github.com/sahasatvik/typst-theorems
#import "theorems.typ": *

#let theorem = thmbox(
    "theorem",
    "Theorem",
    base_level: 1,
    titlefmt: strong,
    bodyfmt: emph
)

    // Set difference
#let setdiff(a, b) = $#a tilde.op #b$
// Turing interval
#let turinginterval(a, b) = $[#a, #b]_T$
// Turing less than or equal
// Need the provide the argument. Othewise $leqt Z$ ends up roughly as $leqt$ $Z$, with too much space
#let leqt(z) = $lt.eq_T #z$
#let emptyset = $nothing$

// Calculation converges
#let converge = $#h(0em) arrow.b #h(0.05em)$

// Restriction of a to b
#let restr(a, b) = $#a harpoon.tr #b$
// Concatenation of sequences a and b
#let concat(a, b) = $#a paren.t #b$

// r.e.[Z]
#let reIn(z) = $"r.e."[#z]$
// REA[Z]
#let reInAbove(z) = $"REA"[#z]$
// dREA[Z]
#let dreInAbove(z) = $"d"reInAbove(#z)$

// Convenience symbols
#let phi = sym.phi.alt
#let join = sym.plus.circle
#let neq = sym.eq.not // not equal
#let geq = sym.gt.eq  // greater than or equal

////////////////////////////////////////
// Placeholder for things that aren't supported yet or that I don't know how to do

#let footnote(body) = {
    box(
        fill: rgb(220, 220, 220),
        [(#emph(body))]
    )
}

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

    #grid(
        columns: (0.5in, 2in),
        sym.copyright,
        align(horizon + left)[
          #underline[Rory Molinari] #h(1em) 1999 \
          All Rights Reserved
       ]
    )
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
#set heading(numbering: "1.")
#show heading.where(level: 1): it => {
    set heading(numbering: "I")
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
$setdiff(X, Y)$. It will be convenient to use the notation $turinginterval(X, Y) = { Z bar.v X leqt(Z) leqt(Y) }$.

We will make frequent use of Lachlan's hat-trick. Given an enumeration ${C_s}_(s geq 0)$ of an r.e. set $C$ define for each stage
$s geq 0$
$
c_s = cases(
    min(setdiff(C_s, C_(s-1))) quad &"if" setdiff(C_s, C_(s-1)) neq emptyset\,,
    max(C_s union {s})              &"otherwise,"
)
$
where we take $C_(-1) = emptyset$. We say that the stage $s$ is $C$-_true_ if $restr(C_s, c_s) = restr(C, c_s)$. Now for the
$C$-recursive function $Phi(C)$ we define
$
hat(Phi)_s(C; x) = cases(
    Phi_s(C_s; x) quad & "if this computation converges and" phi(x, s) < c_s\,,
    "undefined"        & "otherwise,"
)
$
and
$
hat(phi)(x,s) = cases(
    phi(x, s) quad & "if" hat(Phi)(C_s; x) converge\,,
    0              & "otherwise."
)
$
The point of all this is the following. If $Phi\(C; x) converge$, then confinitely often $hat(Phi)_s(C; x) converge$, and for every
$C$-true stage $s$, $hat(Phi)_s(C_s; x) arrow.r.double hat(Phi)(C; x) converge$. The hattrick serves to weed out at $C$-true stages
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
$reIn(Y)$ set $U^Y$. $U$ then becomes a _pseudojump operator_, $U : Y arrow.r.bar Y join U^Y$. These operators will appear in
(TBD).

A set $Y$ is _recursively enumerable in, and above_ $X$ ("Y is $reInAbove(X)$") if $Y$ is $reIn(x)$ and $X leqt(Y)$.
If, instead, $Y$ is the difference of two $reIn(x)$ sets, and $X leqt(Y)$ then Y is said to be $dreInAbove(X)$.

= A patched proof of the weak density of the properly d.r.e. degrees
== Introduction

In @CLW1989 a proof is given of the weak density of the properly d.r.e. degrees:
#theorem[
Given recursively enumerable sets $C <_T G$ there is a d.r.e. set $D$ not of r.e. degree such that $C <_T D <_T G$.
<thm2.1>
]

The proof given in @CLW1989 has two technical but important flaws. The first, involving the timing of injuries caused by different
strategies competing on the priorty tree, was noted and fixed by LaForte in @LaForte. The second, involving the claim that the
various functionals defined in the construction (specifically, the $Delta(C)$ functionals) are always defined consistently, was
noted by the present author and is discussed here. We assume the reader has access to a copy of @CLW1989.

When discussing the construction in @CLW1989 during the remainder of this section we will use notation matching the rest of this
thesis.  This notation varies slightly from that used in @CLW1989. We do, however, refer to the cycle-state numbers as defined in
@CLW1989, rather than their equivalents (if any) in this paper.

=== The central claim

The argument in @CLW1989 constructs a d.r.e. set $A$ satisfying each of the requirements
$
  R_e: quad A neq Theta_e(E_e) or E_e neq Phi_e(C join A)
$
where $E_e$ is an r.e. set, and $Theta_e$ and $Phi_e$ are partial recursive functionals.

The basic module presented to satisfy $E_e$ consists of an infinite collection of _cycles_, indexed by $omega^2$. Together, these
cycles attempt to define fuctionals $Delta(C)$ and $Gamma_j(C)$ (for $j in omega$) such that, if the strategy fails to satisfy
$R_e$, one of these functionals demonstrates $G leqt(C)$, contrary to assumption. Cycle $(j, k)$ is allowed to define the values
$Delta(C\; j)$ and $Gamma_j(C; k)$.

After the description of the basic module (@CLW1989[p141]) two claims are made:

+ "Whenever cycle $(j,k)$ is started, any previous version of it has been cancelled and its functionals have become undefined
  through $C$-changes."
+ Because of 1, "$Gamma_j$ and $Delta$ are defined consistently."

We will demonstrate that both of these claims are false. In the case of claim 2 this means that, even if claim 1 were true,
this still wouldn't be enough to show that the functional $Delta$ is defined consistently.

=== Counterexamples

Consider the case in which $C = emptyset$, so that no $C$-change ever occurs, and once we define a value for a functional
we are stuck with it. Write $Delta(j)$ for $Delta(emptyset \;  j)$.

We first show that 1 does not hold.

Consider the situation in which, at stage $t$, cycle $(j,k)$ is in state (5), cycle $(j, k+1)$ is in state (10) and cycle $(j+1,0)$
is in state (7). Now suppose that there are stages $t < s < s' < s''$, which are the next three stages and which any of the cycles
of the strategy act, such that those actions are:

- Stage $s$:   #h(1em) Cycle $(j+1, 0)$ defines $Delta(j+1)$ with use $v$.
- Stage $s'$:  #h(1em) Cycle $(j, k)$ sees the $G$-permission it has been waiting for and stops cycles $(j, k+1)$ and $(j+1, 0)$.
  At this point, cycle $(j,k)$ advances to state (7).
- Stage $s''$: #h(1em) Cycle $(j,k)$ sees the stage (which it calls $s_2$) it has been waiting for, and so (re)starts cycle $(j+1, 0)$.
The value for $Delta(j+1)$ that cycle $(j+1, 0)$ defined at stage $s$ has not become undefined, and claim 1 is false.

#v(1em)

Now suppose that somehow we patch the algorithm so that claim 1 holds, without changing any of the other essential features of the
construction. We show that it still may be that the functional $Delta$ is not defined consistently. Now the problem is that, for
a given value $j$, any of the cycles $(j, k)$ (for $k in omega$) may define $Delta(j)$, and it is these definitions which clash.

So consider the situation in which, at stage $t$, cycle $(j, k)$ is in state (5) and cycle $(j, k+1)$ is in state (7). Suppose
also that there are stages $t < s < s' < s''$, which are the next three stages at which any of the cycles of the strategy act,
such that these actions are:

- Stage $s$:   #h(1em) Cycle $(j, k+1)$ sees the stage (called $s_2$) it is waiting for, and so defines $Delta(j)$ with use $v'$,
  advancing to state (10).
- Stage $s'$:  #h(1em) Cycle $(j, k)$ gets the $G$-permission it has been waiting for and advances to state (7), stopping cycle
  $(j, k+1)$.
- Stage $s''$: #h(1em) Cycle $(j, k)$ sees _its_ version of stage $s_2$ (this is what it waits for in state (7)), and so attempts
  to define its own value of $Delta(j)$.

We further suppose that $G_s(j) neq G_(s'')(j)$ (this assumption is independent of any of the activity at stages $s$, $s'$ and
$s''$). Then the values of $Delta(j)$ that cycles $(j,k)$ and $(j, k+1)$ define will differ, but will both be present at stage
$s''$.

When boiled down, the problem is the tension between the definitions of the functions $Delta(C)$ and $Gamma_j(C)$.  The apparent
need to keep the definition of $Gamma_j(C)$ synchronozed with enumerations into the set $G$ conflicts with the more subdued approach
needed to keep $Delta(C)$ consistent. The inconsistency sneaks in when we "back the wrong horse," in committing to the wrong
$G$-change, rather than waiting for the one associated with a $Delta(C \; j)$-definition to pan out.

Now, we have no way of knowing ahead of time which horse to back: there are no Pharlaps #footnote[Gratuitous Australian reference]
here. If we hold back and hope that the $Delta$ route pans out we may be left dealing with the fact that we have ignored a (now)
vital $G$-change. If we jump at the $G$-change though (as in @CLW1989) we are left with the possibility of the inconsistency of
$Delta(C)$.

The author tried, and failed, for some time to reconcile these conflicting demands. I think my adviser, Peter Hinman, for suggesting
the correct compromise: we back both horses, hedging our bets until we have a better idea which is likely to be the right one.

This chapter, then, gives a correct proof of #thmref(<thm2.1>)[Theorem], slightly strengthening it to obtain the following result:
#theorem[
Given r.e. sets $C <_T G$ there are d.r.e. sets $D <_T E$ such that $turinginterval(D, F) subset turinginterval(C, G)$
and there is no r.e. set $E in turinginterval(D, F)$.
<thm2.2>
]

== The construction

We will construct d.r.e. sets $A$ and $B$ such that $D = C join A$ and $F = C join A join B$ satisfy the theorem.
To do this we satisfy all requirements of the form
$
  R_e: quad A neq Phi_e(E_e) or thin E_e neq Psi_e(C join A join B)
$
and
$
  P_e: quad B neq Theta_e(C join A)
$
where ${angle.l E_e, Phi_e, Psi_e angle.r}_(e geq 0)$ enumerates all triples in which $E_e$ is an r.e. set and
$Phi_e$ and $Psi_e$ are recursive functionals. ${Theta_e}_(e geq 0)$ merely enumerates the recursive functionals.


#bibliography("works.yml")
