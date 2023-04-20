//
#let thesis_title = "Properties of relative recursive enumerability"
#let author = "Rory Molinari"

////////////////////////////////////////
// Theorem envinroment
// https://github.com/sahasatvik/typst-theorems
#import "theorems.typ": *

#let myresult = thmbox.with(
    base_level: 1,
    titlefmt: strong,
    inset: 0em,
    padding: (top: 0.5em),
    separator: [#h(0.5em)] // using my change to theorems.typ - pull requested
)

#let theorem = myresult("theorem", "Theorem", bodyfmt: emph)
#let lemma = myresult("theorem", "Lemma")

#let proof = thmplain(
    none,
    "Proof",
    titlefmt: strong,
    bodyfmt: body => [
        #body #h(1fr) $square$
    ],
    padding: (top: 0em, bottom: 0em),
    inset: 0em,
    separator: [:#h(1em)]
).with(numbering: none)


// Set difference
#let setdiff(a, b) = $#a tilde.op #b$
// Turing interval
#let turinginterval(a, b) = $[#a, #b]_T$
// Turing less than and leq. Note that we have extra space after this symbol. See https://github.com/typst/typst/issues/877. The
// workaround is to specify 0 space ourselves.
#let ltt = $<_T #h(0em)$
#let leqt = $lt.eq_T #h(0em)$
#let emptyset = $nothing$

// Calculation converges
#let converge = $#h(0em) arrow.b #h(0.05em)$

// Restriction of a to b
#let restr(a, b) = $#a harpoon.tr #b$
// Concatenation of sequences a and b
#let concat(a, b) = $#a paren.t #b$
#let concatone(a, b) = $concat(#a, #angletup(b))$

// r.e.[Z]
#let reIn(z) = $"r.e."[#z]$
// REA[Z]
#let reInAbove(z) = $"REA"[#z]$
// dREA[Z]
#let dreInAbove(z) = $"d"reInAbove(#z)$

// Tuple with angle brackets
#let angletup(..z) = $angle.l #z.pos().join(", ") angle.r$

// Restriction of a to b
#let restr(a, b) = $#a harpoon.tr #b$
// Concatenation of sequences a and b
#let concat(a, b) = $#a paren.t #b$
#let concatone(a, b) = $concat(#a, #angletup(b))$
// "Finite sequences of"
#let finseq(a) = $#a^(< infinity)$

// Row j of an omega^2 set of cycles
#let row(j) = $cal(R)_#j$
// A cycle pattern. Note awkward negative space to get good placement of the subscript
#let pattern(s) = $cal(P)#h(-0.2em)_s$

// A "term" from the pattern definitions
#let patternname(n) = $sans(#n)$

// The "equality" property
#let Eq(x, y) = $sans("Eq")(#x, #y)$

// Convenience symbols
#let phi = sym.phi.alt
#let join = sym.plus.circle
#let neq = sym.eq.not // not equal
#let geq = sym.gt.eq  // greater than or equal
#let st = sym.bar.v   // vertical bar: "such that"
#let dubpr = sym.prime.double // double primes
#let trippr = sym.prime.triple // triple!

////////////////////////////////////////
// Placeholder for things that aren't supported yet or that I don't know how to do

#let footnote(body) = {
    box(
        fill: rgb(220, 220, 220),
        [(#emph(body))]
    )
}

////////////////////////////////////////
// Global formatting
#set par(justify: true)


// Based on an answer in the Discord from PgSuper (2023-04-13 1:43 PM)
// See issue #9 on GitHub
#let setupenum(doc, prefix: "", formats: ("1.", "(a)", "i.")) = {
  set enum(
    full: true,
    numbering: (..n) => {
      let n = n.pos()
      if n.len() > 2 {
        numbering(formats.at(2), n.last())
      } else if n.len() == 2 {
        numbering(formats.at(1), n.last())
      } else {
        numbering(prefix + formats.at(0), ..n)
      }
    }
  )
  doc
}

#show: doc => setupenum(doc)

////////////////////////////////////////
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
$setdiff(X, Y)$. It will be convenient to use the notation $turinginterval(X, Y) = { Z st X leqt Z leqt Y }$.

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
X = U^C = { x st (exists e)[ (restr(C, e), x, e) in U] }
$
is $reIn(C)$. The axiom $(restr(C, e), x, e)$ _witnesses_ the fact that $x in U^C$, and $e$ is the _use_ of the enumeration. All
$reIn(C)$ sets are realizable in this way (up to degree).

Note that, once it is defined, $U$ does not depend essentially in any way on $C$. Thus we may consider, for _any_ set $Y$, the
$reIn(Y)$ set $U^Y$. $U$ then becomes a _pseudojump operator_, $U : Y arrow.r.bar Y join U^Y$. These operators will appear in
(TBD).

A set $Y$ is _recursively enumerable in, and above_ $X$ ("Y is $reInAbove(X)$") if $Y$ is $reIn(x)$ and $X leqt Y$.
If, instead, $Y$ is the difference of two $reIn(x)$ sets, and $X leqt Y$ then Y is said to be $dreInAbove(X)$.

= A patched proof of the weak density of the properly d.r.e. degrees
== Introduction

In @CLW1989 a proof is given of the weak density of the properly d.r.e. degrees:
#theorem[
Given recursively enumerable sets $C ltt G$ there is a d.r.e. set $D$ not of r.e. degree such that $C ltt D ltt G$.
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
$R_e$, one of these functionals demonstrates $G leqt C$, contrary to assumption. Cycle $(j, k)$ is allowed to define the values
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
is in state (7). Now suppose that there are stages $t < s < s' < s dubpr$, which are the next three stages and which any of the
cycles of the strategy act, such that those actions are:

- Stage $s$:   #h(1em) Cycle $(j+1, 0)$ defines $Delta(j+1)$ with use $v$.
- Stage $s'$:  #h(1em) Cycle $(j, k)$ sees the $G$-permission it has been waiting for and stops cycles $(j, k+1)$ and $(j+1, 0)$.
  At this point, cycle $(j,k)$ advances to state (7).
- Stage $s dubpr$: #h(1em) Cycle $(j,k)$ sees the stage (which it calls $s_2$) it has been waiting for, and so (re)starts cycle $(j+1, 0)$.
The value for $Delta(j+1)$ that cycle $(j+1, 0)$ defined at stage $s$ has not become undefined, and claim 1 is false.

#v(1em)

Now suppose that somehow we patch the algorithm so that claim 1 holds, without changing any of the other essential features of the
construction. We show that it still may be that the functional $Delta$ is not defined consistently. Now the problem is that, for
a given value $j$, any of the cycles $(j, k)$ (for $k in omega$) may define $Delta(j)$, and it is these definitions which clash.

So consider the situation in which, at stage $t$, cycle $(j, k)$ is in state (5) and cycle $(j, k+1)$ is in state (7). Suppose
also that there are stages $t < s < s' < s dubpr$, which are the next three stages at which any of the cycles of the strategy act,
such that these actions are:

- Stage $s$:   #h(1em) Cycle $(j, k+1)$ sees the stage (called $s_2$) it is waiting for, and so defines $Delta(j)$ with use $v'$,
  advancing to state (10).
- Stage $s'$:  #h(1em) Cycle $(j, k)$ gets the $G$-permission it has been waiting for and advances to state (7), stopping cycle
  $(j, k+1)$.
- Stage $s dubpr$: #h(1em) Cycle $(j, k)$ sees _its_ version of stage $s_2$ (this is what it waits for in state (7)), and so attempts
  to define its own value of $Delta(j)$.

We further suppose that $G_s(j) neq G_(s dubpr)(j)$ (this assumption is independent of any of the activity at stages $s$, $s'$ and
$s dubpr$). Then the values of $Delta(j)$ that cycles $(j,k)$ and $(j, k+1)$ define will differ, but will both be present at stage
$s dubpr$.

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
Given r.e. sets $C ltt G$ there are d.r.e. sets $D ltt E$ such that $turinginterval(D, F) subset turinginterval(C, G)$
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
We will ensure that $A leqt G$ and $B leqt G$ by delayed, direct permitting.

The first thing we do is to give basic modules for each of the two types of requirement.  It is useful to note here
that elements are enumerated into or out of $A$ only in satisfying $R_e$ requirements, and $B$ receives elements
only in satisfying $P_e$ requirements. We also note that $B$ turns out to be r.e., and not just d.r.e., as we
never need to remove elements from $B$ once they are enumerated in.

=== The basic module for $R_e$

The basic module is very nearly the same as the one given in @CLW1989. (It appears to be somewhat differend here,
as we use slightly different notation, and a reduction in the number of states.) There is an extra state
necessary to avoid $Delta$-inconsistency.

Suppose $e$ is fixed and write $angletup(E, Phi, Psi)$ for $angletup(E_e, Phi_e, Psi_e)$. We will describe the strategy for
satisfying $R_e$. It consists of a $(omega^2)$-sequence of cycles ordered lexicographically. Cycle $(0,0)$ starts first, and each
cycle $(j,k)$ may start cycles $(j, k+1)$ and $(j+1, 0)$, as well as stopping all cycles $> (j,k)$.  The strategy as a whole
threatens to demonstrate that, if no cycle satisfies the requirement, then $G leqt C$ _via_ one of the functionals $Gamma_j(C)$
(for $j in omega$) or $Delta(C)$.  The cycle $(j, k)$ may define the values $Gamma_j(C\; k)$ and $Delta(C\; k)$. We refer to the
collection $row(j) = { (j, k) st k in omega }$ as the _$j$-th row of cycles_.

All cycles begin in state 0. A cycle is _started_ by letting it pass from state 0 to another state, as determined by its history. In
starting, a given cycle $(j, k)$ may in fact start subsequent cycles at the same stage, depending on whether cycle $(j, k)$ has been
abandoned in the past. This may start a "cascade" of cycle-startings. See state 0, below. A cycle is _reset_ by putting it back into
state 0, returing its restraints to 0 and undefining the values of its parameters $u$ and $v$.
//
(Note that the paper @CLW1989 uses
"_cancelled_" for this operation. We reserve this word for another purpose: see the description of the priority tree construction in
@sec233 below.)
//
A cycle is _abandoned_ by returing its restraints to 0 and stopping all activity for that cycle. This is done when a cycle has
categorically failed to satisfy $R_e$, due to the squandering of the various $G$-changes to which it has access. We gain through
this failure the correct definition of a value for one of the functionals $Gamma_j(C)$ or $Delta(C)$. A cycle is said to _act_
whenever it moves from one state to another. An exception to this is the transition from state 2 to state 3: this transition is made
purely for bookkeeping purposes.

Also, when (say) cycle $(j, k)$ acts and in doing so resets cycles to its right, we enirely discard any functionals $Gamma_l(C)$
for $l > j$, starting them completely afresh if ever needed.

Cycle $(j,k)$ of the strategy proceeds as follows.

0. Until given the go-ahead, do nothing. When told to start, if $k = 0$ we check if row $row(j)$ has been previously abandoned
  _en masse_. If so, advance directly to state 8 and follow the instructions at that state. Otherwise check if cycle $(j, k)$
  itself has been abandoned. If so, there is no point in trying to satisfy $R_e$ with this cycle, so jump straight to state 7
  and follow the instructions at that state. Otherwise, choose a new witness $x$ larger than any number used so far in the
  construction (including all currently imposed $A$-restraints, and the current stage) and larger than both $j$ and $k$.
  Advance to state 1.

+ Wait for a stage $s_1$ at which the following statement, which we call $Eq(x, s_1)$, holds:
  $
    ( A(x) = Phi(E \; x) )[s_1] and (restr(E, phi(x)) = ( restr(hat(Psi)(C join A join B), phi(x)) )[s_1]
  $
  [Note that if $s_1$ doesn't exist, we automatically satisify the requirement.]

  If $G_(s_1)(k) = 1$ we jump straight to state 7 and follow the instructions there.

  Otherwise put $u = (hat(psi) phi(x))[s_1]$. Restrain $restr(A, u)$ and $restr(B, u)$, put $Gamma_j(C; k) = G_(s_1)(k) thin (= 0)$
  with use $gamma_j(k) = u$ and start cycle $(j, k+1)$ to run simultaneously. Advance to state 2.

+ Wait for a stage $t_1$ at which either
  + $restr(C_(t_1), u) neq restr(C_(s_1), u)$; or
  + $G_(t_1)(k) neq G_(s_1)(k)$.

  [Note that we do not wait for a stage $t_1$ at which $C_(t_1) neq C_(t_1 - 1)$, (or where there is similar change in $G$) but
   rather for a change from the situation at stage $s_1$. In either case, once we combine the various strategies using a priority
   tree (see @sec233 below) strategy $alpha$ is not "accessible" at every stage. There may be times at which a relevant $G$- or
   $C$-change occurs but $alpha$ is not accessible, only to become accessible later. The reaction to the change, and hence
   permission, is "delayed" until the strategy is accessible.

   It is common in these situations to account for the "gaps" in the accessibility of $alpha$ by defining for each node $beta$
   in the priority tree an auxiliary enumeration for the r.e. set $C$:
   $
     C_s^beta = cases(
       C_s               &"if node" beta "is accessible at stage" s\, ,
       C_(s-1)^beta quad &"otherwise"
     )
   $
   where we take $C_(-1)^beta = emptyset$. Here we do _not_ use this construct. The part of the verification argument, below,
   which deals with the permission delays inherient with our set up (Lemma TBD) would only be complicated by the use of
   such variant enumerations.]

  Now, if
  + $restr(C, u)$ changes first, reset all cycles $> (j, k)$, drop the $A$- and $B$-restraint of cycle $(j, k)$ back to 0, and
    return to state 1. While if
  + $G(k)$ changes first, it it time to see if we need to hedge our bets. There are two subcases.
    + If some cycle $(j, k')$ of $row(j)$ is currently in stage 5 or 6 (there is at most one, by Lemma TBD below) we cannot
      act on the $G(k)$ change yet. We set the marker $mu(x) = v_(s_1)(j, k')$, defined below, (with the intention of allowing
      $x$ to enter $A$ later with a a $restr(C, mu(x))$ change) and advance to state 3. Recall that this transition does
      _not_ count as an action.
    + If no such $(j, k')$ exists we reset all cycles $> (j, k)$, enumerate $x$ into $A$ and advance to state 4.

+ Wait for a stage $t_2$ such that $restr(C_(t_2), mu(x)) neq restr(C_(t_1), mu(x))$.
  (The idea here is that the change in $restr(C, mu(x))$ has undefined the computation of $Delta(j)$ previously set by
   cycle $(j, k')$, allowing it be redefined in the future. This is how we avoid the $Delta$-inconsistency of the
   original paper, @CLW1989.)
  Reset all cycles $> (j, k)$, enumerate $x$ into $A$ and advance to state 4.

+ Wait for a stage $s_2$ such that $Eq(x, s_2)$. [As before, if $s_2$ doesn't exist we automatically satisfy the requirement.]

  If $G_(s_2)(j) = 1$ we jump straight to state 8 and follow the instructions there.

  Otherwise, we note that since
  $
    (Phi(E\; x))[s_2] = A_(s_2)(x) neq A_(s_1)(x) = (Phi(E\; x))[s_1]
  $
  we must have $restr(E_(s_2), phi_(s_1)(x)) neq restr(E_(s_1), phi_(s_1)(x))$, and since $E$ is r.e. this change is permanent
  and hence a target. Put $v = (hat(psi) phi(x))[s_2]$, restrain $restr(A, v)$ and $restr(B, v)$, put
  $Delta(C\; j) = G_(s_2)(j) thick (= 0)$ with use $delta(j) = v$ and start cycle $(j+1, 0)$ to run simultaneously.
  Advance to state 5.

+ Wait for a stage $t_3$ at which either
  + $restr(C_(t_3), v) neq restr(C_(s_2), v)$; or
  + $G_(t_3)(j) neq G_(s_2)(j)$.

  On reaching stage $t_3$ reset all cycles $> (j, k)$. Then
  + If $restr(C, v)$ changes first, return the $A$- and $B$-restraints to $u$, and return to state 4.
  + Otherwise, remove $x$ from $A$ and advance to state 6.  Note that now $restr(A_(t_3 + 1), u) = restr(A_(s_1), u)$.

+ Wait for $restr(C_(t_4), u) neq restr(C_(s_1), u)$. If this ever occurs, advance to state 7.

  If $restr(C, u) = restr(C_(s_1), u)$ we satisfy the requirement by
  $
    restr(hat(Psi)(C join A join B), phi_(s_1)(x))
               &= (restr(hat(Psi)(C join A join B), phi(x)))[s_1] \
               &= (restr(E, phi(x)))[s_1] \
               &= restr(E, phi_(s_1)(x))
  $

+ We only reach this state if it is safe (in terms of the consistency of $Gamma_j(C)$) and accurate
  to set $Gamma_j(C; k) = 1$ with use 0. Do so, unless it has already been done, (permanently) abandon cycle (j, k)
  and start cycle $(j, k+1)$.

  Once we reach this state, we define a value for $Gamma_j(C; k)$ which we _know_ to be correct, since $G(k)$ has already changed,
  and won't change again, $G$ being r.e.  Also, the "once-off" nature of the $G$-change means that the only way cycle $(j,k)$ is
  going to be able to satisfy requirement $R_e$ in the future, even with a new witness, is by being infinitely often in state 1; it
  cannot enumerate its witness into $A$, as the $G$-change it needs has already come and gone.  Although it is posisble that $(j,
  k)$ will be able to succeed in this manner, it is improbable. More likely is that cycle $(j, k)$ will be eventually stuck in state
  2, waiting forlornly for an impossible $G$-change, but in the meantime computing a correct value for $Gamma_j(C; k)$. We may as
  well cut our losses and simplify by abandoning this cycle: we content ourselves with the modest gain of a single correct value for
  $Gamma_j(C; k)$ and the knowledge that if we end up permanently abandoning _all_ cycles like this, we'll be able to compute $G$
  from $C$ (see Lemma TBD below), a contradiction.

+ We only reach _this_ state if it is similarly safe to set $Delta(C\; j) = 1$ with use 0. Do so, unless it has already been done.
  We permanently abandon the whole of row $row(j)$, and since there is no need to keep any of this row in business, it is convenient
  for technical reasons to reset every cycle in row $row(j)$, put cycle $(j, 0)$ into stage 8, and start cycle $(j+1, 0)$.

  The same comments as in state 7 just above apply here, but the result of the failure of cycle $(j, k)$ is even more stark. Now we
  have defined a correct value for $Delta(C, j)$, and have seen (and "wasted") the only change in $G(j)$ that will ever occur. Thus
  all cycles which rely on a change in $G(j)$ at some point are our of luck in the future, and we may as well not bother with
  them. These cycles include _all_ of row $row(j)$, which is why we permanently abandon this whole row. We content ourselves now
  with the single correct value $Delta(C\; j)$.

=== The basic module for $P_e$

The $P_e$ requriements are simpler than those of the first kind, and we implement a standard diagonalisation approach to satisfy
them. To ensure that $B leqt G$ we again use a system of cycles, but now we only have a one-dimensional arrangement.

Again, suppose $e$ is fixed, and write $Theta$ for $Theta_e$. We have a $omega$-sequence of cycles, and again threaten
to show $G leqt C$, by means of a functional $Xi(C)$. _Starting_ and _abandoning_ have the same definitions as before. _Resetting_
is similar, but now we need only worry about the single parameter, $u$. _Acting_ now happens with any change of state,
as we have no equivalent of the bookkeeping state 3 to worry about.

To distinguish the names of the states from those in the module for the $R_e$-requirements we will prefix the numbers here with
the letter P. Cycle $k$ proceeds as follows.

// TODO: this is hacky. We set up num for the rest of the document with a P prefix, and then undo that below. How can we restrict
// the scope?
#show: doc => setupenum(doc, prefix: "P")
0. Until given the go-ahead, do nothing. When told to start check if cycle $k$ has been abandoned in the past. If so, jump straight
  to state P4 and follow the instructions there. Otherwise, choose a new witness $y$ larger than any number mentioned in the
  construction so far (including all currently defined $B$-restraints, and the current stage) and larger than $k$. Advance to state
  P1.

+ Wait for a stage $s_1$ at which
  $
    (B(y) = hat(Theta)(C join A\; y))[s_1]
  $
  and let $u = hat(theta)_(s_1)(y)$. Restrain $restr(A, u)$, put $Xi(C\; k) = G_(s_1)(k)$ with use $xi(k) = u$ and start
  cycle $k+1$ to run simultaneously. Advance to state P2.

  [Note that if there is no such stage $s_1$ we immediately satisfy the requirement, by diagonalization.]

+ Wait for a stage $t_1$ at which either
  + $restr(C_(t_1), u) neq restr(C_(s_1), u)$; or
  + $G_(t_1)(k) neq G_(s_1)(k)$.

  On reaching $t_1$, reset all cycles $k' > k$. Then
  + If $restr(C, u)$ changes first, set the $B$-restraint of this cycle back to 0 and return to state P1.
  + Otherwise, enumerate $y$ into $B$. This has been permitted (perhaps after a delay) by the change in $G(k)$. Proceed to state P3.

+ Wait for a stage $s_2$ at which
  $ (B(y) = hat(Theta)(C join A\; y))[s_2] $
  If there is no such stage, $y$ again witnesses the success of our strategy.

  If such an $s_2$ exists, note that we have
  $
  (hat(Theta)(C join A\; y))[s_2] = B_(s_2)(y) = 1 neq 0 = B_(s_1) = (hat(Theta)(C join A\; y))[s_1].
  $
  By the restraint on $A$, $restr(A_(s_2), u) = restr(A_(s_1), u)$ so we must have $restr(C_(s_2), u) neq restr(C_(s_1), u)$.
  This change in $C$ allows us to redefine $Xi(C\; k)$, which we do after advancing to state P4.

+ It is now safe and correct to define $Xi(C\; k) = 1$ with use 0. Do so, unless this has already been done, permanently abandon
  cycle $k$, and start cycle $k+1$.

  [This is just like state 7 in the basic module for the $R_e$ requirements.]

// TODO: hacky (see above)
#show: doc => setupenum(doc)

=== Combining the modules <sec233>

Now that we have desribed the strategy for satisfying a single requirement in isolation we must consider how to satisfy all
requirements simultaneously. Since each strategy may well act infinitely often we must use a _priority tree_ to manage this. The
standard reference fo this technique is Chapter XIV of Soare @Soare1987.

#let outcome = $concatone(alpha, (j, k))$

In @LaForte LaForte introduced a path restraint to deal with a problem in the original construction in @CLW1989. Basically, that
construction worked the tree angle in an "obvious" way. As soon a strategy $alpha$'s cycle $(j, k)$ became "active" we use #outcome
as the outcome; this happens as soon as cycle $(j, k)$ chooses a witness. (For the moment the consider the case of
                                                                           $R_e$-strategies.) However, if cycle $(j, k)$ later sees a relevant computation converge and imposes a restraint $r$, those
strategies in the subtree below #outcome started in the meantime will not have chosen witnesses to respect this new restraint. This
is naturally a Bad Thing. LaForte ingeniously solves the problem by introducing the path restraint: as the new restraint is imposed
it is incorporated into the path restraint for strategies below #outcome and respected "after the fact."  Strategies below #outcome
constantly check the extent of the path restraint being imposed on them.

#let outcome = none

This method works fine, as seen in @LaForte. However, it not particulary pretty. In particular, the point of tree-based arguments is
to remove the need for strategies to themselves keep an eye on the restraints set by other strategies. If possible, we would like to
avoid the path restraint, and there is a simple trick that lets us do so. We only follow a child corresponding to cycle $(j,k)$ when
cycle $(j, k)$ has actually imposed a restraint. Until that happen we follow a child corresponding to the rightmost cycle to the
left of $(j, k)$ which imposes restraint. This is perfectly safe, as, so long as $(j, k)$ imposes no restraint, we cannot injure any
computions by letting the strategies below the leftward cycle operate. Once such a restraint is imposed, we automatically respect it
by starting to follow a child corresponding to $(j, k)$. The only trick we actually need is to add a new child,
$concatone(alpha, -1)$, to be followed when no cycles at all of strategy $alpha$ impose a restraint.

Each cycle can impose restraint in two "waves". By seeing $Eq(x, s_1)$ cycle $(j, k)$ restrains $restr(A, u)$ and $restr(B, u)$.
Later, on seeing $Eq(x, s_2)$, it further restrains $A$ and $B$ as far as $v$. Thus, corresponding to each cycle $(j, k)$ we will
have _two_ outcomes, $((j, k), 1)$ and $((j, k), 2)$, progressively used to respect these two waves of restraint. $P_e$-restraints
impose only one wave of restraint and so need only one outcome per cycle on the tree.

So, let $Lambda = {-1} union ((omega^2) times {1, 2}) union omega$. We partially order $Lambda$ lexicographically on
$(omega^2) times {1, 2}$, with the natural ordering on $omega$, and making -1 come before everything. We don't define any relative
order between elements of $(omega^2) times {1, 2}$ and $omega$, as this won't be necessary. Let
$
T = {f in Lambda^(< omega) st f(n) in {-1} union (omega^2) times {1, 2} "if" n "is even", f(n) in {-1} union omega "if" n "is odd" }
$

be the priority tree, with the started partial ordering $<_L$ inherited from the order imposed on $Lambda$ above. If $alpha in T$
has even length $|alpha| = 2e$ then $alpha$ aims to satisfy requirement $R_e$, while if $|alpha| = 2e + 1$ then $alpha$ works
towards satisfying $P_e$. Recall that we make no distinction between a node on the tree and the (instance of the) strategy it is
using. A strategy is _cancelled_ by resetting all of its cycles and discarding any functionals it may have (partially) defined. Any
paramater, once defined, keeps that value until it is redefined or undefined.

The construction proceeds as follows.

Stage 0: #h(1em) All parameters are undefined or $emptyset$ as appropriate, and all cycles are in state 0 or state P0.

#let nextval = $f_(s+1)(t)$
Stage $s+1$: #h(1em) We define, in substages $t < s$, a finite path $nextval$ through the tree, of length $s$. So, suppose $alpha =
(restr(nextval, t)) in T$ is defined. If no cycle of strategy $alpha$ has been started since $alpha$ was last cancelled, start
$alpha$'s cycle $(0, 0)$ or $0$, as appropriate, and put $nextval(t) = -1$.

Otherwise, first suppose that $|alpha|$ is even, so that $alpha$ is using an $R_e$ strategy. Allow any cycles of strategy $alpha$
able to make the transition from state 2 to state 3 do so. Now there are 2 cases.
- #smallcaps("Case 1") #h(1em) Some least cycle $nu$ of strategy $alpha$ is able (or forced by a $C$-change) to act.

We allow cycle $nu$ to act. Let $lambda$ be the rightmost cycle of strategy $alpha$ now imposing restraint (if there is any such
                                                                                                            cycle.) It is not necessarily the case that $lambda = nu$. If cycle $lambda$ is now in state 2, 3, or 4 then put
$nextval = (lambda, 1)$. If instead, $lambda$ is in stage 5 or 6 then put $nextval = (lambda, 2)$. Cancel all strategies
$beta$ with $concatone(alpha, nextval) <_L beta$. If $lambda = nu$ and the action of cycle $nu$ involved enumerating a number into
or out of $A$ or into $B$ we also cancel all strategies $beta supset concatone(alpha, nextval)$.

If there is no such cycle $lambda$ then put $nextval = -1$ and cancel all strategies $beta$ with $concatone(alpha, -1) <_L beta$.

- #smallcaps("Case 2") #h(1em) No cycle of strategy $alpha$ is able, or forced, to act.

We do nothing, and nothing needs to be cancelled. Define $nextval$ just as above. No strategies need to be cancelled.

If $|alpha|$ is odd, then we behave similarly. Now, given the rightmost cycle, $lambda$, imposing restraint, we simply put
$nextval = lambda$, rather than worrying about two kinds of restraint.

If $t + 1 < s$ we advance to substage $t + 1$.

We say tha the strategies $alpha subset f_(s+1)$ are _accessible_ at stage $s+1$.

== Verification

The verification of the construction is a long and tedious one, and is broken up into a sequence of lemmas. As the arguments for the
two types of module are of necessity quite different, for the first part of the verification we discuss the modules separately.

We will refer to the parameters associated with cycle $nu$ of strategy $alpha$ as they are defined at stage $s$ like so:
$u_s(alpha, nu)$, $v_s(alpha, nu)$, _etc_. When the strategy is clear from context (as it usually will be), we will drop it.

=== Lemmas for the $R_e$ strategy

==== The layout of the cycle states

We begin with a sequence of lemmas which describes the different arrangements possible of the states of the various cycles at any time.
The aim is to formalize the intuitive ideas that develop from an understanding of the way the construction works.

We assume that we have a certain, fixed strategy, $alpha$, of even length in mind, and that all cycles mentioned belong to this
strategy. Also, we ignore the fact that strategy $alpha$ may not be accessible at all (or even all sufficiently large) stages: we
just treat the stages mentioned as being the successive ones at which strategy $alpha$ _is_ accessible.

It will be convenient to refer to a cycle with is in either stage 5 or state 6 as being "in state 5/6".

#lemma[
    For any row $row(j)$, at most one cycle $(j, k)$ is in state 5/6.
    <lemma23>
]
#proof[
    We show that if cycle $(j, k)$ is in state 5 or state 6 at stage $s$ then nothing to the right of $(j, k)$ in row $row(j)$
    (namely, a cycle $(j, k') > (j, k)$) is in either of these states at stage $s$.

    If cycle $(j, k)$ entered state 5 from state 4 (and there is no other way), no cycles to the right of $(j, k)$ are in any state
    other than 0 at the start of stage $s$, because by entereing state 4, cycle $(j, k)$ reset every cycle to its right, and no new
    cycles were started so long as $(j, k)$ remained in state 4. Upon entering state 5, cycle $(j, k)$ starts cycle $(j+1, 0)$,
    and no cycle to the right of $(j, k)$ in row $row(j)$ is started so long as $(j, k)$ stays in state 5.

    On entering state 6, cycle $(j, k)$ resets every cycle to its right (including those in rows $row(j')$ for $j' > j$), and no
    cycle to its right will be started so long as $(j, k)$ remains in this state.
]

#lemma[
    Suppose cycle $(j, k)$ enters state 3 at stage $s$ due to cycle $(j, k')$ being in state 5/6. If at stage $t > s$ cycle $(j, k')$
    leaves state 5/6 for the first time, for any reason, then cycle $(j, k)$ is no longer in state 3 at the end of stage $t$.
    <lemma24>
]
#proof[
    Note that $mu_s(x(j, k)) = v_s(j, k')$.

    Cycle $(j, k')$ leaves state 5/6 either through acting or through being reset. If $(j, k') < (j, k)$ then we see that the
    action/resetting of $(j, k')$ also resets $(j, k)$, and the latter is no longer in state 3. (It will turn out later that a cycle
    can't be in state 3 when something in the same row to its left is in state 5/6, but we can't rule out that possibility yet.)

    If $(j, k) < (j, k')$ we must work substantially harder.

    In this case, if $(j, k')$ is able to get out of state 5/6 without being reset, we must have a change in $restr(C, v_t(j, k'))$
    (if $(j, k')$ goes to state 4) or in $restr(C, u_t(j, k')) subset restr(C, v_t(j, k'))$
    (if it goes to state 7). This very change in $C$ allows $(j, k)$
    to move to state 4, unless another cycle to its left acts for this same reason, resetting cycle $(j, k)$ completely.

    If $(j, k')$ is reset at $t$ by the action of a cycle to the left of $(j, k)$, cycle $(j, k)$ is reset also.

    Thus, aiming for a contradiction, we need only consider the case in which for some $k dubpr$ with
    $k < k dubpr < k'$, cycle $(j, k dubpr)$ acts at stage $t$,
    but $restr(C, v_t(j, k'))$ does not change at stage $t$. (Note that $v_t(j, k') = v_s(j, k')$.)
    Without loss of generality we may assume that $t$ is minimal in witnessing the failure of this lemma.
    Since cycle $(j, k')$ is "awake" (that is, in a state other than 0) between stages $s$ and $t$, cycle $(j, k dubpr)$
    must be in one of the states 2, 3 or 7, and cannot change states (other than going from 2 to 3) during this time, for otherwise
    cycle $(j, k')$ would be reset. We may may immediately discount the possibility that $(j, k dubpr)$ in state 7,
    because a cycle in this state cannot act. Thus, as stage $t$ starts, cycle $(j, k dubpr)$ is in state 2 or state 3.

    We first claim that $(j, k dubpr)$ can't make the transition from state 2 to state 1. Indeed, such a transition indicates a change
    in $restr(C, u(j, k dubpr))$. But cycle $(j, k')$ starts after cycle $(j, k dubpr)$ enters state 2, so by construction,
    $v_t(j, k') > x(j, k') > u(j, k dubpr)$, and we have a change in $restr(C, v_t(j, k'))$ at stage $t$, which is a contradiction.

    Cycle $(j, k dubpr)$ can't go from state 2 to state 3 at stage $t$, as this does not count as an action, so the only remaining
    possibility is the $3 arrow.r.bar 4$ transition, so that there is a change in $restr(C, mu_t(x(j, k dubpr)))$.
    We claim that $mu_t(x(j, k dubpr)) = v_t(j, k')$, and obtain the contradiciton of a change in $restr(C, v_t(j, k'))$.

    Suppose otherwise, so that $(j, k dubpr)$ enters state 3 for the sake of yet another cycle $(j, k trippr)$ being
    in state 5/6, or for another "incarnation" of cycle $(j, k')$; that is, for the sake of cycle $(j, k')$ being in state 5/6
    based on another computation. Well, if we are in the former case, cycle $(j, k trippr)$ must leave state 5/6 by stage $s$,
    by #thmref(<lemma23>)[Lemma], forcing cycle $(j, k dubpr)$ out of state 3, by the assumption of the minimality of $t$.
    The same argument applies to another "incarnation" of cycle $(j, k')$. Thus, cycle $(j, k dubpr)$ enters state 3 for
    the sake of the same $(j, k')$-related computations that force cycle $(j, k)$ to do likewise, and
    $mu_t(x(j, k dubpr)) = mu_s(x(j, k')) = v_s(j, k') = v_t(j, k')$. We are done.
]
#lemma[
    For all $j$, if cycles $(j, k) neq (j, k')$ are both in state 3 at stage $s$, then
    $(mu(x(j, k)))[s] = (mu(x(j, k')))[s]$.
]
#proof[
    Suppose $(j, k)$ enters state 3 at stage $t$ and remains there until $(j, k')$ does the same at stage $t' > t$, and
    that they both stay in this state until at least stage $s$. By Lemmas #thmref(<lemma23>) and #thmref(<lemma24>),
    both cycles must enter state 3 for the sake of the same cycle being in stage 5/6, and for the same computations.
    The lemma follows.
]

We are now ready to describe the various patterns made by the successive
cycle-states.#footnote[Such as Athens, Sparta, Hamburg, #sym.dots . Oh, no, that's something else.]
To do this we first need to introduce some definitions and notation.

Consider a stage $s$, and the states that all the various cycles of strategy $alpha$ are in at the end of stage $s$.  We will call
this arrangement the _pattern of strategy $alpha$ at stage $s$_, and denote it by $pattern(s) = pattern(s)(alpha)$.  The notation
used to represent patterns is based on the row structure of the cycles. $pattern(s)$ will be given as a finite sequence, one term
each for those rows $row(j)$ of the strategy with at least one cycle in a state other than 0. Each term in this sequence will itself
be a finite sequence, one term each for the cycles of row $row(j)$ (say) in a state other than 0.

Let $X = {0, 1, 2, dots, 8}$. For sets $M, N$ of finite sequences (of unspecified type) we let
$M; N = {concat(theta, sigma) st theta in M and sigma in N}$,
the finite sequences got by appending a sequence from $N$ to a sequence from $M$. For convenience we also allow the notation
$angletup(M) = { angletup(theta) | theta in M }$, the length 1 sequences consisting of single terms from $M$. We define the
following subsets of $finseq(X)$:
#let prelimCramp = patternname("prelimCrampedRow")
#let finalCramp = patternname("finalCrampedRow")
#let crampedRow = patternname("crampedRow")
#let uncrampedRow = patternname("uncrampedRow")
#let abandonedrow = patternname("abandonedRow")
#let prelimRow = patternname("prelimRow")
#let finalRow = patternname("finalRow")
#let validPattern = patternname("validPattern")
$
  prelimCramp  &= finseq({2, 3, 7}); angletup({5}), \
  finalCramp   &= finseq({2, 3, 7}); angletup({6}), \
  crampedRow   &= prelimCramp union finalCramp, \
  uncrampedRow &= finseq({2, 7}); angletup({1, 4}), \
  abandonedrow &= angletup({8}), \
  prelimRow    &= prelimCramp union abandonedrow, \
  finalRow     &= finalCramp union uncrampedRow,
$
and a subset of $finseq((finseq(X)))$
$
  validPattern = finseq(prelimRow); angletup(finalRow).
$
The names are intended to be somewhat mnemonic. "Cramped" refers to a row in which cycles are prevented from reaching state 4 by the
presence of a cycle in that row in state 5/6. These cycles have their style cramped: they must bide their time in state 3 waiting
for the chance to go to state 4 later. A "#patternname("prelim")" row is one that isn't the last in the list: the row after it also
has at least one cycle not in state 0.

When we want to make it clear how long a finite sequence is, we subscript the sequence with its length, like so:
$angletup(0, 1, dots, 7)_8$.

The claim is now that if strategy $alpha$ has been started since last being cancelled, its pattern in "valid":
#lemma(name: "Pattern Lemma")[
    If strategy $alpha$ has at least one cycle not in state 0 at stage $s$, $pattern(s) in validPattern$.
    <patternLemma>
]
#bibliography("works.yml", style: "ieee")
