//
#let thesis_title = "Properties of relative recursive enumerability"
#let author = "Rory Molinari"

////////////////////////////////////////
// Theorem environment
// https://github.com/sahasatvik/typst-theorems
#import "theorems.typ": *

////////////////////////////////////////
// Tablex
// Extended table support
// https://github.com/PgBiel/typst-tablex
#import "tablex.typ": tablex, gridx, hlinex, colspanx

#let myresult = thmbox.with(
    base_level: 1,
    titlefmt: strong,
    bodyfmt: emph,
    inset: 0em,
    padding: (top: 0.0em),
    separator: [#h(0.5em)] // using my change to theorems.typ - pull requested
)

#let theorem = myresult("theorem", "Theorem")
#let lemma = myresult("theorem", "Lemma", bodyfmt: text)
#let proposition = myresult("theorem", "Proposition")
#let conjecture = myresult("theorem", "Natural Conjeccture")

#let qed = [#h(1fr) $square$]
#let proof = thmplain(
    none,
    "Proof",
    titlefmt: strong,
    bodyfmt: body => [
        #body #qed
    ],
    padding: (top: 0em, bottom: 0em),
    inset: 0em,
    separator: [:#h(1em)]
).with(numbering: none)

#let theoremRef(name) = thmref(name)[Theorem]
#let lemmaRef(name) = thmref(name)[Lemma]

#let chapRef(num) = ref(label("chapter" + str(num)), supplement: "Chapter")

// Set difference
#let setdiff(a, b) = $#a tilde.op #b$
// Turing interval
#let turinginterval(a, b) = $[#a, #b]_T$
// Turing less than and leq. Note that we have extra space after this symbol. See https://github.com/typst/typst/issues/877. The
// workaround is to specify 0 space ourselves.
#let ltt = $<_T$
#let leqt = $lt.eq_T$
#let emptyset = $nothing$
// "Zero jump"
#let zerojump = $emptyset'$

// Calculation converges
#let converge = $#h(0em) arrow.b #h(0.05em)$

// "State transition"
#let trans(a, b) = $#a arrow.r.bar #b$

// r.e.[Z]
#let reIn(z) = $"r.e."[#z]$
// REA[Z]
#let reInAbove(z) = $upright("REA")[#z]$
// dREA[Z]
#let dreInAbove(z) = $upright("d")reInAbove(#z)$

// Tuple with angle brackets
#let angletup(..z) = $lr(angle.l #z.pos().join([, ]) angle.r)$

// Restriction of a to b
#let restr(a, b) = $#a harpoon.tr #b$
// Concatenation of sequences a and b
#let concat(a, b) = $#a paren.t #b$
#let concatone(a, b) = $concat(#a, #angletup(b))$

#let setconcat(M, N) = $#M\; #N$

// "Finite sequences of"
#let finseq(a) = $#a^(< infinity)$

// Row j of an omega^2 set of cycles, and a more general "slice" of a higher-dimensional set
#let row(j) = $cal(R)_#j$
#let slice(..j) = $cal(S)_(#j.pos().join([,]))$
// A cycle pattern. Note awkward negative space to get good placement of the subscript
#let pattern(s) = $cal(P)#h(-0.2em)_#s$

// State/stage/strategy/row numbers/names, with nonbreaking space
#let state(num) = [state~#num]
#let nstate(num) = [state~N#num]
#let strat(s) = [strategy~#s]
#let stg(num) = [stage~#num]
#let theRow(j) = [row~$row(#j)$]
#let cycle(name) = [cycle~#name]

// The "equality" property
#let Eq(x, y) = $sans("Eq")(#x, #y)$

// Convenience symbols
#let phi = sym.phi.alt
#let epsilon = sym.epsilon.alt
#let join = sym.plus.circle
#let neq = sym.eq.not // not equal
#let leq = sym.lt.eq  // greater than or equal
#let geq = sym.gt.eq  // greater than or equal
#let st = sym.bar.v   // vertical bar: "such that"
#let dubpr = sym.prime.double // double primes
#let trippr = sym.prime.triple // triple!

////////////////////////////////////////
// The names of things in the Pattern Lemmas
#let patternName(n) = $sans(#n)$
#let prelimCrampedRow = patternName("prelimCrampedRow")
#let finalCrampedRow = patternName("finalCrampedRow")
#let crampedRow = patternName("crampedRow")
#let uncrampedRow = patternName("uncrampedRow")
#let abandonedRow = patternName("abandonedRow")
#let prelimRow = patternName("prelimRow")
#let finalRow = patternName("finalRow")
#let validPattern = patternName("validPattern")
#let validPatternForP = patternName("validPatternForP")

////////////////////////////////////////
// Small-scale layout things

#let stage-hdr(name) = [Stage #name: #h(1em)]
#let case(name) = [#smallcaps([Case #name]) #h(1em)]

#let squad = h(1em)

////////////////////////////////////////
// Placeholder for things that aren't supported yet or that I don't know how to do

#let footnote(body) = {
    set text(
        fill: blue,
        size: 0.8em
    )
    [ ^(#emph(body)) ]
}

////////////////////////////////////////
// Global formatting
#set par(justify: true)


// Based on an answer in the Discord from PgSuper (2023-04-13 1:43 PM)
// See issue #9 on my GitHub
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

#let defEnum(..fmts) = {
    show: doc => setupenum(doc, formats: fmts)
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
      #v(0.8in)
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
angle.r$. The length of the sequence $alpha$ is denonted $|alpha|$. The empty sequence, $angle.l angle.r$, is written as $emptyset$.
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
(Chapter VI TODO).

A set $Y$ is _recursively enumerable in, and above_ $X$ ("Y is $reInAbove(X)$") if $Y$ is $reIn(x)$ and $X leqt Y$.
If, instead, $Y$ is the difference of two $reIn(x)$ sets, and $X leqt Y$ then Y is said to be $dreInAbove(X)$.

= A patched proof of the weak density of the properly d.r.e. degrees <chapter2>

== Introduction

In @CLW1989 a proof is given of the weak density of the properly d.r.e. degrees:
#theorem[
Given recursively enumerable sets $C ltt G$ there is a d.r.e. set $D$ not of r.e. degree such that $C ltt D ltt G$.
<theorem2.1>
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

This chapter, then, gives a correct proof of #theoremRef(<theorem2.1>), slightly strengthening it to obtain the following result:
#theorem[
Given r.e. sets $C ltt G$ there are d.r.e. sets $D ltt E$ such that $turinginterval(D, F) subset turinginterval(C, G)$
and there is no r.e. set $E in turinginterval(D, F)$.
<theorem2.2>
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

=== The basic module for $R_e$ <basicModuleRe>

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
@section2.3.3 below.)
//
A cycle is _abandoned_ by returing its restraints to 0 and stopping all activity for that cycle. This is done when a cycle has
categorically failed to satisfy $R_e$, due to the squandering of the various $G$-changes to which it has access. We gain through
this failure the correct definition of a value for one of the functionals $Gamma_j(C)$ or $Delta(C)$. A cycle is said to _act_
whenever it moves from one state to another. An exception to this is the transition from state~2 to state~3: this transition is made
purely for bookkeeping purposes.

Also, when (say) cycle $(j, k)$ acts and in doing so resets cycles to its right, we enirely discard any functionals $Gamma_l(C)$
for $l > j$, starting them completely afresh if ever needed.

Cycle $(j,k)$ of the strategy proceeds as follows.

0. Until given the go-ahead, do nothing. When told to start, if $k = 0$ we check if row $row(j)$ has been previously abandoned
  _en masse_. If so, advance directly to state~8 and follow the instructions at that state. Otherwise check if cycle $(j, k)$
  itself has been abandoned. If so, there is no point in trying to satisfy $R_e$ with this cycle, so jump straight to state~7
  and follow the instructions at that state. Otherwise, choose a new witness $x$ larger than any number used so far in the
  construction (including all currently imposed $A$-restraints, and the current stage) and larger than both $j$ and $k$.
  Advance to state~1.

+ Wait for a stage $s_1$ at which the following statement, which we call $Eq(x, s_1)$, holds:
  $
    ( A(x) = Phi(E \; x) )[s_1] and (restr(E, phi(x)) = ( restr(hat(Psi)(C join A join B), phi(x)) )[s_1]
  $
  [Note that if $s_1$ doesn't exist, we automatically satisify the requirement.]

  If $G_(s_1)(k) = 1$ we jump straight to state~7 and follow the instructions there.

  Otherwise put $u = (hat(psi) phi(x))[s_1]$. Restrain $restr(A, u)$ and $restr(B, u)$, put $Gamma_j(C; k) = G_(s_1)(k) thin (= 0)$
  with use $gamma_j(k) = u$ and start cycle $(j, k+1)$ to run simultaneously. Advance to state~2.

+ Wait for a stage $t_1$ at which either
  + $restr(C_(t_1), u) neq restr(C_(s_1), u)$; or
  + $G_(t_1)(k) neq G_(s_1)(k)$.

  [Note that we do not wait for a stage $t_1$ at which $C_(t_1) neq C_(t_1 - 1)$, (or where there is similar change in $G$) but
   rather for a change from the situation at stage $s_1$. In either case, once we combine the various strategies using a priority
   tree (see @section2.3.3 below) strategy $alpha$ is not "accessible" at every stage. There may be times at which a relevant $G$- or
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
   which deals with the permission delays inherent with our set up (#lemmaRef(<lemma2.25>)) would only be complicated by the use of
   such variant enumerations.]

  Now, if
  + $restr(C, u)$ changes first, reset all cycles $> (j, k)$, drop the $A$- and $B$-restraint of cycle $(j, k)$ back to 0, and
    return to state~1. While if
  + $G(k)$ changes first, it it time to see if we need to hedge our bets. There are two subcases.
    + If some cycle $(j, k')$ of $row(j)$ is currently in stage 5 or 6 (there is at most one, by #lemmaRef(<lemma2.3>) below) we cannot
      act on the $G(k)$ change yet. We set the marker $mu(x) = v_(s_1)(j, k')$, defined below, (with the intention of allowing
      $x$ to enter $A$ later with a a $restr(C, mu(x))$ change) and advance to state~3. Recall that this transition does
      _not_ count as an action.
    + If no such $(j, k')$ exists we reset all cycles $> (j, k)$, enumerate $x$ into $A$ and advance to state~4.

+ Wait for a stage $t_2$ such that $restr(C_(t_2), mu(x)) neq restr(C_(t_1), mu(x))$.
  (The idea here is that the change in $restr(C, mu(x))$ has undefined the computation of $Delta(j)$ previously set by
   cycle $(j, k')$, allowing it be redefined in the future. This is how we avoid the $Delta$-inconsistency of the
   original paper, @CLW1989.)
  Reset all cycles $> (j, k)$, enumerate $x$ into $A$ and advance to state~4.

+ Wait for a stage $s_2$ such that $Eq(x, s_2)$. [As before, if $s_2$ doesn't exist we automatically satisfy the requirement.]

  If $G_(s_2)(j) = 1$ we jump straight to state~8 and follow the instructions there.

  Otherwise, we note that since
  $
    (Phi(E\; x))[s_2] = A_(s_2)(x) neq A_(s_1)(x) = (Phi(E\; x))[s_1]
  $
  we must have $restr(E_(s_2), phi_(s_1)(x)) neq restr(E_(s_1), phi_(s_1)(x))$, and since $E$ is r.e. this change is permanent
  and hence a target. Put $v = (hat(psi) phi(x))[s_2]$, restrain $restr(A, v)$ and $restr(B, v)$, put
  $Delta(C\; j) = G_(s_2)(j) thick (= 0)$ with use $delta(j) = v$ and start cycle $(j+1, 0)$ to run simultaneously.
  Advance to state~5.

+ Wait for a stage $t_3$ at which either
  + $restr(C_(t_3), v) neq restr(C_(s_2), v)$; or
  + $G_(t_3)(j) neq G_(s_2)(j)$.

  On reaching stage $t_3$ reset all cycles $> (j, k)$. Then
  + If $restr(C, v)$ changes first, return the $A$- and $B$-restraints to $u$, and return to state~4.
  + Otherwise, remove $x$ from $A$ and advance to state~6.  Note that now $restr(A_(t_3 + 1), u) = restr(A_(s_1), u)$.

+ Wait for $restr(C_(t_4), u) neq restr(C_(s_1), u)$. If this ever occurs, advance to state~7.

  If $restr(C, u) = restr(C_(s_1), u)$ we satisfy the requirement by
  $
    restr(hat(Psi)(C join A join B), phi_(s_1)(x))
               &= (restr(hat(Psi)(C join A join B), phi(x)))[s_1] \
               &= (restr(E, phi(x)))[s_1] \
               &= restr(E, phi_(s_1)(x))
  $

+ We only reach this state if it is safe (in terms of the consistency of $Gamma_j(C)$) and accurate
  to set $Gamma_j(C; k) = 1$ with use 0. Do so, unless it has already been done, (permanently) abandon cycle $(j, k)$
  and start cycle $(j, k+1)$.

  Once we reach this state, we define a value for $Gamma_j(C; k)$ which we _know_ to be correct, since $G(k)$ has already changed,
  and won't change again, $G$ being r.e.  Also, the "once-off" nature of the $G$-change means that the only way cycle $(j,k)$ is
  going to be able to satisfy requirement $R_e$ in the future, even with a new witness, is by being infinitely often in state~1; it
  cannot enumerate its witness into $A$, as the $G$-change it needs has already come and gone.  Although it is posisble that $(j,
  k)$ will be able to succeed in this manner, it is improbable. More likely is that cycle $(j, k)$ will be eventually stuck in state
  2, waiting forlornly for an impossible $G$-change, but in the meantime computing a correct value for $Gamma_j(C; k)$. We may as
  well cut our losses and simplify by abandoning this cycle: we content ourselves with the modest gain of a single correct value for
  $Gamma_j(C; k)$ and the knowledge that if we end up permanently abandoning _all_ cycles like this, we'll be able to compute $G$
  from $C$ (see #lemmaRef(<lemma2.17>) below), a contradiction.

+ We only reach _this_ state if it is similarly safe to set $Delta(C\; j) = 1$ with use 0. Do so, unless it has already been done.
  We permanently abandon the whole of row $row(j)$, and since there is no need to keep any of this row in business, it is convenient
  for technical reasons to reset every cycle in row $row(j)$, put cycle $(j, 0)$ into stage 8, and start cycle $(j+1, 0)$.

  The same comments as in state~7 just above apply here, but the result of the failure of cycle $(j, k)$ is even more stark. Now we
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
as we have no equivalent of the bookkeeping state~3 to worry about.

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

  [This is just like state~7 in the basic module for the $R_e$ requirements.]

// TODO: hacky (see above)
#show: doc => setupenum(doc)

=== Combining the modules <section2.3.3>

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
able to make the transition from state~2 to state~3 do so. Now there are 2 cases.
- #smallcaps("Case 1") #h(1em) Some least cycle $nu$ of strategy $alpha$ is able (or forced by a $C$-change) to act.

We allow cycle $nu$ to act. Let $lambda$ be the rightmost cycle of strategy $alpha$ now imposing restraint
(if there is any such cycle.) It is not necessarily the case that $lambda = nu$. If cycle $lambda$ is now in state~2, 3, or 4 then put
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

=== Lemmas for the $R_e$ strategy <section2.3.1>

==== The layout of the cycle states

We begin with a sequence of lemmas which describes the different arrangements possible of the states of the various cycles at any time.
The aim is to formalize the intuitive ideas that develop from an understanding of the way the construction works.

We assume that we have a certain, fixed strategy, $alpha$, of even length in mind, and that all cycles mentioned belong to this
strategy. Also, we ignore the fact that strategy $alpha$ may not be accessible at all (or even all sufficiently large) stages: we
just treat the stages mentioned as being the successive ones at which strategy $alpha$ _is_ accessible.

It will be convenient to refer to a cycle with is in either stage 5 or state~6 as being "in state~5/6".

#lemma[
    For any row $row(j)$, at most one cycle $(j, k)$ is in state~5/6.
    <lemma2.3>
]
#proof[
    We show that if cycle $(j, k)$ is in state~5 or state~6 at stage $s$ then nothing to the right of $(j, k)$ in row $row(j)$
    (namely, a cycle $(j, k') > (j, k)$) is in either of these states at stage $s$.

    If cycle $(j, k)$ entered state~5 from state~4 (and there is no other way), no cycles to the right of $(j, k)$ are in any state
    other than 0 at the start of stage $s$, because by entereing state~4, cycle $(j, k)$ reset every cycle to its right, and no new
    cycles were started so long as $(j, k)$ remained in state~4. Upon entering state~5, cycle $(j, k)$ starts cycle $(j+1, 0)$,
    and no cycle to the right of $(j, k)$ in row $row(j)$ is started so long as $(j, k)$ stays in state~5.

    On entering state~6, cycle $(j, k)$ resets every cycle to its right (including those in rows $row(j')$ for $j' > j$), and no
    cycle to its right will be started so long as $(j, k)$ remains in this state.
]

#lemma[
    Suppose cycle $(j, k)$ enters state~3 at stage $s$ due to cycle $(j, k')$ being in state~5/6. If at stage $t > s$ cycle $(j, k')$
    leaves state~5/6 for the first time, for any reason, then cycle $(j, k)$ is no longer in state~3 at the end of stage $t$.
    <lemma2.4>
]
#proof[
    Note that $mu_s(x(j, k)) = v_s(j, k')$.

    Cycle $(j, k')$ leaves state~5/6 either through acting or through being reset. If $(j, k') < (j, k)$ then we see that the
    action/resetting of $(j, k')$ also resets $(j, k)$, and the latter is no longer in state~3. (It will turn out later that a cycle
    can't be in state~3 when something in the same row to its left is in state~5/6, but we can't rule out that possibility yet.)

    If $(j, k) < (j, k')$ we must work substantially harder.

    In this case, if $(j, k')$ is able to get out of state~5/6 without being reset, we must have a change in $restr(C, v_t(j, k'))$
    (if $(j, k')$ goes to state~4) or in $restr(C, u_t(j, k')) subset restr(C, v_t(j, k'))$
    (if it goes to state~7). This very change in $C$ allows $(j, k)$
    to move to state~4, unless another cycle to its left acts for this same reason, resetting cycle $(j, k)$ completely.

    If $(j, k')$ is reset at $t$ by the action of a cycle to the left of $(j, k)$, cycle $(j, k)$ is reset also.

    Thus, aiming for a contradiction, we need only consider the case in which for some $k dubpr$ with
    $k < k dubpr < k'$, cycle $(j, k dubpr)$ acts at stage $t$,
    but $restr(C, v_t(j, k'))$ does not change at stage $t$. (Note that $v_t(j, k') = v_s(j, k')$.)
    Without loss of generality we may assume that $t$ is minimal in witnessing the failure of this lemma.
    Since cycle $(j, k')$ is "awake" (that is, in a state other than 0) between stages $s$ and $t$, cycle $(j, k dubpr)$
    must be in one of the states 2, 3 or 7, and cannot change states (other than going from 2 to 3) during this time, for otherwise
    cycle $(j, k')$ would be reset. We may may immediately discount the possibility that $(j, k dubpr)$ in state~7,
    because a cycle in this state cannot act. Thus, as stage $t$ starts, cycle $(j, k dubpr)$ is in state~2 or state~3.

    We first claim that $(j, k dubpr)$ can't make the transition from state~2 to state~1. Indeed, such a transition indicates a change
    in $restr(C, u(j, k dubpr))$. But cycle $(j, k')$ starts after cycle $(j, k dubpr)$ enters state~2, so by construction,
    $v_t(j, k') > x(j, k') > u(j, k dubpr)$, and we have a change in $restr(C, v_t(j, k'))$ at stage $t$, which is a contradiction.

    Cycle $(j, k dubpr)$ can't go from state~2 to state~3 at stage $t$, as this does not count as an action, so the only remaining
    possibility is the $3 arrow.r.bar 4$ transition, so that there is a change in $restr(C, mu_t(x(j, k dubpr)))$.
    We claim that $mu_t(x(j, k dubpr)) = v_t(j, k')$, and obtain the contradiciton of a change in $restr(C, v_t(j, k'))$.

    Suppose otherwise, so that $(j, k dubpr)$ enters state~3 for the sake of yet another cycle $(j, k trippr)$ being
    in state~5/6, or for another "incarnation" of cycle $(j, k')$; that is, for the sake of cycle $(j, k')$ being in state~5/6
    based on another computation. Well, if we are in the former case, cycle $(j, k trippr)$ must leave state~5/6 by stage $s$,
    by #lemmaRef(<lemma2.3>), forcing cycle $(j, k dubpr)$ out of state~3, by the assumption of the minimality of $t$.
    The same argument applies to another "incarnation" of cycle $(j, k')$. Thus, cycle $(j, k dubpr)$ enters state~3 for
    the sake of the same $(j, k')$-related computations that force cycle $(j, k)$ to do likewise, and
    $mu_t(x(j, k dubpr)) = mu_s(x(j, k')) = v_s(j, k') = v_t(j, k')$. We are done.
]
#lemma[
    For all $j$, if cycles $(j, k) neq (j, k')$ are both in state~3 at stage $s$, then
    $(mu(x(j, k)))[s] = (mu(x(j, k')))[s]$.
    <lemma2.5>
]
#proof[
    Suppose $(j, k)$ enters state~3 at stage $t$ and remains there until $(j, k')$ does the same at stage $t' > t$, and
    that they both stay in this state until at least stage $s$. By Lemmas #thmref(<lemma2.3>) and #thmref(<lemma2.4>),
    both cycles must enter state~3 for the sake of the same cycle being in stage 5/6, and for the same computations.
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
$setconcat(M, N) = {concat(theta, sigma) st theta in M and sigma in N}$,
the finite sequences got by appending a sequence from $N$ to a sequence from $M$. For convenience we also allow the notation
$angletup(M) = { angletup(theta) | theta in M }$, the length 1 sequences consisting of single terms from $M$. We define the
following subsets of $finseq(X)$:
$
  prelimCrampedRow  &= setconcat(finseq({2, 3, 7}), angletup({5})), \
  finalCrampedRow   &= setconcat(finseq({2, 3, 7}), angletup({6})), \
  crampedRow        &= prelimCrampedRow union finalCrampedRow, \
  uncrampedRow      &= setconcat(finseq({2, 7}), angletup({1, 4})), \
  abandonedRow      &= angletup({8}), \
  prelimRow         &= prelimCrampedRow union abandonedRow, \
  finalRow          &= finalCrampedRow union uncrampedRow,
$
and a subset of $finseq((finseq(X)))$
$
  validPattern = setconcat(finseq(prelimRow), angletup(finalRow)).
$
The names are intended to be somewhat mnemonic. "Cramped" refers to a row in which cycles are prevented from reaching state~4 by the
presence of a cycle in that row in state~5/6. These cycles have their style cramped: they must bide their time in state~3 waiting
for the chance to go to state~4 later. A "#patternName("prelim")" row is one that isn't the last in the list: the row after it also
has at least one cycle not in state 0.

When we want to make it clear how long a finite sequence is, we subscript the sequence with its length, like so:
$angletup(0, 1, dots, 7)_8$.

The claim is now that if strategy $alpha$ has been started since last being cancelled, its pattern in "valid":
#lemma(name: "Pattern Lemma")[
    If strategy $alpha$ has at least one cycle not in state 0 at stage $s$, $pattern(s) in validPattern$.
    <patternLemma>
]

#proof[
    #let angle8 = angletup(8)
    We proceed by induction on the number of stages since the last time strategy $alpha$ had a cycle started after previously being
    cancelled.

    When a strategy is started up (perhaps not for the first time), as stage $s$, cycle $(0, 0)$ is started. If this cycle, or row
    $row(0)$, has been abandoned before, subsequent cycles are automatically started as well in the cascading effect mentioned at
    the start of @basicModuleRe. Let $j = min_iota{ "row" row(iota) "never abandoned" }$,
    and let $k = min_kappa { "cycle" (j, k) "never abandoned" }$. Then the pattern at stage $s$ is
    $
      pattern(s) = angletup(angle8, angle8, dots, angle8, angletup(7, 7, dots, 7, 1)_(k+1))_(j+1).
    $
    This is a valid pattern, as $angle8 in prelimRow$ and $angletup(7, dots, 7, 1) in uncrampedRow subset finalRow$.

    Now suppose that $alpha$'s pattern is valid coming into stage $s$, that strategy $alpha$ is not cancelled at $s$, and that something
    actually appens: some cycle of the strategy changes state.  We let $pattern(s-1) = angletup(p_0, p_1, dots, p_n, f)$, where
    $p_i in prelimRow$ and $f in finalRow$. First consider any $2 arrow.r.bar 3$ transitions. These can occur only in a crampedRow,
    as only such rows have anything in state~5/6. But a 3 in place of a 2 leaves the type of crampedRow
    (either #patternName("prelim") or #patternName("final")) unchanged, so the pattern is still valid after such changes.  From now on let
    $pattern(s-1)$ represent the pattern after all $2 arrow.r.bar 3$ state transitions are taken into accout, bet before any action is
    recorded.

    If no cycle of the strategy actually acts at stage $s$ we are done. Otherwise, let $(j, k)$ be the leftmost cycle which acts. We
    have a large collection of cases and subcases.

    #show: doc => setupenum(doc, formats: ("I.", "1.", "a."))
    + $j = n + 1$, so the action is in the last row.

      + Row $row(j)$ is cramped: $f = angletup(h_0, h_1, dots, h_m, 6)$, $h_i in {2, 3, 7}$.

        + $k = m + 1$, so cycle $(j, k)$ is in state~6.

          The only way that cycle $(j, k)$ to act is to go to stage 7, starting cycle $(j, k+1)$. This means that
          we can't have any $j_i = 3$ for $i leq m$, since any cycle $(j, i) < (j, k)$ in state~3 at the start
          of stage $s$ would have left that state, by #lemmaRef(<lemma2.4>). Let $k' = min_(kappa > k) { "cycle" (j, kappa) "never abandoned" }$.
          Then the new pattern for row $row(j)$ is $f' = angletup(h_0, dots, h_m, 7, dots, 7, 1)_(k' + 1) in finalRow$.
          Thus $pattern(s) = angletup(p_0, dots, p_n, f')$ in validPattern.

        + $k < m+1$ and cycle $(j, k)$ is in state~2.

          The action of $(j, k)$ can't just be to enter state~3, as such a transition does not count as an action.
          Neither can $(j, k)$ enter state~4, as the row is cramped, and such a transition is prohibited. Thus the
          action is to go back to state~1 due to a change in $restr(C, u_s(j, k))$. Now, since the action of cycle $(j, k)$
          resets cycle $(j, m+1)$, by #lemmaRef(<lemma2.4>) we cannot have $h_i = 3$ for any $i < k$. Thus $h_i in {2, 7}$
          for $i < k$. But now the new pattern for row $row(j)$ is $f' = angletup(h_0, dots, h_(k-1), 1) in uncrampedRow$
          and again $pattern(s) in validPattern$.

        + $k < m+1$ and cycle $(j, k)$ is in state~3.

          First note that, as in the previous case, $h_i in {2, 7}$ for $i < k$. In entering state~4 cycle $(j, k)$ resets
          all cycles to its right, so the new pattern for row $row(j)$ is $f' = angletup(h_0, dots, h_(k-1), 4) in uncrampedRow$.
          Again $pattern(s) in validPattern$.

       We don't need a case for cycle $(j, k)$ being in state~7, as such a state can't act.

     + Row $row(j)$ is uncramped: $f = angletup(h_0, h_1, dots, h_m, b)$, $h_i in {2, 7}, b in {1, 4}$.

       + $k = m + 1$, and cycle $(j, k)$ is in state~1.

         The action of $(j, k)$ must take it to state~2, starting cycle $(j, k+1)$.
         Let $k' = min_(kappa > k) { "cycle" (j, kappa) "never abandoned" }$. The new pattern for row $row(j)$ is
         $f = angletup(h_0, dots, h_m, 7, dots, 7, 1)_(k' + 1) in finalRow$. Thus $pattern(s) in validPattern$.

       + $k = m + 1$, and cycle $(j, k)$ is in state~4.

         If the action of $(j, k)$ is to go to state~5, the new pattern for row $row(j)$ must be
         $f' = angletup(h_0, dots, h_m, 5) in prelimCrampedRow subset prelimRow$. In the same way as above,
         let $j' = min_(iota > j) { "row" row(iota) "never abandoned" }$
         and $k' = min_kappa { "cycle" (j', kappa) "never abandoned" }$.
         Then the new pattern for the strategy is
         $
           pattern(s) = angletup(p_0, dots, p_n, f', angle8, dots, angle8, angletup(7, dots, 7, 1)_(k' + 1))_(j' + 1).
         $
         If, instead, $(j, k)$'s action is to go to state~8, row $row(j)$ is abandoned as a whole, and its new pattern
         will simple be angle8. Define $j'$ and $k'$ as before and the new pattern for the strategy will be
         $
           pattern(s) = angletup(p_0, dots, p_n, angle8, dots, angle8, angletup(7, dots, 7, 1)_(k' + 1))_(j' + 1).
         $
         In either case, the new pattern is valid.

     + $k < m+1$. We have that cycle $(j, k)$ is in state~2, since a cycle can't act if it is in state~7.

       This action can take cycle $(j, k)$ to either state~1 or state~4. In either case, all cycles to the
       right of $(j, k)$ are reset and the new pattern for row $row(j)$ is $f' = angletup(h_0, dots, h_(k-1), b')$,
       where $b = 1$ or $b = 4$ according as how the cycle acted. In either case, $f' in uncrampedRow$,
       and the new pattern for the strategy $pattern(s) = angletup(p_0, dots, p_n, f')$ is still valid.

  + $j < n+1$. Row $row(j)$ can't ever have been abandoned, as otherwise no cycle it in could act, so
    $p_j = angletup(h_0, dots, h_m, 5) in prelimCrampedRow$. Note that for $i leq m$, $h_i in {2, 3, 7}$.

    + $k = m+1$, so cycle $(j, k)$ is in state~5.

      If the action consists of returning to state~4, no cycles in row $row(j)$ to the left of
      $(j, k)$ can still be in state~3, by Lemmas #thmref(<lemma2.4>) and #thmref(<lemma2.5>).
      Thus $h_i in {2, 7}$ for $i < m+1$. The action resets all cycles to the right of $(j, k)$ (including
      those is rows $row(l)$, $l > j$), so the new pattern for row $row(j)$ is
      $p'_j = angletup(h_0, dots, h_m, 4) in uncrampedRow$, and the pattern for the whole strategy is
      $pattern(s) = angletup(p_0, dots, p_(j-1), p'_j) in validPattern$.

      If instead the action of $(j, k)$ consists of advancing to state~6, again all cycles to the right
      of $(j, k)$ are reset, but now we can't say anything new about the status of cycles in row $row(j)$
      to the left of $(j, k)$. This doesn't matter though, since the new pattern for row $row(j)$ is
      $p'_j = angletup(h_0, dots, h_m, 6) in finalCrampedRow$, and the pattern for the strategy is
      $pattern(s) = angletup(p_0, dots, p_(j-1), p'_j) in validPattern$.

    + $k < m + 1$. Clearly $h_k neq 7$, so we have two cases, $h_k = 2$ and $h_k = 3$.

      + $h_k = 2$.

        Cycle $(j, k)$ can't advance to state~4, as the row is cramped, and it can't go to state~3,
        as such a transition doesn't count as acting. Thus the action must consist of cycle $(j, k)$
        returning to state~1 on the basis of a change in $restr(C, u_s(j, k))$. As above (case I.1.b)
        we conclude that the new pattern for row $row(j)$ is
        $p'_j = angletup(h_0, dots, h_(k-1), 1) in uncrampedRow$. As all cycles to the right of $(j, k)$
        are reset, the pattern for the whole strategy is therefore
        $pattern(s) = angletup(p_0, dots, p_(j-1), p'_j) in validPattern$.

      + $h_k = 3$.

        This case is to case I.1.c as case II.2.a is to case I.1.b.

  Thus the new pattern $pattern(s)$ is valid, and we are done.
]
#show: doc => setupenum(doc)

==== Consistency of the functions $Gamma_j(C)$ and $Delta(C)$

Here we show that the functionals $Gamma_j$ and $Delta$ are defined in a such a way that at every stage
$s$ $(Gamma_j(C))[s]$ and $(Delta(C))[s]$ are well defined (partial) functions. The failure of this property
was one of the technical flaws in the original paper @CLW1989.

For the following lemmas we again assume that we have fixed in our minds a specific node/strategy of the construction,
and restrict our attention to the functionals associated with this strategy.
#lemma[
    For all $j$ and $k$, if cycle $(j, k)$ is in state~5 at stage $s$, then $(Delta(C\; j))[s] converge$.
    The same conclusion can be made if row $row(j)$ was abandoned at some stage before $s$.
    <lemma2.7>
]
#proof[
    If cycle $(j, k)$ is in state~5, we must have in particular $restr(C_s, v(j, k)) = restr(C_(s_2), v(j, k))$.
    But $v(j, k) = delta_(s_0)(j)$, so the computation for $Delta(C\; j)$ that was defined by cycle $(j, k)$
    when it entered state~5 is still defined.

    If, instead, row $row(j)$ was abandoned at some earlier stage, this abandonment was accompanied by
    a definition of $Delta(C\; j)$ with use 0. Such a computation can never become undefined, and must persist to stage $s$.
]

#lemma[
    If some cycle $(j, k)$ acts at stage $s$ to define a computation for $Delta(C\; j)$,
    then for eaach $i < j$, ($Delta(C\; i))[s] converge$.
    <lemma2.8>
]
#proof[
    Such a cycle can act in this way only by moving from state~4 to either state~5 or state~8. In either case,
    the pattern corresponding to row $row(j)$ coming into stage $s$ must have been an uncrampedRow.
    So, by the Pattern Lemma, for each $i < j$, the pattern for row $row(i)$ must either be angle8
    (indiciating that row $row(i)$ was abandoned at some time) or an element of prelimCrampedRow. In the latter
    case, each row $row(i)$ has some cycle in state~5 as we enter stage $s$. But no cycle in any row $row(i)$, $i < j$
    acts at stage $s$, as othwerwise cycle $(j, k)$ would be reset and unable to act. Thus the pattern of each of these rows
    is unchanged (except perhaps for 2 changing to 3) during stage $s$, and each has a cycle in state~5 at the end of the stage.

    So, by #lemmaRef(<lemma2.7>), $(Delta(C\; i))[s] converge$.
]

A similar argument establishes the following.
#lemma[
    If some cycle $(j, k)$ acts at stage $s$ to define a computation for $Gamma_j(C; k)$,
    then for each $i < k$, ($Gamma_j(C; i))[s] converge$.
    <lemma2.9>
]

Now we can prove that the functionals are defined consistently.

#show: doc => setupenum(doc, formats: ("(I)", "a"))
#lemma[
    For all $j in omega$,

    + For $i < j$, if $(Delta(C\; i))[s] converge$ and $(Delta(C\; j))[s] converge$ with $delta_s(j) > 0$
      then $delta_s(i) < delta_s(j)$.
    + Row $row(j)$ defines a computation for $Delta(C\; j)$ only when no other such computation is currently defined.
    <lemma2.10>
]
#proof[
    Notice that we may assume that the strategy in questino is not cancelled during
    any of the stages of interest to us in this lemma. If such a cancellation were to occur, all functionals
    associated with our strategy would be discarded and the lemma follows trivially.

    We proceed by induction. Assume that (I) and (II) hold for $0, 1, dots, j-1$.

    First note that when any cycle $(j, k)$ of $row(j)$ starts it chooses a witness $x(j, k)$ larger than
    any number mentioned so far. In particular, $x(j, k)$ is larger than the use of any $Delta(C\; i)$
    computation (for $i < j$) still defined when the witness is chosen. As the defintition of such
    a new computation would involve the resetting of cycle $(j, k)$ (by the Pattern Lemma), $x(j, k)$
    will remain larger than the use of any currently defined $Delta(C\; i)$ computation. But
    if cycle $(j, k)$ ever defines a compuation for $Delta(C\; j)$, then $delta(j) = v(j, k) > x(j, k)$
    will also be larger than the uses of prior $Delta(C\; i)$ computations. So (I) will never be violated
    by a row defining a $Delta$-computation with a use smaller than the uses of computations defined by earlier rows.

    So, suppose that for the first time, at stage $s$, (I) is about to be violated by a row defining a
    computation with a use larger than the use currently defined by a later row:
    $Delta(C\; j)[s] converge$, $i < j$, and we are about to define $Delta(C\; i)$ such that $delta_s(i) geq delta_s(j) > 0$.
    Let $t < s$ be the stage at which the computation $(Delta(C\; j))[s]$ was defined.
    By #lemmaRef(<lemma2.8>), $(Delta(C\; i))[t] converge$ and by the minimality of $s$, $delta_t(i) < delta_t(j) = delta_s(j)$.
    By the inductive hypothesis, $(Delta(C\; i))[t]$ must get undefined before stage $s$, as we redefine this value
    at stage $s$. But such an undefinition#footnote[This is only marginally a word.] can only occur through a change in
    $restr(C, delta_t(i))$ which implies a change in $restr(C, delta_s(j))$ and the undefinition of the computation
    $(Delta(C\; j))[t]$, contradicting our assumption. This verifies (I) for $j$.

    For the sake of contradiction, suppose (II) fails at $j$. That is, suppose that at stage $s$ cycle $(j, k)$
    defines $Delta(C\; j)$, and another computation for this value is still current, having been defined at stage
    $t < s$ by cycle $(j, k')$ with use $delta_t(j) = v_t(j, k')$. We note the following:

    - $restr(C_s, v_t(j, k')) = restr(C_t, v_t(j, k'))$.

    - For all $i < j$, $(Delta(C\; i))[t] converge$ and by (I) $delta_t(i) < delta_t(j) = v_t(j, k')$.

    - We know that $delta_t(j) > 0$, for a definition of $Delta(C\; j)$ with use 0 would have
      led to the abandoning of row $row(j)$ in its entirety at stage $t$ and the consequent impossibility of
      cycle $(j, k)$ acting now.

    - All cycles in row $row(j)$ to the left of $(j, k')$ must be in state~2 or state~7 at stage $t$.
      This follows from the Pattern Lemma, as the definition of the $Delta(C\; j)$ computation at stage $t$
      implies that cycle $(j, k')$ started that stage in state~4, and so the pattern for row $row(j)$ formed
      an #uncrampedRow at $t$.

    - Because of the constraints listed at state~2, no cycle of row $row(j)$, except perhaps for cycle $(j, k')$
      itself, may act so long as cycle $(j, k')$ remains in state~5 or 6. (The $C$-change which allows a cycle
      to the left of $(j, k')$ to leave state~3 is precisely the change that forces cycle $(j, k')$ out of state
      5 or 6. The cycles in row $row(j)$ to the right of cycle $(j, k')$ cannot act, as the "next" cycle
      to the right of $(j, k')$ allowed to act under these circumstances is cycle $(j+1, 0)$, in row $row(j+1)$.)

    Now, cycle $(j, k')$ does not exit cycle 5/6 before stage $s$ "under its own steam", as this would involve
    a change in $restr(C, v_t(j, k'))$, which we have seen does not occur. Thus the only way that _any_
    cycle in row $row(j)$ can act at stage $s$ is if all the cycles of the row are first reset by the action
    of a cycle in row $row(i)$, for $i < j$, at stage $t'$, where $t < t' < s$. When row $row(i)$ later
    starts row $row(i+1)$ (which is must do before stage $s$) it in the process defines a new computation
    for $Delta(C\; i)$. By the inductive hypothesis, the previous computation must have become undefined,
    which means that $restr(C_s, delta_t(i)) neq restr(C_t, delta_t(i))$ and hence
    $restr(C_s, v_t(j, k')) neq restr(C_t, v_t(j, k'))$, contradicting our assumption.

    Thus such an attempted redefinition never occurs, and the inductive step in complete.
]

We have the analogous result for the $Gamma$ functionals.

#lemma[
    For each $j$ and each $k$

    + For $i < k$, if $(Gamma_j(C; i))[s] converge$ and $(Gamma_j(C; k))[s] converge$ with $gamma_(j,s)(k) > 0$
      then $gamma_(j,s)(i) < gamma_(j,s)(k)$.

    + Cycle $(j, k)$ defines a computation for $Gamma_j(C; k)$ only when no other such computation is currently defined.
    <lemma2.11>
]
#proof[
    Again we may assume that the strategy is not cancelled during stages that concern us.

    We proceed as before, by induction. So, fix $j$ and assume that (I) and (II) hold for $0, 1, dots, k-1$.

    The comments at the start of the proof of #lemmaRef(<lemma2.10>) are valid here too: a computation for
    $Gamma_j(C; k)$ will never be defined with a a non-zero use less than the use of a previously defined
    computation for $Gamma_j(C; i)$, where $i < k$.

    Suppose that at stage $s$, $(Gamma_j(C; k))[s] converge$ and for the first time we are about to violate (I): we define
    $Gamma_j(C; i)$ with $i < j$ such that $gamma_(j,s)(i) geq gamma_(j,s)(k) > 0$. Let $t < s$ be the stage at which the current
    computation for $Gamma_j(C; k)$ was defined. By #lemmaRef(<lemma2.9>), $(Gamma_j(C; i))[t] converge$ and by the minimality of
    $s$, $gamma_(j,t)(i) < gamma_(j,t)(k) = gamma_(j,s)(k)$.  But the computation for $Gamma_j(C; i)$ valid at stage $t$ must get
    undefined before stage $s$, by the inductive hypothesis, so $restr(C_s, gamma_(j,t)(i)) neq restr(C_t, gamma_(j,t)(i))$ which
    implies $restr(C_s, gamma_(j,s)(k)) neq restr(C_t, gamma_(j,s)(k))$.  This means that the computation $(Gamma_j(C; k))[s]$
    actually becomes undefined at some stage between $t$ and $s$, a contradiction. This establishes (I) for $k$.

    Now suppose that (II) fails for k: at stage $s$ cycle $(j, k)$ defines $Gamma_j(C; k)$ but another
    computation, $(Gamma_j(C; k))[t]$, exists from an earlier stage $t < s$. Note that
    $restr(C_s, u_t(j, k)) = restr(C_t, u_t(j, k))$. Note also that $gamma_(j,t)(k) > 0$, since the definition
    of a computation of use 0 would lead to the permenent abandonment of cycle $(j, k)$ at stage $t$. This cycle
    would therefore be unable to act at stage $s$.

    Now, only cycle $(j, k)$ can define a computation for $Gamma_j(C; k)$. It cannot merely have returned to state~1 and again to
    state~2 between stages $t$ and $s$, as this requires a change in $restr(C, u_t(j, k))$. Neither can it advance from state~2 to
    state~7 between stages $t$ and $s$, as entering state~7 entails the same $C$-change. Thus in order to have another crack at
    defining $Gamma_j(C; k)$, cycle $(j, k)$ must be reset and later restarted. If ever something in row $row(i)$, for $i < j$,
    acts, the functional $Gamma_j(C)$ is discarded wholesale, preventing any conflicting definition
    at stage $s$. So, at some stage $t' in (t, s)$ some cycle $(j, k') < (j, k)$ acts, resetting $(j, k)$
    (if it hadn't been reset since stage $t$ already.) By #lemmaRef(<lemma2.9>), $(Gamma_j(C; k'))[t] converge$ and by part (I)
    $gamma_(j,t)(k') < gamma_(j,t)(k)$. Before stage $s$ cycle $(j, k')$ must restart cycle $(j, k' + 1)$, and at the same
    time define a new computation for $Gamma_j(C; k')$. But by the inductive hypothesis the previous such computation
    (_i.e._ that valid at stage $t$) must have become undefined. This meanst hat there has been a change
    since stage $t$ in $restr(C, gamma_(j,t)(k')) subset restr(C, gamma_(j,t)(k))$. But $gamma_(j,t)(k) = u_t(j, k)$,
    so this is a contradiction.

    The lemma is proved.
]

=== Lemmas for the $P_e$ strategy <section2.3.2>

@section2.3.1 was a long and complicated one. As the $P_e$ strategy is so much simpler than the $R_e$ one,
the corresponding set of lemmas is also. We assume we have fixed a strategy $alpha$ of odd length. Again
we streat all stages mentioned as being the succissive ones at which strategy $alpha$ is actually accessible.
We start by discussing the patterns that the cycle states can make. We again refer to the pattern at stage $s$
as $pattern(s)$.

As the $P_e$ strategy involves a one-dimensional array of cycles, the pattern formed by the cycle-states
in this case is simply a finite sequence of state-names. There is no need for the sequence of sequences
used in the $R_e$ strategy argument.

#let plabel(n) = $upright(P)#n$
Let $Y = {plabel(0), plabel(1), ..., plabel(4)}$. Using the same notation as in the definition of #validPattern we may
define a single subset of $finseq(Y)$:
$
  validPatternForP = setconcat(finseq({plabel(2), plabel(4)}), angletup({plabel(1), plabel(3)}))
$
We then have the following analogue to the Pattern Lemma.#footnote[We don't refer to this result as a "Pattern Lemma",
                                                                   as it is too simple to deserve a name.]

#lemma[
    If strategy $alpha$ has at least one cycle not in state #plabel(0) at stage $s$, $pattern(s) in validPatternForP$.
    <lemma2.12>
]
#show: doc => setupenum(doc, formats: ("I.", "1.", "a."))
#proof[
    If strategy $alpha$ is started at stage $s$, cycle 0 is started, perhaps having been abandoned in the past.
    Let $j = min_iota{ "cycle" iota "never abandoned" }$. Then the pattern at the end of stage $s$
    is $pattern(s) = angletup(plabel(4), dots, plabel(4), plabel(1))_(j+1) in validPatternForP$.

    Now suppose that $pattern(s-1)$, $alpha$'s pattern coming into stage $s$, was valid and that strategy $alpha$
    is not cancelled at $s$. If no cycle of $alpha$ acts at stage $s$ then $pattern(s) = pattern(s-1)$ and there
    is nothing to prove. So, suppose some cycle does act, let $k$ be the leftmost one, and write
    $pattern(s-1) = angletup(h_0, dots, h_m, b)$, where $h_i in {plabel(2), plabel(4)}$ and $b in {plabel(1), plabel(3)}$.
    We again have several cases.

    + $k = m+1$. There are two subcases.
      + $b = plabel(1)$.

        Cycle $k$ must act by advancing to state #plabel(2), starting cycle $k+1$ in the process.
        Let $j = min_(j' > k){"cycle" j' "never abandoned"}$. Then the new pattern is
        $
          pattern(s) = angletup(h_0, dots, h_m, plabel(2), plabel(4), dots, plabel(4), plabel(1))_(j+1) in validPatternForP.
        $

      + $b = plabel(3)$.

        Now cycle $k$ acts by advancing to state $plabel(4)$, again starting cycle $k+1$. Using the same definition for $j$
        as in the previous case we have
        $
          pattern(s) = angletup(h_0, dots, h_m, plabel(4), dots, plabel(4), plabel(1))_(j+1) in validPatternForP.
        $

    + $k < m + 1$. Now there is only one case, $h_k = plabel(2)$, as a cycle already in state $plabel(4)$ cannot act.
      However cycle $k$ acts, all cycles to the right of $k$ are reset. If cycle $k$ acts by returning to state #plabel(1)
      the new pattern is
      $
        pattern(s) = angletup(h_0, dots, h_(k-1), plabel(1)).
      $
      If, however, cycle $k$ enters state #plabel(3) we have
      $
        pattern(s) = angletup(h_0, dots, h_(k-1), plabel(3)).
      $
      Either way, $pattern(s) in validPatternForP$, and we are done.
]

Now there are some results corresponding to Lemmas #thmref(<lemma2.7>)--#thmref(<lemma2.11>).

#lemma[
    If cycle $k$ is in state #plabel(2) or state #plabel(4) at stage $s$ then $Xi(C\; j)[s] converge$.
    <lemma2.13>
]
#proof[
    If cycle $k$ is in state #plabel(2) at stage $s$ then, in particular, $restr(C_s, u_t(k)) = restr(C_t, u_t(k))$
    where $t < s$ is the stage at which cycle $k$ last entered state #plabel(2). This means that $(Xi(C\; k))[t]$,
    the computation defined at $t$, is still valid at $s$.

    If cycle $k$ is in state #plabel(4) then it must have been abandoned at some earlier stage.
    The abandonment was accompanies by a definition of $Xi(C\; K)$ with use 0, so this computation must persist to stage $s$.
]

#lemma[
    If cycle $k$ is in any state other than #plabel(0) at stage $s$, then $(Xi(C\; k'))[s] converge$ for all $k' < k$.
    <lemma2.14>
]
#proof[
    Lemmas #thmref(<lemma2.12>) and #thmref(<lemma2.13>).
]


#lemma[
    #show: doc => setupenum(doc, formats: ("(I)", "1.", "a."))
    + For $i < k$, if $(Xi(C\; i))[s] converge$ and $(Xi(C\; k))[s] converge$ with $xi_s(k) > 0$ then $xi_s(i) < xi_s(k)$.
    + Cycle $k$ defines a computation for $Xi(C\; k)$ only when no such other computation is currently defined.
    <lemma2.15>
]
#proof[
    As in Lemmas~#thmref(<lemma2.10>) and~#thmref(<lemma2.11>) we may assume that strategy $alpha$ is not cancelled during
    the stages that concern us.

    We proceed by induction. Fix $k$ and assume (I) and (II) for $0, 1, dots, k-1$. Statement (I) holds for $k$
    by the same argument as in #lemmaRef(<lemma2.11>), which we don't repeat.

    Suppose that (II) fails for $k$: that is, as some (least) stage $s$, cycle $k$ defines a computation $Xi(C\; k)$
    while another computation $(Xi(C\; k))[t]$ is still valid from an earlier stage.
    Note that $restr(C_s, u_t(k)) = restr(C_t, u_t(k))$ and that $u_t(k) = xi_t(k) > 0$.

    Now, since $C$ did not change below $u_t(k)$ between stages $t$ and $s$, cycle $k$ cannot merely have
    returned to state #plabel(1) and then attempted to redefine $Xi(C\; k)$.
    The only possibility is that cycle $k$ is reset by the action of some cycle to the left, at some stage
    between $t$ and $s$. Let $k' < k$ be the leftmost cycle to act between stages $t$ and $s$, and let
    it so act for the first time at stage $t' in (t, s)$. Since it is leftmost in acting, it is not itself
    reset between $t$ and $s$. We note that $(Xi(C\; k'))[t] converge$ (by #lemmaRef(<lemma2.14>))
    and $u_t(k') = xi_t(k') < xi_t(k)$, by (I).

    Now cycle $k'$ must have been in state #plabel(2) by stage~$t$, by #lemmaRef(<lemma2.12>), as cycles in
    state~#plabel(4) cannot act again before being reset. Cycle $k'$ cannot act at $t'$ by returning
    to state~#plabel(1) as this would mean a change in $restr(C, xi_t(k')) subset restr(C, xi_t(k))$
    which contradicts our assumption. Thus cycle $k'$ acts by reaching state~#plabel(3). As cycle $k'$
    is not reset before stage $s$ it can not reenter state~#plabel(1) before $s$. It must
    therefore enter #plabel(4) before stage~$s$, by #lemmaRef(<lemma2.12>), as cycle $k$
    is not in state~#plabel(0) at stage~$s$. But cycle $k'$ passes from state~#plabel(3) to state~#plabel(4)
    only when it sees a change in $restr(C, xi_t(k'))$, which again leads to the contradiction of
    a change in $restr(C, xi_t(k))$.

    We are done.
]

=== Satisfaction of the requirements <sec2.3.3>

The following sequence of lemmas derives from~@LaForte, but we do not here concern ourselves with path restraint.

At the point, many of the fundamental differences between the two types of strategy have been abstracted away into the preceding
lemmas. From now on th we discuss both types in each lemma: there is no need for separation.

The key object in the verification is the _true path_, $f$, through the priority tree $T$, defined by
$f(n) = xi$, where $concatone((restr(f, n)), xi)$ is the leftmost successor of $restr(f, n)$ accessible infinitely often.

The following result is the key one.

#proposition[
    #show: doc => setupenum(doc, formats: ("1.", "a."))
    For all $n in omega$
    + $f(n)$ is defined;

    + $restr(f, (n+1))$ is cancelled only finitely often, (note that $restr(f, 0) = emptyset$ is never cancelled);

    + strategy $restr(f, n)$ satisfies the requirement towards which it works;

    + for all sufficiently large $C$-true stages $t$, $restr(f, (n+1)) subset f_t$.
    <prop2.16>
]

So, inductively assume 1, 2, 3 and 4 for $n = eta - 1$, and let $alpha = restr(f, eta)$. Fix a stage $s_0$
so large that $alpha$ is not cancelled after $s_0$, and for every $C$-true stage $t > s_0$, $alpha subset f_t$.

We say that strategy $alpha$ _acts finitely_ if there is a stage $s$ after which no cycle of $alpha$ every
acts. Otherwise we say that $alpha$ _acts infinitely_.

#lemma[
    If $alpha$ acts infinitely then some specific cycle of $alpha$ acts infinitely often.
    <lemma2.17>
]
#proof[
    Suppose otherwise, and begin by assuming that $|alpha| = 2e$. Infinitely many individual cycles of $alpha$
    eventually act, but each does so only finitely often. So, each of these cycles must eventually get
    permanently stuck in a state which does not prevent subsequent cycles from acting in turn. There are two
    basic possibilities.

    #show: doc => setupenum(doc, formats: ("(A)",))
    + Some (leftmost) row $row(j)$ acts infinitely often. That is, infinitely often a cycle of the form
      $(j, k)$ acts, but no single cycle of this form acts infinitely often.

    + Every row acts, but each acts only finitely often.

    We consider (A) first.

    Fix $j$ minimal so that row $row(j)$ acts infinitely, and let $t_0 > s_0$ be so large that no cycle
    of the form $(i, k)$ for $i < j$ acts after stage~$t_0$. Since row~$row(j)$ acts infinitely, but each
    cycle in it acts only finitely often, _every_ cycle $(j, k)$ must eventually act, and get stuck in a way
    which does not prevent cycle~$(j, k+1)$ from acting. This means that each cycle in the row
    must eventually get parmanently stuck in state~2 or state~3, or is abandoned.

    By #lemmaRef(<lemma2.4>) a cycle gets permanently stuck in #state(3) only if another cycle in its
    row gets permanently stuck in #state(5) or #state(6), which we have seen does not happen to row~$row(j)$.
    Thus in fact every cycle of row~$row(j)$ eventually gets permanently stuck in #state(2) or is
    abandoned in #state(7). In the latter case, $Gamma_j(C; k)$ is correctly defined to be
    $1 = G(k)$ with use~0. We claim that the cycles which get permantently stuck in #state(2) also
    compute a correct value. Well, suppose that $(j, k)$ gets so stuck. It must be that
    $restr(C, u(j,k)) = restr(C_(s_1(j,k)), u(j, k))$ _and_ $G(k) = G_(s_1(j,k))(k)$. But then
    $
    Gamma_j(C; k) &= (Gamma_j(C; k))[s_1] \
                  &= (G(k))[s_1] \
                  &= G(k)
    $
    and we have a correct definition again. Now, by~#lemmaRef(<lemma2.11>), $Gamma_j(C)$ is
    a well-defined, $C$-recursive function. By the argument above, for all $k in omega$,
    $G(k) = Gamma_j(C; k)$, and we see that $G leqt C$, a contradiction.

    Suppose outcome (B) happens. We aim for a similar contradiction. Each row acts only finitely,
    but every row eventually acts, so given $j in omega$ there are $k_j$ and $t_j > t_(j-1)$
    such that cycle $(j, k_j)$ starts cycle $(j+1, 0)$ at stage $t_j$ and no cycle of
    row $row(j)$ ever acts again. So, at stage $t_j$, cycle $(j, k_j)$ must enter #state(5) never
    to leave, or #state(8), abandoning row $row(j)$.

    In the latter case, $Delta(C\; j) = 1 = G(j)$. In the former, we may argue as above that
    each such cycle computes a value for $Delta(C\; j)$ with agrees with $G(j)$. So again
    $G leqt C$, which is a contradiction, and outcome (B) cannot occur.

    For the case $|alpha| = 2e + 1$ the argument is much simpler. Since the cycle sequence
    is one-dimensional, _every_ cycle must end up getting stuck in #state(plabel(2)) or #state(plabel(4)).
    As before, each cycle will compute a value for $Xi(C)$ which agrees with $G$, and we see
    that $G leqt C$ again.

    The lemma is proved.
]

We extract part of the proof of the preceeding lemma as a separate result.
#lemma[
    Given s strategy $alpha$, if $chi$ is the leftmost cycle of strategy $alpha$ to act infinitely
    often then only finitely often can _any_ cycle to the left of $chi$ act.
    <lemma2.18>
]
#proof[
    Suppose otherwise, and write $chi = (j, k)$. If there is infinitely much action
    involving cycles to the left of cycle~$(j, 0)$ then one of the rows $row(0), dots, row(j-1)$
    must act infinitely, and we find ourselves in the impossible case (A) of~#lemmaRef(<lemma2.17>).

    But now now there must be infinite action among the cycles $(j, 0), dots (j, k-1)$. But this is impossible,
    as one of these cycles must act infinitely often, contradicting the definition of~$chi$.
]

#lemma[
    Some (leftmost) successor of $alpha$ is accessible infinitely often.
    <lemma2.19>
]
#proof[
    If $alpha$ acts finitely, then after some stage~$s$ no cycle of $alpha$ ever acts again.
    If $nu$ is the rightmost cycle of $alpha$ imposing restraint at stage~$s$, then
    $concatone(alpha, (nu, 1))$, $concatone(alpha, (nu, 2))$, or $concatone(alpha, nu)$
    (as appropriate to the parity of $|alpha|$ and the behavior of cycle $nu$) will be accessible
    at every stage after $s$ at which $alpha$ is accessible. If there is no such $nu$
    then $concatone(alpha, -1)$ will be accessible in the same way. But $alpha$ is accessible
    at every $C$-true stage $t > s_0$.

    Otherwise $alpha$ acts infinitely. Suppose first that $|alpha|$ is even and (by #lemmaRef(<lemma2.17>))
    let $nu$ be the leftmost cycle of strategy $alpha$ which acts infinitely often. By #lemmaRef(<lemma2.18>)
    choose $s > s_0$ large enough that cycle $nu$ is not reset after stage $s$ by the action of any $alpha$-cycles
    to its left. Suppose for the moment that $nu^-$ is the rightmost cycle of $alpha$ to the left of $nu$
    imposing restraint at stage $s$. (That is, suppose such $nu^-$ exists.) Note that cycle~$nu^-$ will never
    change state after stage $s$, and so will impose the same restraint forever more. Cycle $nu$ must return
    infinitely often either to #state(1)
    (at which time either $concatone(alpha, (nu^-, 1))$ or $concatone(alpha, (nu^-, 2))$ will be accessible
     as appropriate to the state in which $nu^-$ finds itself,) or to
    state 4 (so that $concatone(alpha, (nu, 1))$ will be accessible.)
    If there is no such $nu^-$ then the respective cases find $concatone(alpha, -1)$ and $concatone(alpha, (nu, 1))$
    accessible.

    If $|alpha|$ is odd then the argument similar, simpler, and omitted.
]

This establishes part 1 of the Proposition for $n = eta$ and we may assume that there is a value, $epsilon$, for $f(eta)$.  We write
this value variously as $epsilon = (nu_eta, i_eta)$ (for some $nu_eta in omega^2$ and $i_eta in {1, 2}$, if $|alpha|$ is even),
$epsilon = nu_eta$ (if $|alpha|$ is odd), or $epsilon = -1$ (if appropriate.) If there is a cycle of
strategy $alpha$ which acts infinitely often then we denote the leftmost one by $nu^+$.

It will be convenient to make the following definition. If $|alpha|$ is even and $i = 1$, or 2, then
we say that cycle $nu$ of strategy $alpha$ is _lacking for $i$ at stage~$s$_ if, at that stage,
cycle $nu$ imposes less restraint than is indicated by an outcome of $(nu, i)$. That is, if $i = 1$
and $nu$ imposes no restraint at stage $s$, or if $i = 2$ and $nu$ imposes only the restraints
$restr(A, u)$ and $restr(B, u)$. If $|alpha|$ is odd then we say that cycle $nu$ is _lacking_ at stage~$s$
if it imposed no restraint at that stage.

#lemma[
    Suppose that $nu_eta$ is defined. If $|alpha|$ is even then $nu_eta$ is lacking for $i_eta$ at only finitely many stages.
    If $|alpha|$ is odd then $nu_eta$ is lacking at only finitely many stages.
    <lemma2.20>
]
#proof[
    If $alpha$ acts only finitely then the result is trivial.

    Otherwise, by #lemmaRef(<lemma2.17>) $nu^+$ is defined, and $nu^+ geq nu_eta$. Thus, by #lemmaRef(<lemma2.18>) we
    may choose $s > s_0$ so large that no $alpha$-cycle to the left of $nu_eta$ acts after stage~$s$.

    We first give the argument for $|alpha|$ even. Cycle~$nu_eta$ can be lacking at infinitely many stages after $s$ in
    two ways.

    #show: doc => setupenum(doc, formats: ("1.",))
    + $i_eta = 1$ and $nu_eta$ returns infinitely often to #state(1).

     But in this case, either $concatone(alpha, nu_eta^-)$ is accessible infinitely often
     (if there is such a $nu_eta^-$ as defined in the proof #lemmaRef(<lemma2.19>),) or $concatone(alpha, -1)$
     is accessible infinitely often. Both of these contradict the definition of $nu_eta$.

    + $i_eta = 2$ and $nu_eta$ is infinitely often in a state numbered less than 4.

     Once cycle $nu_eta$ reaches #state(4) it can only return to a lower numbered state by being reset.
     But by defintion this cycle is not reset after state~$s$, so the only way it can infinitely often
     be in a state numbered less than 4 is if it never reaches #state(4). This contradicts the definition of $i_eta$.

    In the case $|alpha| = 2e + 1$ the argument is again similar and simpler.
]

#lemma[
    $restr(f, (eta + 1)) = concatone(alpha, epsilon)$ is cancelled only finitely often.
    <lemma2.21>
]
#proof[
    If $alpha$ acts only finitely, then $concatone(alpha, epsilon)$ is certainly not
    cancelled after the last time any cycle of stretegy $alpha$ acts.

    Otherwise, we note that by assumption $alpha$ is cancelled only finitely often, so
    ofter stage $s_0$, $concatone(alpha, -1)$ is never cancelled. For other possible
    values of $epsilon$, $concatone(alpha, epsilon)$ is cancelled only when

    #show: doc => setupenum(doc, formats: ("1.",))
    + cycle $nu_eta$ is lacking for $i_eta$ (or just lacking, if $|alpha|$ is odd); or

    + cycle $nu_eta$ of strategy $|alpha|$ enumerates something into or out of $A$,
      or something into $B$.

    By #lemmaRef(<lemma2.20>) cancellations of the first kind happen only finitely often.

    We claim also that cancellations of the second kind can happen only finitely often.
    By #lemmaRef(<lemma2.20>) choose $s > s_0$ so large that $nu_eta$ is not lacking for $i_eta$
    (or just lacking) after stage~$s$. In particular, cycle $nu_eta$ is not reset after stage~$s$,
    as in being reset it would (temporarily) be lacking. Thus $eta_nu$ works only with its final witness, $x$ (resp.~$y$),
    after $s$. But the worst $nu_eta$ can now do is ennumerate $x$ into $A$ and out again (or into $B$) once.

    Thus $concatone(alpha, epsilon)$ is cancelled only finitely often.
]

This establishes part 2 of the Proposition for $n = eta$.

#lemma[
    Strategy $alpha$ satisfies the requirement towards which it was working.
    <lemma2.22>
]
#proof[
    By Lemmas #thmref(<lemma2.17>), #thmref(<lemma2.18>), and #thmref(<lemma2.21>) we have just two possibilities.

    #show: doc => setupenum(doc, formats: ("1.",))
    + Only finitely often does any cycle of strategy $alpha$ act.

    + Either $epsilon neq -1$ and cycle $nu^+$ acts infinitely often, but is only reset finitely often,
      or $epsilon = -1$ and cycle $(0, 0)$ (resp. 0) returnes infinitely often to #state(1) (resp. #state(plabel(0))).

    We start with the argument for $|alpha| = 2e$.

    In the first case, some cycle gets permanently stuck in #state(1), #state(4), or #state(6). In any of these cases,
    we satisfy the requirement through a successful diagonalization.

    In the second case, let $sigma = nu^+$ if $epsilon neq -1$, and $sigma = (0,0)$ otherwise. Let $s > s_0$ be
    large enough that cycle~$sigma$ is not reset after stage~$s$, so that it works with the same witness, $x$, after~$s$.
    The only way that cycle $sigma$ can act infinitely often is if it alternates infinitely
    between states~1 and~2, or (if $epsilon neq -1$) between states~4 and~5. This implies that at least one of
    $Phi_e(E_e)$ and $hat(Psi)_e(C join A join B)$ is partial.

    Indeed, suppose that both functions are total and that we bounce infinitely often between #state(1) and #state(2).
    Let $t > s$ be so large that
    $(Phi_e(E_e; x))[t] converge$,
    $restr(E_(e,t), phi_t(x)) = restr(E_e, phi_t(x)) = (restr(hat(Psi)_e(C join A join B), phi_t(x)))[t]$,
    and each of $C$, $A$, and $B$ have reached their final values on the use of the $hat(Psi)_e(C join A join B)$ computations.
    Then there is no way that a $C$-change will ever subsequently cause cycle $sigma$ to jump from #state(2) back to #state(1).
    The case in which $epsilon neq -1$ and $sigma$ alternates infinitely between states~4 and~5 is the same.

    If $|alpha| = 2e + 1$, finite action again leads to success through diagonalization. The only way that
    cycle~$nu^+$ can act infinitely often is if it alternates infinitely often between states~#plabel(1)
    and~#plabel(2). We argue as above that in this case $Xi_e(C join A)$ is partial.
]

This establishes part 3 of the Proposition for $n = eta$.

Naturally, #lemmaRef(<lemma2.22>) describes what "really" happens to strategy $alpha$: the construction
of $Gamma_j$ and $Delta$ is only a threat to ensure that we get $G$ changes when we need them, and not too
many $C$-changes. If $Phi(E)$ and $Psi(C join A join B)$ are both total, then we actually win by diagonalization.
If not, we track down a witness to the partialness.

#lemma[
    For all sufficiently large $C$-true stages $t$, $restr(f, (eta + 1)) = concatone(alpha, epsilon) subset f_t$.
    <lemma2.23>
]
#proof[
    Again we start with the case $alpha = 2e$.

    First suppose that $alpha$ acts finitely. Let $q > s_0$ be so large that no cycle of $alpha$ acts after stage~$q$.

    Then $concatone(alpha, epsilon) subset f_t$ whenever $alpha$ is accessible, provided that also $t > q$.
    But $alpha subset f_t$ at every $C$-true stage $t$ after $s_0$.

    Now suppose that $alpha$ acts infinitely, and that $alpha$'s cycle $nu^+$ jumps infinitely often between
    states~1 and~2. By #lemmaRef(<lemma2.18>) we may choose $q > s_0$ so that no cycle $(j, k) < nu_eta$ acts
    after stage $q$, and cycle $nu_eta$ is not in #state(0) at $q$. Notice that, since cycle~$nu_eta$ is not
    reset after stage $q$, it can never advance past #state(2), for otherwise nothing could ever cause
    it to return to #state(1).

    Now, if $nu^+$ remains in #state(2) at a $C$-true stage $t > q$ then it will never never subsequently
    see a change in $restr(C, u)$. (We use $hat(Psi)$ instead of just $Psi$ in the definition of $Eq(x, s_1)$
                                    for just this purpose.)
    But this means that $nu^+$ will never return to #state(1). So, as $nu^+$ doesn't advance past
    #state(2), and doesn't get reset (and hence returned to #state(0)) after $q$, $nu^+$
    must be in #state(1) at stage~$t$. But $nu^+$'s being in #state(1) implies that $nu_eta = (nu^+)^-$ (if any)
    is rightmost in imposing restraint, and $concatone(alpha, epsilon) subset f_t$.
    If there is no cycle to left of $nu^+$ imposing restraint after $q$ then $epsilon = -1$ and
    $concatone(alpha, -1) subset f_t$.

    If $nu^+$ jumps between states~4 and~5 then a similar argument shows that $nu^+$ is in #state(4) at
    every $C$-true stage $t > q$. But in this case $nu^+ = nu_eta$ and $i_eta = 1$, so at such
    stages~$t$, $concatone(alpha, epsilon) = concatone(alpha, (nu_eta, i_eta)) subset f_t$.

    The case for $|alpha| = 2e + 1$ is essentially identical, and is omitted.

    The lemma is proved.
]

This establishes the last part of the Proposition for $n = eta$ and the inductive step is complete.
#thmref(<prop2.16>)[Proposition] is proved. #qed

Thus all the requirements are satisfied, and we have constructed $D = C join A$ and $F = C join A join B$,
d.r.e.~sets forming a proper interval $turinginterval(D, F) subset turinginterval(C, zerojump)$ free of r.e.~degrees.
It remains to show that there is enough permitting in the construction to ensure that $F leqt G$.

We follow the method and notation of~@LaForte. For $alpha in T$ we let
$
e^alpha = max({j, k st (exists beta in T)[concatone(beta, (j, k)) subset alpha]} union {k st (exists beta in T)[concatone(beta, k) subset alpha]})
$
the largest number which occurs in the path leading to $alpha$. We also define
$
s^alpha = min{s st restr(G_s, e^alpha) = restr(G, e^alpha)}.
$
(Note that the function $lambda alpha[s^alpha]$ is $G$-recursive.) The point is that none of the cycles
(of the strategies) leading to $alpha$ will ever see any of the $G$-changes they are looking for
after stage $s^alpha$.

The following two lemmas are technical, but basically say that if $t > s^alpha$ is a $C$-true stage,
then either strategy $alpha$ is accessible at stage~$t$, or is cancelled before ever being accessible
again. This allows us to get a handle on the delayed permitting nature of the argument.

#lemma[
    Suppose that $t > s^(concatone(alpha, nu))$ is a $C$-true stage, and that $alpha$'s cycle $nu$ is in a state
    other than 0, 1, and~4 (if $|alpha|$ is even), or a state other than #plabel(0) and~#plabel(1) (if $|alpha|$ is odd).
    Then if cycle $nu$ does not act at stage $t$ it will never act subsequently without first being reset.
    <lemma2.24>
]
#proof[
    We consider the case $|alpha| = 2e$. The case $|alpha| = 2e + 1$ is much the same, and simpler, as we don't have to worry
    about the parameter,~$mu$.

    We immediately dispense with the case in which $nu$ is in #state(7) or #state(8) at stage~$t$, as by construction such
    a cycle needs to be reset to act again. Thus $nu$ is in #state(2), 3, 5, or~6.

    Since $t$ is $C$-true, $nu$'s failure to act at $t$ due to a $C$-change
    (so as to make a state-transition #trans(2, 1), #trans(3, 4), #trans(5, 4), or #trans(6, 7))
    means that such action is also impossible in the future.
    Also, $t > s^(concatone(alpha, nu))$, so (writing $nu = (j,k)$), ${j, k} sect G = {j, k} sect G_t$,
    and so by stage~$t$ cycle~$nu$ will have seen all of the explicit $G$-permission it will ever see.
    Finally, if $nu$ makes the trasition #trans(2, 3) at stage~$t$, then the value of $mu$ just calculated
    is based on some computations in some cycle to the right, and these computations will never be subsequently injuired by
    a $C$-change, as $t$ is $C$-true. Thus cycle $nu$ will be stuck in #state(3) until it is reset.

    The upshot of all of this is that by not acting at $t$, cycle $nu$ has demonstrated that it is unable
    ever subsequently to act without first being reset.
]

#lemma[
    Suppose that $alpha subset f_s$, $t > max{s, s^alpha}$ is $C$-true, and $s' > t$. Then for $beta subset alpha$,
    if $beta subset.not f_t$ but $beta subset f_(s')$ then there is a $tau in (s, s']$ such that $beta$ is cancelled
    at stage~$tau$.
    <lemma2.25>
]
#proof[
    We proceed by induction on the length of $beta subset alpha$. As $emptyset$ is always accessible we assume the
    result for $beta$ and first consider $beta^+ = concat(beta, nu) subset alpha$. So assume
    $beta^+ subset f_(s')$ but $beta^+ subset.not f_t$. If also $beta subset.not f_t$ then by the inductive
    hypothesis $beta$ is cancelled at some stage in $(s, s']$ which leads to $beta^+$ being cancelled as well. So
    it suffices to assume that $beta subset f_t$ and that $beta$ is never cancelled in $(s, s']$.

    Suppose cycle~$nu$ of strategy $beta$ is reset at some $tau in (s, s']$. As $beta$ isn't cancelled at $tau$,
    $nu$ is reset by some the action at $tau$ of some cycle $nu' < nu$ of strategy $beta$. By construction,
    this leads to the cancellation of node $beta^+$.

    (In what follows it will be convenient to refer to a cycle which is not in #state(0) or #state(plabel(0))
     as _awake_. Cycles in #state(0) or #state(plabel(0)) are _asleep_.)

    So it remains to consider the case in which $nu$ is not reset at any $tau in (s, s']$. The following
    argument applies necessarily to the case $|alpha| = 2e$. The case $|alpha| = 2e + 1$ is much the same;
    and simpler, as do not have to worry about the parameter~$mu$.

    Write $nu = (j, k)$. $beta^+ = concatone(beta, nu) subset f_s$, so cycle $nu$ is awake at stage $s$.
    As it is not reset in $(s, s']$ it remains awake during this period, and in particular is awake at
    stage~$t$. But $beta^+ subset.not f_t$, so some cycle to the right of $nu$ must also be awake at $t$.
    This means that $(j, k)$ must be in one of the states 2, 3, 5, 7, and~8 by the Pattern Lemma.
    Now, $t > s^alpha geq s^(beta^+)$, so we may apply #lemmaRef(<lemma2.24>) to see that cycle~$nu$
    does not act before being first reset. As it is not reset in $(s, s']$, it cannot act at or before $s'$,
    and $concatone(beta, (j, k)) subset.not f_(s')$, a contradiction.

    If, instead, $beta^+ = concatone(beta, -1) subset alpha$, assume that $beta^+ subset.not f_t$. This means
    that, at stage $t$, some (leftmost) cycle~$chi$ of strategy~$beta$ is imposing restraint $r$. As $t$
    is $C$-true this restraint is based on computations which will never be injured by a later $C$-change.
    Thus $chi$ will always impose at least $r$-much restraint unless strategy~$beta$ (and hence strategy $beta^+$)
    is cancelled. Thus, if $beta^+ subset f_(s')$ then strategy~$beta^+$ is cancelled by stage~$s'$.
]

Now we can show that the permitting works.

#lemma[
    $A join B leqt G$.
    <lemma2.26>
]
#proof[
    Let $x in omega$. If $x$ is not chosen as a witness by stage~$x$ then it never will be, and $x in.not A union B$.
    Otherwise, suppose $x$ is chosen at stage $s_0$ to be the witness for a cycle $nu = (j,k)$ of strategy~$alpha$
    of even length. Note that $alpha subset f_(s_0)$, and that $x in.not B$.

    If $k in.not G$ or $G_(s_0)(k) = 1$ then $alpha$'s cycle~$nu$ will never get the first permission that it needs,
    and $x in.not A$.

    Suppose now that $k in setdiff(G_s, G_(s-1))$. Let $t$ be the first $C$-true stage larger than each of
    $s$, $s_0$, and $s^(concatone(alpha, nu))$. We claim that if $x$ is not enumerated into $A$ by stage $t$
    it never will be. Well, if $alpha subset.not f_t$ then by #lemmaRef(<lemma2.25>) strategy~$alpha$ will be
    cancelled (and witness $x$ forgotten) before $alpha$ gets a chance to act again. So if $x$ hasn't entered $A$
    before~$t$, we must have $alpha subset f_t$ if $x$ is ever to have a chance. If some cycle $(j', k') < nu$
    of strategy~$alpha$ acts at $t$ then cycle~$nu$ will be reset, and its witness forgotten. Otherwise, if cycle $nu$
    acts at or after stage~$t$ due only to $Eq(x, s_1)$ holding, then certainly $x in.not A$, as by construction
    cycle~$(j,k)$ will jump straight to #state(7) rather than attempt to enumerate $x$ into $A$. If $nu$ is in #state(4)
    at stage~$t$ then $x$ would have already entered $A$.  So we may assume that cycle~$nu$ is in a state
    other than 0, 1, and~4 at stage~$t$, and by #lemmaRef(<lemma2.24>) is unable ever to act again without getting
    reset first.

    So if $x in.not A_t$, $x in.not A$.

    If $x in A_t$ we must check to see if $x$ ever gets removed from $A$. If $j in.not G$ then cycle $nu$ will never
    see the necessary permission, and $x in A$. Otherwise, let $j in setdiff(G_w, G_(w-1))$. Let $t'$ be the first
    $C$-true stage greater than both $t > s^(concatone(alpha, nu))$ and $w$. The same reasoning as before
    shows that $x$ will have been removed from $A$ by stage $w$ if it ever will be.

    Thus $A(x) = A_w(x)$.

    If $x$ is chosen at $s_0$ to be a witness for cycke $k$ of strategy $alpha$ of _odd_ length then the same
    basic argument applies, but now we need not worry about $x$ being enumerated out of $B$: we just check if it
    ever gets enumerated in.

    All of the above can be done by asking questions of a $C$ oracle and a $G$ oracle. As $C ltt G$, a $G$ oracle
    suffices, and $A join B leqt G$.
]


////////////////////////////////////////
// Chapter 3

= Avoiding $n$-r.e. degrees with dREA sets <chapter3>

== Introduction

Soare and Stob prove (see @SoareStob1982)
#theorem[
    Given a nonrecursive, r.e. set $G$ there is an $reInAbove(G)$ set $F$ not of r.e. degree.
    <theorem3.1>
]

A question arises: what other sorts of degrees can we avoid in this way? For example, can
we always construct $F$ to be not of d.r.e. degree? The answer is no:
#theorem(name: [Arslanov, LaForte, and Slaman; @ALS1998])[
    There exists an r.e. set $G ident.not_T emptyset$ such that every $reInAbove(G)$ set $F$ is of d.r.e. degree.
    <theorem3.2>
]

The question is then how we might relax the requirements on the construction of $F$. Rather than work with a
fixed "base" set $G$, Jockusch and Shore consider what happens if the choice of r.e.~$G$ is completely
free (see @JockuschShore1984[Thm1.6a]). That is, $F$ is required only to be 2-REA, _i.e._ $reInAbove(G)$ for
_some_ r.e. set~$G$, which we are free to construct:
#theorem(name: [Jockusch and Shore])[
    Let $A_0, A_1, dots$ be uniformly recursive in $zerojump$. Then there is a 2-REA set $F leqt zerojump$
    such that for all $i geq 0$, $F ident.not A_i$.
    <theorem3.3>
]
Here "uniformly recursive in $zerojump$" means that there is a $zerojump$-recursive function $f$ such that
$A_i(x) = f(i, x)$ for all $i$ and $x$. This is an important result, as many interesting families of
sets are uniformly recursive in~$zerojump$. Examples are the $n$-r.e. sets, for each $n$, and the union
over $n$ of these families. So we immediately have
#theorem(name: [Jockusch and Shore])[
    For each $n$, there is a 2-REA set $F_n leqt zerojump$ not of $n$-r.e. degree. In fact, there is a single 2-REA
    set $F leqt zerojump$ which fails to be of $n$-r.e. degree for any $n geq 0$.
    <theorem3.4>
]

Rather than give up control over $G$ we will give up some rigor in the way $F$ is enumerated from $G$. When
constructing $F$ to be $dreInAbove(G)$ the following result is obtained.
#theorem(name: [Cholak and Hinman; @CholakHinman])[
    Given any nonrecursive, r.e. set $G$ there is $dreInAbove(G)$ set $F$ not of d.r.e. degree.
    <theorem3.5>
]
This result has been strengthened by Hinman, @Hinman:
#theorem[
    Given a nonrecursive, r.e. set $G$ there is $dreInAbove(G)$ set $F$ not of 3-r.e. degree.
    <theorem3.6>
]

Can we avoid 4-r.e. degrees _via_ $dreInAbove(G)$ sets in this way? $n$-r.e. degrees in general?
We cannot answer this question at the moment. However, if we drop the requirement that
the constructed set be Turing-above $G$, we can avoid $n$-r.e. degrees, and at the same time
place the "base set" $G$ (which we now call $D$) in a prescribed r.e.~interval.
#theorem[
    For any $n in omega$ and any r.e.sets $C ltt G$ there is r.e. $D in turinginterval(C, G)$
    and $dreInAbove(D)$ $F$ such that $F$ is not of $n$-r.e. degree.
    <theorem3.7>
]
Note that $D leqt F$, but we do not know whether or not we can ensure $G leqt F$.

This result is in some sense a middle point between Theorems~#thmref(<theorem3.1>) and~#thmref(<theorem3.4>).
We maintain some control over the base set by allowing more flexiibility in the construction of $F$ from it.


== The construction for the case $n = 4$ <section3.2>

#let udvd = $setdiff(U^D, V^D)$

We start by giving a proof for the case $n = 4$. In @section3.4 we comment on the changes needed for larger
values of $n$.

We will construct $D = C join A leqt G$ and $F = C join A join (udvd)$ with the required
properties. We must meet all of the requirements
$
R_e: quad udvd neq Phi_e(E_e) thick or thick E_e neq Psi_e(C join A join (udvd))
$
in which ${angletup(E_e, Phi_e, Psi_e)}_(e geq 0)$ enumerates all triples in which $E_e$ is a 4-r.e. set and
$Phi_e$ and $Psi_e$ are recursive functionals. We will ensure that $D leqt G$ by direct permitting. As in
#chapRef(2) this permitting is delayed, as there will be "gaps" in the stages at which any particular strategy
is accessible. It will be convenient to enumerate elements into $U^(C join A)$ and $V^(C join A)$ with
separate $C$- and $A$-uses. Thus we will actually be enumerating into r.e. sets $U$ and $V$ axioms
of the form $angletup(x, Z_1, Z_2)$, where are $Z_1$ and $Z_2$ are finite sets thought of as
initial segments (correct at some stage $s$) of $C$ and $A$ respectively.

Where the structure $D = C join A$ of $D$ is important, we will write it out in full.
In other places we will just use $D$.


=== The basic module <section3.2.1>

The construction used to satisfy the requirements is (loosely) based on the basic module given in @CLW1989.
It is similar to the module in #chapRef(2). The strategy for a single requirement consists of a
(potentially unbounded) number of cycles, each of which makes a very simplistic attempt
to satisfy the requirement. We argue that if no cycle succeeds then we have $G leqt C$, a contradiction.

So, fix $e in omega$. We desribe the strategy for satisfying requirement $R_e$. To simplify notation
we write $angletup(R, Phi, Psi)$ for $angletup(E_e, Phi_e, Psi_e)$.

In #chapRef(2) we avoided an r.e.~opponent by changing our constructed set twice. When avoiding
a 4-r.e. set we must change our set 5 times. This is not as bad as it seems as we have sweeping
powers over the set, $F$, we construct. Firstly, $F$ is (the join of an r.e.~set with) the difference
of two r.e.[$D$] sets, and membership of individual numbers in such sets may change
many times during a construction due to changes in $D$. Furthermore, $D = C join A$ and we have complete control
over $A$. This will allow us to eject elements from $udvd$ with great flexibility.

Now, as we wish to ensure $A leqt G$ we must ask for $G$-permission each time we put an element into~$A$.
It turns out that in the $n = 4$ case we must do this twice, which leads to a two dimensional cycle layout, as in #chapRef(2).

Thus, the strategy consts of an $(omega^2)$-sequence of cycles ordered lexicographically. Cycle $(0,0)$ starts first.
Cycle $chi = (j, k)$ may start $(j, k+1)$ and $(j+1, 0)$ as well as stopping all cycles $> chi$.
Cycle $chi$ may define the values $Gamma_j(C; k)$ and $Delta(C\; j)$.
Again we refer to rows of cycles, $R_j = {(j,k) st k in omega}$.

Cycles may declare various numbers to be _levers_. These are used when we want to remove some some element, $x$, from $V^D$.
When $x$ is enumerated into $V^D$ we choose some new large element, $lambda$, not already a member of $D$
(actually, not a member of $A$, over which we have control) and put $x$ into $V^D$ with an $A$-use that is larger than $lambda$.
When it comes to remove $x$ from $V^D$ we "pull the lever": we enumerate $lambda$ into $A$, thus ejecting $x$ from $V^D$.

Each cycle begins in #state(0). A cycle is _started_ by letting it pass from #state(0) to another state,
as determined by its history in much the same way as in #chapRef(2); we have the same cascading effect.
A cycle is reset by putting it back into #state(0), returning its restraints to 0 and undefining its
parameters $x, u, tilde(u), v, tilde(v), lambda^1(x)$, and $lambda^2(x)$.
A cycle is _abandoned_ by returing its restraints to 0 and stopping all activity for that cycle. This is done in much
the same situations as in #chapRef(2): a cycle has failed to satisfy $R_e$.
A cycle is said to _act_ whenever it moves from one state to another, _except_ in the case of the bookkeeping
transition from #state(4) to #state(5).

Cycle $chi = (j, k)$ proceeds as follows.

#show: doc => setupenum(doc, formats: ("1.", "(i)",))
0. Until given the go-ahead, do nothing. When told to start, if $k=0$ or row $R_j$ has previously been abandoned _in toto_,
   advance directly to #state(11) and follow the instructions there. Otherwise, check if cycle $chi$ has been abanonded
   in the past. In this case jump straight to #state(10) and follow the instruction there. Otherwise, choose a witness~$x$,
   larger than any number mentioned in the construction so far, including all currently defined $(udvd)$-restraints,
   and larger than both $j$ and~$k$. Advance to #state(1).

+ Let $Eq(x, s)$ denote the condition
  $
    ((udvd)(x))[s] = (Phi(E\, x))[s] #h(1fr) \ #h(1fr)
      and (restr(E, phi(x)))[s] = (restr(hat(Psi)(C join A join (udvd)), phi(x)))[s].
  $

  Wait for a stage $s_1$ at which $Eq(x, s_1)$ holds. There are two kinds of computation use we must consider.
  The first is $u = (hat(psi) phi(x))[s_1]$, the total (direct) use of the
  $hat(Psi)(C join A join udvd)$ computations. Also implied here are the $C$- and $A$-uses
  needed to enumerate that part of $setdiff(U^(C join A), V^(C join A))$ used in the computation. So, we defined
  $
  tilde(u) = max({eta_C^U(x), eta_A^U(x) st x in restr(U^(C join A), u)} union
                 {eta_C^V(x), eta_A^V(x) st x in restr(V^(C join A), u)})
  $

  where $eta_C^U(x)$ is the $C$-use of the axiom which witnesses the membership of $x$ in $U^(C join A)$,
  and the other terms are defined analogously. The point is that a $C$- or $A$-change below $tilde(u)$
  and hence destroy the important computations. Conversely, the definition ensures that a
  change in $restr((udvd), u)$ is accompanied (nay, caused!) by a change in $restr(C, tilde(u))$
  or $restr(A, tilde(u))$. We restrain $restr((udvd), u)$ and $restr(A, tilde(u))$,
  enumerate $x$ into $U^(C join A)$ with $C$-use $tilde(u)$ and $A$-use~0, and advance to #state(2).

  [Note that if $s_1$ does not exist then $x$ is already a witness to the success of our strategy.
   The same comment applies to $s_2, dots, s_5$ below.]

+ Wait for a stage $s_2$ at which either
  + $restr(C_(s_2), tilde(u)) neq restr(C_(s_1), tilde(u))$; or
  + $restr(C_(s_2), tilde(u)) = restr(C_(s_1), tilde(u))$, $Eq(x, s_2)$ holds.

  If (i) occurs then return to #state(1), setting the (udvd)- and $A$-restraints back to~0.
  Note that the change in $C$ automatically ejhects the witness $x$ from $U^D$.

  If we have (ii) let $v = (hat(psi)phi(x))[s_2] > u$, the total use of the
  $hat(Psi(C join A join udvd))$ computations at stage~$s_2$, and define $tilde(v) > tilde(u)$ analogously
  to~$tilde(u)$. Note that because of the enumeration at #state(1) info $(udvd)$ we have
  $(Phi(E\; x))[s_2] = 1 neq 0 = (Phi(E\; x))[s_1]$, so that $restr(E_(s_2), phi_(s_1)(x)) neq restr(E_(s_1), phi_(s_1)(x))$.
  Also note that by reaching this point we still have $restr(C_(s_2), tilde(u)) = restr(C_(s_1), tilde(u))$.

  We set
  $
    lambda^1(x) = (min lambda)[lambda > tilde(v) and lambda > l and lambda > s_2 and lambda in.not A_(s_2) \
                               and lambda "is larger than any number mentioned in the construction so far"].
  $
  Declare $lambda^1(x)$ to be a lever, restrain $restr((udvd), v)$ and $restr(A, lambda^1(x) + 1)$, and enumerate
  $x$ into $V^(C join A)$ with $C$-use $tilde(v)$ and $A$-use $lambda^1(x) + 1$.

  Note that now, since we have just removed $x$ from $udvd$, we have
  $
    (restr((C join A join (udvd)), u))[s_2 + 1] = (restr((C join A join (udvd)), u))[s_1].
  $

  Advance to #state(3).

+ Wait for a stage $s_3$ at which either
  + $restr(C_(s_3), tilde(u)) neq restr(C_(s_1), tilde(u))$;
  + $restr(C_(s_3), tilde(u)) = restr(C_(s_1), tilde(u))$ but $restr(C_(s_3), tilde(v)) neq restr(C_(s_2), tilde(v))$; or
  + we see no appropriate $C$-change, $Eq(x, s_3)$ holds.

  In case (i), return to #state(1), setting the cycle's restraints back to 0.
  In case (ii), return to #state(2), setting the $udvd$ restraint to $u$, and the $A$-restraint to $tilde(u)$.
  In either of these cases we also discard our choice of the lever, $lambda^1(x)$.
  Note that in case~(i) (resp.~(ii)), $x$ has been ejected from both $U^D$ and $V^D$ (resp. from $V^D$)
  by the change in $C$.

  In case (iii) we have $restr(E_(s_3), phi_(s_1)(x)) = restr(E_(s_1), phi_(s_1)(x))$, so there is a
  $y < phi_(s_1)(x)$ such that $E_(s_3)(y) = E_(s_1)(y) neq E_(s_2)(y)$. Thus $E$ has changed (at least)
  twice on $y$ so far. Fix this $y$ in subsequenct discussion.

  We wish to continue our tactic of reacting to changes in $E$ by changing $(udvd)(x)$.
  The witness $x$ is already in both of $U^D$ and $V^D$, so to get it back into the difference
  we must remove it from $V^D$. We have a mechanism for doing this: pulling the lever $lambda^1(x)$.
  However, enumerating $lambda^1(x)$ into $A$ means asking for $G$-permission. We do this now.

  If $G_(s_3)(k) = 1$ we have no hope of getting the $G$-change we rely on; jump straight
  to #state(10) and follow the instructions there.

  Otherwise we prepare to wait for $G(k)$ to change to get the permission we need.
  Define $Gamma_j(C; k) = G_(s_3)(k) thin (=0)$ with use $tilde(v)$ and start cycle $(j, k+1)$ to run
  simultaneously. Advance to #state(4).

+ Wait for a stage $t_1$ at which either
  + $restr(C_(t_1), tilde(u)) neq restr(C_(s_1), tilde(u))$;
  + $restr(C_(t_1), tilde(u)) = restr(C_(s_1), tilde(u))$ but $restr(C_(t_1), tilde(v)) neq restr(C_(s_2), tilde(v))$; or
  + $G_(t_1)(k) neq G_(s_3)(k)$.

  In cases (i) and (ii) we reset all the cycles $> (j, k)$ behave as we did in #state(3), returning to #state(1)
  or #state(2) as appropriate. We also declare $lambda^1(x)$ not to be a lever any more.

  In case (iii) we have two subcases, just as in #state(2) of the strategy in #chapRef(2):
  #[
    #show: doc => setupenum(doc, formats: ("1.", "(a)",))
    + If some cycle $chi'$ of row $row(j)$ is currently in #state(8) or #state(9)
      (as in #chapRef(2) there will be at most one such cycle) we set the marker $mu(x) = tilde(v)_(t_1)(chi')$
      and advance to #state(5). This transition does not count as an action.
    + Otherwise no such $chi'$ exists and we reset all cycles $> chi$, enumerate $lambda^1(x)$ into $A$
      (so that $x$ re-enters $udvd$) and advance to #state(6).
  ]

+ Wait for a stage $t_2$ such that either

  + $restr(C_(t_2), tilde(u)) neq restr(C_(s_1), tilde(u))$;
  + $restr(C_(t_2), tilde(u)) = restr(C_(s_1), tilde(u))$ but $restr(C_(t_2), tilde(v)) neq restr(C_(s_2), tilde(v))$; or
  + $restr(C_(t_2), tilde(v)) = restr(C_(s_2), tilde(v))$ but $restr(C_(t_2), mu(x)) neq restr(C_(t_1), mu(x))$.

  In cases (i) and (ii) we behave as we did in #state(3).

  In case (iii) reset all cycles $> chi$, enumerate $lambda^1(x)$ into $A$ and advance to #state(6).

+ [Once we reach this point, any subsequent change in $restr(C, tilde(v))$ from its shape at stage~$s_2$
   is disastrous to our underlying computations. By taking advantage of the change in $G(k)$ to enumerate
   our lever we have passed the point of no return and cannot cope with a $C$-change by going back to
   #state(1) or #state(2). However, as in #chapRef(2) such a $C$-change gives us the small victory
   of a correct definition of the value $Gamma_j(C; k)$. So, if we ever subsequently see such
   a change in $restr(C, tilde(v))$, reset all cycles $> chi$ and jump straight to #state(10).
   This instruction is implicit in all the states that follow, up to #state(10) itself.]

  Wait for a stage $s_4$ such that $Eq(x, s_4)$ holds. Now, since
  $
    (restr((C join A join (udvd)), v))[s_4] = (restr((C join A join (udvd)), v))[s_2]
  $
  we must have that $restr(E_(s_4), phi_(s_1)(x)) = restr(E_(s_2), phi_(s_1)(x))$.
  Thus $E_(s_4)(y) = E_(s_2)(y) neq E_(s_3)(y)$ = $E_(s_1)(y)$ and $E$ has now changed 3~times on $y$.

  We prepare to enumerate $x$ back into $V^D$ by defining another lever:
  $
    lambda^2(x) = (min lambda)[lambda > tilde(v) and lambda > j and lambda > s_4 and lambda in.not A_(s_4) \
                               and lambda "is larger than any number mentioned in the construction so far"].
  $
  Declare $lambda^2(x)$ to be a lever and restrain $restr(A, lambda^2(x) + 1)$.
  (The restraint $restr((udvd), v)$ is still in place from before.)
  Enumerate $x$ into $V^(C join A)$ with $C$-use $tilde(v)$ and $A$-use $lambda^2(x) + 1$.
  This enumeration ensures that
  $
  (restr((C join A join (udvd)), u))[s_4 + 1] = (restr((C join A join (udvd)), u))[s_1].
  $
  Advance to #state(7).

+ Wait for a stage $s_5$ such that $Eq(x, s_5)$ holds. Now we have
  $restr(E_(s_5), phi_(s_1)(x)) = restr(E_(s_1), phi_(s_1)(x))$ so that
  $E_(s_5)(y) = E_(s_3)(y) = E_(s_1)(y) neq E_(s_4) = E_(s_2)$.
  $E$ has changed 4~times on $y$, and being 4-r.e. can't change again. We want
  to put $x$ back into $udvd$ to take advantage of the fact that $restr(E, phi_(s_1)(x))$
  can't return to its $s_2$ shape. This entails pulling the lever $lambda^2(x)$, which
  means asking for $G$-permission again.

  If $G_(s_5)(j) = 1$ already, jump straight to $state(11)$ and follow the instructions there.
  Otherwise set $Delta(C \; j) = G_(s_5)(j)$ with use $tilde(v)$, and start cycle $(j+1, 0)$
  to run simultaneously. Advance to #state(8).

+ Wait for a stage $t_3$ such that $G_(t_3)(j) neq G_(s_5)(j)$. Then reset all cycles to the right
  of $chi$, enumerate $lambda^2(x)$ into $A$, and advance to #state(9).

+ Wait for a stage $t_4$ such that $restr(C_(t_4), tilde(v)) neq restr(C_(s_2), tilde(v))$.
   (We make explicit the implicit instruction mentioned in #state(6).)
   If this happens, advance to #state(11).

  Otherwise $restr(C, tilde(v)) = restr(C_(s_2), tilde(v))$ and we satisfy the requirement because
  $E(y)$ cannot change any more:
  $
  restr(E, phi_(s_1)(x)) & neq (restr(E, phi_(s_1)(x)))[s_2] \
                         & = (restr(hat(Psi)(C join A join (udvd)), phi_(s_1)(x)))[s_2] \
                         & = restr(Psi(C join A join (udvd)), phi_(s_1)(x)).
  $

+ This state is analogous to #state(7) in #chapRef(2). If we arrive here it is safe and accurate
  to set $Gamma_j(C; k) = 1$ with use~0. Do so, unless it has already been done, (permanently)
  abandon cycle $(j, k)$ and start cycle $(j, k+1)$.

+ Arriving here means we can with confidence set $Delta(C\; j)$ with use~0.
  Do so, unless it has already been done, (permanently) abandon row $row(j)$ and start cycle $(j+1, 0)$.
  For technical reasons also reset every cycle in row $row(j)$ and put cycle $(j, 0)$ into #state(11).

=== Combining the modules

The basic modules are combined in much the same way as we used in #chapRef(2) with a tree.
However, there is a very important difference.

In #chapRef(2) a cycle could act infinitely often without being reset by bouncing back and forth
between states 1 and~2, or between states 4 and~5. It was important in that construction
that such infinite action was not accompanied by any enumerations into or out of the sets
under construction. The proof of #lemmaRef(<lemma2.21>) depended on this fact: after
a cycle is reset for the last time it can only cause finitely much enuemration.
In the preset construction, however, this is not true. A cycle returning infinitely often
to #state(1) (or to #state(2)) must infinitely often change the value of $(udvd)(x)$,
only to have it changed back again when a $C$-change causes the return to #state(1).
We need a way to deal with this.

In #chapRef(2) we used multiple outcomes for each cycle. We make use of them again, both
to remove the need for a path restraint, and to deal with the potentially infinite
changes in $(udvd)(x)$ mentioned above. For each cycle~$nu$ of the basic strategy
there are six fundamentally different situations at stage~$s$.
#[
#set align(center)
#tablex(
    columns: (1.3in,) * 4,
    rows: 3em,
    align: horizon + center,
    [$nu$'s state], [$x in (udvd)$?], [Restraint on \ $(udvd)$], [Restraint on $A$],
    $0, 1, 10, 11$, [doesn't\ matter], $0$,                     $0$,
    $2$,            [yes],            $u$,                     $tilde(u)$,
    $3, 4, 5$,      [no],             $v$,                     $(lambda^1(x) + 1)[s]$,
    $6$,            [yes],            $v$,                     $(lambda^1(x) + 1)[s]$,
    $7, 8$,         [no],             $v$,                     $(lambda^2(x) + 1)[s]$,
    $9$,            [yes],            $v$,                     $(lambda^2(x) + 1)[s]$
)
]
(The only state in the first row to which $nu$ can return infinitely often without
 being reset infinitely often is #state(1), and whenever $nu$ is in this state $x(nu) in.not (udvd)[s]$.
 This is why we have a "doesn't matter" in this row.)

We will have a separate outcome for each of these possibilities but the first. This first
possibility is dealt with, as in #chapRef(2), by using the rightmost cycle to the left which imposes restraint.

So let $Lambda = {-1} union (omega^2 times {1, 2, 3, 4, 5})$, ordered lexicographically with $-1$ coming first.  Now let $T =
finseq(Lambda)$ with the standard partial order $<_L$. As before, we make no distinction between a node of the tree and (instance of
the) strategy it is implementing. The node $alpha in T$ attempts to satisfy requirement $R_(|alpha|)$. A strategy is _cancelled_ by
resetting all of its cycles and discarding any functionals it may have partially defined. Any parameter of a strategy keeps its
assigned value until that value is redefined or undefined.

The construction proceeds as follows.

#stage-hdr(0) All strategies are cancelled.

#stage-hdr($s+1$) We defined, in substages $t < s$ a finite path $f_(s+1)$ through the tree, of length $s$.
Suppose $alpha = (restr(f_(s+1), t)) in T$ has been defined by substage $t-1$. If no cycle of strategy $alpha$ has been
started since $alpha$ was last cancelled then start $alpha$'s cycle $(0,0)$ and set $nextval = -1$.

Otherwise,let any cycles of stategy $alpha$ able to make the transition from #state(4) to #state(5) do so.
Let any cycle forced solely by a $C$-change to change state do so. There are now two cases
- #case(1) Some leftmost cycle $nu$ of strategy $alpha$ is able to act.

#let bigS = $sans(upright("S"))$
We allow cycle $nu$ to act. Let $lambda$ be the rightmost cycle of strategy $alpha$ now imposing restraint of some sort
(if there is such a cycle.) Let $lambda$ be in state~#bigS (note that $bigS neq 0, 1, 10, 11$) and let $i$ be defined by
$
i = cases(
    1 quad & "if" bigS = 2\,,
    2      & "if" bigS = 3\, 4 "or" 5\,,
    3      & "if" bigS = 6\,,
    4      & "if" bigS = 7 "or" 8\,,
    5      & "if" bigS = 9.
)
$
Now set $nextval = (nu, i)$. If there is no such cycle $lambda$ put $nextval = -1$.

In any case, cancel all strategies $beta$ with $concatone(alpha, nextval) <_L beta$.

- #case(2) No cycle of strategy $alpha$ is able to act.

We do nothing at this substage. Define $nextval$ just as above. There is nothing to cancel.

If $t + 1 < s$ we advance to substage $t+1$.

A node $alpha$ is _accessible_ at stage $s+1$ if $alpha subset f_(s+1)$.

One of the points of multiple outcomes for each cycle is to cope with the coming and going
of elements of $udvd$ as $C$ changes. It is important to observe that every time $concatone(alpha, (nu, i))$
($i = 1, 2, 3, 4, 5$) is accessible, $(udvd)(x(alpha, nu))$ is the same, where $x(alpha, nu)$ is the witness chosen by
cycle~$nu$ of strategy~$alpha$.

== Verification for $n = 4$ <section3.3>

At heart this construction is very like the one in #chapRef(2). We use the same mechanism
to avoid $Delta$-inconsistency, and the underlying aim is the same: change the constructed set
frequently enough that our opponent (previously an r.e.~set; here a 4-r.e.~set) cannot keep up with us.
As such, we would expect the verification to take alrgely the same tack. This is the case.

The verification argument given in #chapRef(2) is detailed#footnote[The less charitable reader may prefer another word.]
and it would please no-one to go through the same sort of thing again in its entirety. So, when an argument follows the
same lines as the corresponding discussion in #chapRef(2) we will just indicate the essential modifications, if any.

As in #chapRef(2), we will refer to parameters associated with cycle~$nu$ of strategy~$alpha$ as they are defined
at stage~$s$ like so: $u_s(alpha, nu)$, $lambda^1_s(alpha, x(nu))$.
Whenever it is made possible by context we will drop the strategy name.

=== Layout of the cycle states

We begin again with a description of the possible state-arrangements, and state a Pattern Lemma.
We assume we have a certain, fixed strategy~$alpha$ in mind, and all cycles mentioned are assumed to belong
to it. As before, we regard the stages mentioned as being the successive ones at which strategy~$alpha$
is accessible. Just as in #chapRef(2), we refer to a special "double state": a cycle in either #state(8)
or #state(9) is said to be "in state~8/9".

#lemma[
    For any row $row(j)$, at most one cycle $(j, k)$ of the row is in state~8/9.
    <lemma3.8>
]
#proof[As #lemmaRef(<lemma2.3>).]

#lemma[
    Suppose cycle $chi = (j, k)$ enters #state(5) at stage $s$ due to cycle $chi'$ being in state~8/9.
    If at stage $t > s$ cycle~$chi'$ leaves stage~8/9 for the first time after~$s$, for any reason, $chi$
    is no longer in #state(5) at the end of stage~$t$.
    <lemma3.9>
]
#proof[
We start by noting that $mu(x(chi)) = tilde(v)_s(chi') = tilde(v)_t(chi')$.
Now, cycle $chi'$ only leaves state~8/9 through acting or being reset. If $chi' < chi$ then
the action/resetting of $chi'$ also resets $chi$, by construction.
We consider the case $chi < chi'$. If cycle $chi'$ leaves state~8/9 without being reset
it must reach either #state(10) (if it sees a change in $restr(C, tilde(v)_t(chi'))$ while in #state(8));
or #state(11) (if that $C$-change is seen while in #state(9).)
In either case there is a change in $restr(C, mu(x(chi)))$, and cycle~$chi$ will change state,
or be reset by the action of a cycle to its left.

The case left to consider is that there is a third cycle, $chi dubpr$ with $chi < chi dubpr < chi'$,
which acts at stage~$t$.
To reach a contradiction we assume that this action is not accompanied by a change in $restr(C, tilde(v)_t(chi'))$.
Without loss of generality we may assume that $t$ is minimal in witnessing the failure of the lemma in this way.
Now, as cycle~$chi'$ is not in #state(0) at stage~$s$, cycle~$chi dubpr$ must be in one of the following
states at that time: 4, 5, or~10.
Cycle~$chi dubpr$ cannot change state between stages~$s$ and~$t$ (except for the transition~#trans(4,5))
as to do so would reset cycle~$chi'$, contradicting the definition of~$t$. We may discard the possibility
that $chi dubpr$ is in #state(10) at stage~$s$, as such a cycle can never act again without first
being reset. Cycle $chi dubpr$ can't make the transition~#trans(4,5) at stage~$t$, as such a transition
doesn't count as an action. The transitions~#trans(4,1), and~#trans(4,2), entail a change in $restr(C, tilde(v)_t(chi dubpr))$.
But $tilde(v)_t(chi dubpr) < tilde(v)_t(chi')$ since cycle~$chi'$ starts after $chi dubpr$ reaches #state(2)
and $tilde(v)_t(chi dubpr)$ is defined. Thus such a $C$-change is impossible.

Thus, the only possible transition left is~#trans(5,6). That this is impossible follows from the same
argument as was used for the #trans(3,4) transition in #chapRef(2).
]

#lemma[
    Given $j$, if cycles $chi, chi' in cal(S)_j$ are both in #state(5) at stage~$s$ then
    $(mu(x(chi)))[s] = (mu(x(chi')))[s]$.
    <lemma3.10>
]
#proof[
    As #lemmaRef(<lemma2.5>).
]

We are now ready to state the Pattern Lemma for this construction.

Let $X = {0, 1, dots, 11}$ and reacall that for sets $M, N$ of finite sequences
(of unspecified type) we set
$setconcat(M, N) = {concat(theta, sigma) | theta in M and sigma in N}$, and $angletup(M) = {angletup(theta) | theta in M}$.

The constructions being very similar, the set of valid patterns to be defined is all-but-isomorphic to that in #chapRef(2).

We define the following subsets of $finseq(X)$:
#let commabr = [\,\ ]
$
prelimCrampedRow &= setconcat(finseq({4, 5, 10}), angletup({8})) commabr
finalCrampedRow  &= setconcat(finseq({4, 5, 10}), angletup({9})) commabr
crampedRow       &= prelimCrampedRow union finalCrampedRow commabr
uncrampedRow     &= setconcat(finseq({4, 10}), angletup({1, 2, 3, 6, 7})) commabr
abandonedRow     &= angletup({11}) commabr
prelimRow        &= prelimCrampedRow union abandonedRow commabr
finalRow         &= finalCrampedRow union uncrampedRow\,
$
and a subset of $finseq((finseq(X)))$,
$
validPattern = setconcat(finseq(prelimRow), angletup(finalRow)).
$

As in #chapRef(2) we define by $pattern(s)(alpha)$ the cycle-state arrangement of the strategy~$alpha$ at stage~$s$.
We also refer to the cycle arrangements of individual slices as "patterns".

#lemma[
    If #strat($alpha$) has at least one cycle not in #state(0) at #stg($s$), $pattern(s) in validPattern$.
    <lemma3.11>
]
#proof[
    The arguments are very similar to those in the corresonding proof in #chapRef(2), and consist of an exhaustion of cases.
    The same follow-your-nose approach works just fine; nothing is to be gained by repeating it.
]

=== Consistency of the functions $Gamma_j(C)$ and $Delta(C)$

Now for the consistency of the constructed functions $Gamma_j(C)$ and $Delta(C)$.
The proofs need little beyond the corresponding ones in #chapRef(2). The only change necessary is typically
a slightly more involved exhaustion of possibilities brought about by the fact that each
cycle has five outcomes corresponding to it, rather than the two of the earlier chapter.

Again we assume that we have a specific strategy, $alpha$, in mind.

#lemma[
    If cycle~$(j,k)$ is in #state(8) at #stg($s$), then $(Delta(C\; j))[s] converge$.
    The same conclusion may be reached if #theRow($j$) was abandoned at some stage before~$s$.
    <lemma3.12>
]
#proof[
    As #lemmaRef(<lemma2.7>).
]

#lemma[
    If some cycle $chi = (j, k)$ acts at #stg($s$) to define $Delta(C\; j)$ then for each
    $i < j$, $(Delta(C\; i))[s] converge$.
    <lemma3.13>
]
#proof[
    As #lemmaRef(<lemma2.8>).
]

Similarly we have.
#lemma[
    If some cycle $chi = (j, k)$ acts at #stg($s$) to define $Gamma_j(C; k)$ then for each
    $i < k$, $(Gamma_j(C; i))[s] converge$.
    <lemma3.14>
]

The consistency of $Delta(C)$ and $Gamma_j(C)$ are proved just as they were in #chapRef(2).
#lemma[
    For all $j in omega$, Row~$row(j)$ defines a computation for $Delta(C\; j)$ only when no
    other such computation is currently defined.
    <lemma3.15>
]
#proof[
    As #lemmaRef(<lemma2.10>).
]

#lemma[
    Cycle $(j, k)$ defines a computation for $Gamma_j(C; k)$ only when no other such computation is currently defined.
    <lemma3.16>
]
#proof[
    As #lemmaRef(<lemma2.11>).
]

=== Satisfaction of the requirements

As in #chapRef(2) we now prove that all the requirements are satisfied.
All that will then remain is to check that $A leqt G$. Again we define the true path, $f$,
through the priority tree: $f(n) = xi$ where $concatone((restr(f, n)), xi)$ is the leftmost successor of
$restr(f, n)$ accessible infinitely often.

We have the same proposition as before.

#proposition[
    #show: doc => setupenum(doc, formats: ("1.", "a."))
    For all $n in omega$
    + $f(n)$ is defined;

    + $restr(f, (n+1))$ is cancelled only finitely often, (note that $restr(f, 0) = emptyset$ is never cancelled);

    + strategy $restr(f, n)$ satisfies requirement $R_n$;

    + for all sufficiently large $C$-true stages $t$, $restr(f, (n+1)) subset f_t$.
    <prop3.17>
]

So, inductively assume 1, 2, 3 and 4 for $n = eta - 1$ and let $alpha = restr(f, eta)$.
Fix a #stg($s_0$) so larger that $alpha$ is not cancelled after~$s_0$; and for for every
$C$-true stage $t > s_0$, $alpha subset f_t$, $rho(alpha, t) = liminf_s rho(alpha, s)$,
and $tilde(rho)(alpha, t) = liminf_s tilde(rho)(alpha, s)$.

Recall that we say _$alpha$ acts finitely_ if there is a stage after which no cycle of #strat($alpha$) acts,
and otherwise we say that _$alpha$ acts infinitely_.
#lemma[
    If $alpha$ acts infinitely then some specific cycle of $alpha$ acts infinitely often.
    <lemma3.18>
]
#proof[
    As #lemmaRef(<lemma2.17>).
]

The next result follows as it did in #chapRef(2).
#lemma[
    Given a #strat($alpha$), if $chi$ is the leftmost cycle of #strat($alpha$) to act infinitely often
    then only finitely often can _any_ cycle to the left of $chi$ act.
    <lemma3.19>
]

#lemma[
    Some (leftmost) successor of $alpha$ is accessible infinitely often.
    <lemma3.20>
]
#proof[
    As #lemmaRef(<lemma2.19>).
]

This establishes part~1 of the Proposition for $n = eta$ and we may assume that there is a value
$f(eta) = epsilon in Lambda$. Write $epsilon = (nu_eta, i_eta)$ or $epsilon = -1$ as appropriate,
where $i_eta = 1, 2, 3, 4, "or" 5$.

It will again be convenient to define what it means for a cycle to be _lacking_ at #stg($s$).
We say that #cycle($nu$) of #strat($alpha$) is lacking for~$i$ at #stg($s$) if $nu$ is in #state(10)
or #state(11), or
(a)~$i=1$ and $nu$ is in a state numbered less than 2,
(b)~$i=2$ and $nu$ is in a state numbered less than 3,
(c)~$i=3$ and $nu$ is in a state numbered less than 6,
(d)~$i=4$ and $nu$ is in a state numbered less than 7, or
(e)~$i=5$ and $nu$ is in a state numbered less than 9.
Then we have the following results, proved as were Lemmas #thmref(<lemma2.20>)-#thmref(<lemma2.23>)
from the definition of $nu_eta$.
#lemma[
    If $nu_eta$ is defined, then it is lacking for $i_eta$ only finitely often. <lemma3.21>
]
#lemma[
    $restr(f, (eta+1)) = concatone(alpha, epsilon)$ is cancelled only finitely often. <lemma3.22>
]
#lemma[
    Strategy~$alpha$ satisfies requirement $R_(|alpha|)$. <lemma3.23>
]
#lemma[
    For all sufficiently large $C$-true stages $t$, $restr(f, (eta+1)) = concatone(alpha, epsilon) subset f_t$. <lemma3.24>
]

These results establish parts 1-4 of the Proposition and complete the inductive step.
#thmref(<prop3.17>)[Proposition] is proved. #qed


Thus all of the requirements are satisfied, and we have constructed r.e. $D gt.eq_T G$ and
two r.e.[$D$] sets $U^D$ and~$V^D$ such that $D join (udvd)$ is not of 4-r.e. degree.
It remains only to show that in fact $D leq_T G$. We use the same method as we did in #chapRef(2).

For $alpha in T$ we set
$
e^alpha = max ( {j, l | (exists beta in T, i = 1, dots 5)[concatone(beta, ((j, k), i)) subset alpha]} //) sic
$
the largest number which occurs in the path leading to $alpha$ and which may be called upon
by a cycle of some strategy on that path to be a witness to a $G$-change. We set
$
s^alpha = min { s | restr(G_s, e^alpha) = restr(G, e^alpha)}.
$
and recall that $lambda alpha [s^alpha]$ is $G$-recursive.

#lemma[
    Suppose that $t > s^(concatone(alpha, nu))$ is a $C$-true stage, and that $alpha$'s cycle $nu$
    is in state 4, 5, 8, 10 or 11. Then if #cycle($nu$) does not act at #stg($t$) it will never act
    subsequently without first being reset.
    <lemma3.25>
]
#proof[
    As #lemmaRef(<lemma2.24>).
]

#lemma[
    Suppose that $alpha subset f_s$, $t > max{s, s^alpha}$ is $C$-true, and $s' > t$.
    Then for $beta subset alpha$, if $beta subset.not f_t$ but $beta subset f_(s')$
    then there is a $tau in (s, s']$ such that $beta$ is cancelled at #stg($tau$).
    <lemma3.26>
]
#proof[
    As #lemmaRef(<lemma2.25>).
]

We can now prove that the delayed permitting worked.

#lemma[
    $A leqt G$.
    <lemma3.27>
]
#proof[
    \
    Let $y in omega$. As the construction always picks levers to be larger than the current stage,
    if $y$ has not been chosen as a lever by #stg($y$) it never will be and $y in.not A$. Otherwise,
    suppose that $y$ is chosen at #stg($s_0$) to be a lever for cycle~$chi = (j,k)$ of #strat($alpha$).
    Note that $alpha subset f_(s_0)$.

    Assume that $y$ is actually chosen as $lambda^1_(s_0)(x(chi))$. If $k in.not G$ or $k in G_(s_0)$
    then #cycle($chi$) will never get the $G$-permission it needs to enumerate $y$ into $A$ and $y in.not A$.
    Otherwise let $k in setdiff(G_s, G_(s-1))$ and let $t$ be the first $C$-true stage larger than each
    of $s_0$, $s$, and $s^(concatone(alpha, chi))$. We claim that $y$ is enumerated into $A$ by #stg($t$)
    or not at all, so that $G(y) = G_t(y)$.

    If $a subset.not f_t$ then by #lemmaRef(<lemma3.26>) #strat($alpha$) will be cancelled before
    being accessible again, and $y$ will be lost. If some cycle $chi' < chi$ of #strat($alpha$) acts
    at #stg($t$) then $chi$ will be reset and again $y$ will be lost.
    Otherwise, if $chi$ is in #state(1) or~2 at #stg($t$) then the lever~$y$ has already been discarded since being chosen,
    and will never get a chance after $t$ to be enumerated.
    If $chi$ is in #state(3) then, since $G_t(k) = 1$, $y$ will never be enumerated into~$A$.
    If $chi$ is in #state(6), 7, or~8 then by construction, $y in A_t$.
    Otherwise we apply #lemmaRef(<lemma3.25>) to see that #cycle($nu$) must act at #stg($t$)
    if it ever will without first being reset, and lever~$y$ is lost..

    If $y$ is chosen as $lambda^2_(s_0)(x(chi))$ the argument is similar, with $j$ replacing $k$.
]

== The cases $n > 4$ <section3.4>

The complications which arise as $n$ gets larger are of notation, rather than of approach.
When avoiding $n$-r.e. sets we must change our constructed set $n+1$ times, leading to
an $(n+1)$-dimensional cycle structure.
This leads to an increase in the number of times that we must ask for $G$-permission for the levers
corresonding to a given witness~$x$, and in the number of different functionals we construct.

We will not attempt to give anything more than the briefest indications of how to
adapt the $n=4$ construction to larger values of~$n$.  We will start by calculating how many times
our basic module must ask for $G$-permission for a given witness.

Our basic approach remains the same. Given an $n$-r.e. set~$E$ and a witness~$x$, we aim to defeat
any agreement of the type $Eq(x, s)$ by changing $n+1$ times the membership of $x$ in $udvd$, thus
exhausting $E$'s ability to reach. The question is thus: while pushing $x$ in and out of $udvd$,
how many times must we actually enumerate a lever into~$A$, thus requiring $G$-permission?
Well, suppose first than $n = 2m + 1$ is odd, so we must make $n+1 = 2m+2$ changes to $(udvd)(x)$.
Our method is the same as before: we make the first change by putting $x$ into $U^D$, and subsequent ones by
pushing $x$ in and out of $V^D$. Only the "out of $V^D$" action requires $G$-permission:
#[
#set align(center)
#gridx(
    columns: (1in, 1in, 1in),
    align: (col, row) => { bottom + if col == 1 { left } else { center } },
    //
    [Action on\ $udvd$], [Method], [Permission?],
    hlinex(),
    [1. #h(1fr) in:],       [$x$ into $U^D$],   [],
    [2. #h(1fr) out:],      [$x$ into $V^D$],   [],
    [3. #h(1fr) in:],       [$x$ out of $V^D$], [(yes)],
    [4. #h(1fr) out:],      [$x$ into $V^D$],   [],
    [5. #h(1fr) in:],       [$x$ out of $V^D$], [(yes)],
    [6. #h(1fr) out:],      [$x$ into $V^D$],   [],
    colspanx(2)[$dots.v$],  (),                 [],
    [$2m+1$. #h(1fr) in:],  [$x$ out of $V^D$], [(yes)],
    [$2m+2$. #h(1fr) out:], [$x$ into $V^D$],   []
)
]
There are thus $m+1$ pairs of actions, each (except the first) needing exactly one "layer" of $G$-permission.
Thus the number of times that we must ask for $G$-permission is just $m = (n-1)\/2$.
In the case that $n = 2m$ is even, the only change to the table above is the removal of the
$(2m+2)$nd line, and we sill need permission $m$ times.
Thus, given any $n$, we need permission $m = floor(n\/2)$ times for a given witness.
(Notice that in the $n=4$ case we seek permission $2 = floor(4\/2)$ times for each witness.)

Suppose that $n=7$. What needs to be done to adapt the basic $n=4$ module?
Well, most obviously, the cycle structure will now be an $(omega^3)$-sequence of cycles $chi = (j, k, l)$,
to accommodate the 3 layers of permission that we will (potentially) need for each witness.
Secondly, in addition to constructing functions $Gamma_j(C)$ and $Delta(C)$ we will need a third tier,
$Upsilon_(j,k)$ to handle the extra layer of $G$-permission.
With the extra dimension, we need a more general concept than "row".
In general, for the $n$-dimensional structure $omega^n$, we define an $(n-i)$-dimensional _slice_
by specifying the first $i < n$ components:
$
slice(c_1, dots, c_i) = {(c_1, dots, c_i, c_(i+1), dots, c_n) | c_(i+1), dots, c_n in omega}
$

Just as before we had a $Delta$-protecting, "waiting" state, 5, which was used to prevent the over-eager
employment of $G$-changes leading to the inconsistent definition of $Delta(C)$, we must now have states
which protect both $Gamma_j$ and $Delta$.
Before, the trigger for entering #state(5) was the existence of some cycle of slice~#slice($j$) in state~8/9.
To allow us some abstraction, call this double state the _endgame for $Delta$_.
In the new construction, there will be endgames for $Gamma_j$ and $Delta$.
In each case, the endgame consists of the two states immediately following the definition
of $Gamma_j(C;k)$ and $Delta(C\; j)$, respectively, in which the value of the functional value
just defined is still valid, and remains and important part of our overall approach.
While some cycle is in an endgame like this we cannot have cycles to the left acting impetuously,
compromising the consistency of $Gamma_j(C)$ and $Delta(C)$.

Now action on $G$-permission corresponding to definitions of values for $Upsilon_(j,k)(C)$ must
wait until there are no cycles to the right in endgames. The subcases for behavior upon seeing
a $G$-change in #state(4) will now look something like this:

#show: doc => setupenum(doc, formats: ("(a)",))
+ If some (leftmost) cycle $chi'$ of slice #slice($j$) is currently in an endgame for $Gamma_j$ or for $Delta$
  then set the marker $mu^1(x) = tilde(v)_(t_3)(chi')$ and advance to #state(5). This transition does not
  count as an action.

+ [As it was before.]

Note that we need only one $Upsilon_(j,k)$-related waiting state to protect both $Gamma_j$ and $Delta$ computations.
We set $mu^1(x)$ to keep our eye on the leftmost cycle, $chi'$, to our right in a $Gamma_j$- or $Delta$-endgame.
If $chi'$ should leave its endgame, the monotonicity of the computation function will ensure that all cycles to _its_
right will leave their respective endgames as well.

Now, $G$-changes corresponding to $Gamma_j$ definitions must also be treated with caution:
action upon these changes must still respect $Delta$-endgames. Thus the state immediately after
the definition of the value $Gamma_j(C; k)$ will have similar subcases to determine the response
to a $G$-change. In this case we need only keep an eye out for $Delta$-endgames.
(Note that the extra waiting state that will follow means that a $Gamma_j$-endgame actually consists of the
 _three_ states immediately following the functional definition. We lied before.)

Apart from that, the same construction will work for $n=7$, and may be adapted for any $n > 4$.
Every time an increase in $n$ requires the addition an extra dimension to the cycle-structure
(that is, every time $n$ is incresed from $2m-1$ to $2m$), we just "bolt" one to the front:
add an extra tier of functionals, with a corresponding waiting stage to protect all of the existing tiers.

== Further comments

As all of the strategies are self-contained, it does not hurt to combine strategies corresponding to
different valus of $n$, so long as we associate their enumerations with different $dreInAbove(D)$ sets.
So, those strategies concerning themselves with avoiding 5-r.e. degrees (say) work with the set
$C join A join (setdiff(U^(D,5), V^(D,5)))$, while those avoiding 13-r.e. degrees work with the separate
$C join A join (setdiff(U^(D,13), V^(D,13)))$. A description of the priority tree then
becomes more complicated (as different nodes will have different successor-sequences),
but in principle the construction is no different. Indeed, as all of the strategies for all $n$
can be combined, we can actually construct a single $D leqt G$ for which, given $n$, there is
a $dreInAbove(D)$ set not of $n$-r.e. degree:
#theorem[
    Given r.e. sets $C ltt G$ there is r.e. $D in turinginterval(C, G)$ such that for all $n in omega$
    there is a $dreInAbove(D)$ set $F_n$ not of $n$-r.e. degree.
    <theorem3.28>
]
In fact, there is no need to keep enumerations for different values of $n$ separate: we can
construct a single $dreInAbove(D)$ set $F$ with is not $n$-r.e. for any $n$:
#theorem[
    Given r.e. sets $C ltt G$ there is r.e. $D in turinginterval(C, G)$ and a $dreInAbove(D)$ set $F$
    not of $n$-r.e. degree for any $n in omega$.
    <theorem3.29>
]

It is also interesting to note that the sets $F_n$ we construct are just barely $dreInAbove(D)$.
In the construction, elements are only ever enumerated into $U^D$ once, at least modulo "unwanted"
ejections due to $C$-changes. In the absense of these $C$-changes the set $U^D$ would be
recursively enumerable. Hence the set(s) $udvd$ are really the difference of an (almost) r.e.~set
and a $C$-r.e. one. Then the question is, how much do we really use the full strength
of "$dreInAbove(D)$"? Can we get the same final result using just $reInAbove(D)$ in place of $dreInAbove(D)$?
Using the present technique, the answer is "no".

The key point in the construction is that we know, ahead of time, how many times we will have to
change the membership of a particular witness in the set $udvd$, and hence the number of times we
will have to ask for corresponding $G$-permissions. This means that, for a specific basic module,
we can specify ahead of time what the cycle-structure is going to look like, $omega^(floor(n\/2))$,
and hence what the possible outcomes will be. All of this is possible because for each witness we have
two _anchor-points_, $restr(E_(s_1), phi_(s_1)(x))$ and $restr(E_(s_2), phi_(s_2)(x))$, to which
we return over and over. Since we force $restr(E, phi_(s_1)(x))$ to repeatedly flip-flop between
these two states, we see that there is a _fixed_ number (called $y$ in the construction) on which
$E$ must change each and every time. As we know how many times $E(y)$ can change we can therefore
put a bound, _before any cycle of the strategy starts_, on how many times we will have to flip-flop.

Consider what would happen here if we tried to construct $F = C join A join V^D$, an $reInAbove(D)$ set.
At our equivalent of #state(1) we would choose a lever $lambda_1(x)$ larger than $tilde(u)$,
and enumerate $x$ into $V^D$ with use $lambda_1(x) + 1$.  Then, when we see the next stage of agreement, $s_2$,
with total use $tilde(v)$, we would (after waiting for permission) kick $x$ out of $V^D$ by pulling the
lever~$lambda_1(x)$. However, it is impossible for us to restrain $restr(A, tilde(v))$ from #stg($s_2$)
onwards, as we cannot be sure that $lambda_1(x) > v$. The very act of returning $V^D$ to its $s_1$ shape
may change $restr(A, tilde(v))$. Thus, instead of two anchor-points, we will only have one,
$restr(E_(s_1), phi_(s_1)(x))$, to which we can be sure of returing each time. Thus, while we can say each time that
$
restr(E_(s_("odd")), phi_(s_1)(x)) = restr(E_1, phi_(s_1)(x)) neq restr(E_(s_("even")), phi_(s_1)(x)),
$
there is no coordination between $E$ at the $s_("even")$
stages,#footnote[Of course, $s_("even")$ should in no way be confused with #[_s_]even or even _seven_.]
and we cannot be sure that $E$ changes on the same element each time.
Thus, instead of the number of changes in $restr(E, phi_(s_1)(x))$ that we must wait for being bound in advance by~$n$,
we must allow $E$ (potentially) to change $n$ times on each element less than $phi_(s_1)(x)$. Thus, instead of
needing to change our constructed set $n+1$ times, we may need to change it
$m(x) = m(x, s_1) = (1 + n dot phi_(s_1)(x))$ times for the witness~$x$.
This bound is clearly not known before the cycle starts: we have to wait until stage~$s_1$ to find it.

This, of course, is where thep problems start. Before we knew that all the witnesses chosen by a given strategy
would be content with just $n+1$ changes and could thereforew do with an $omega^(floor(n\/2))$ cycle structure.
Now, as we chose larger and larger witnesses for the various cycles, the potential number of times that we must seek
permission may grow without bound. This fact by itself does not make the construction impossible: we can
use $omega^(< omega)$ (ordered lexicographically) to organize our cycles, and we can speak of slices of all finine
dimensions. Define the _slice dimension_ of a #cycle($chi$) as the dimension of the smallest
slice containing $chi$ and all of itse predecessors. Thus the slice dimension of cycle $(1, 1, 1)$ is 3, while
that of $(1, 0, 0, 0)$ is 4. Various cycles will now have varying (finite) numbers of internal states
(determined by each cycle dynamically as soon as $phi_(s_1)(x)$ is calculated), and the strategy
as a whole may have infinitely many different ones. There is now a fundamentally different kind of possibility
that must be considered in the proof of #lemmaRef(<lemma3.18>) (which is really just the proof of #lemmaRef(<lemma2.17>)):

($infinity$) #h(0.5em) For all $i in omega$ a non-zero number of cycles of slice dimension greater than $i$ act.

The author has been unable to turn a failure of this type into a deomnstration that $G leqt C$.
In the $dreInAbove(D)$ construction, possibility~(A), say, of #lemmaRef(<lemma3.18>) (actually of #lemmaRef(<lemma2.17>))
led to computation of $G$ from $C$ "along the first component". In general, for any $n$, a failure of
the $dreInAbove(D)$ computation leads a computation of $D$ along one of the components. Outcome ($infinity$) allows no
such computation.

The same problems occur, even when we allow $F$ to be $dreInAbove(D)$, if we try to avoid $omega$-r.e. degrees,
as again the number of flip-flops depends on the particular witness chosen.

=== The special case $C = emptyset$

The case in which $C = emptyset$ was the first to be proved by the author.
It was obtained before the method was developed to ensure the consistency of the $Delta$ functional,
as that method is not needed in the special case. The overall construction is in any case vastly simplifed.

To see why, consider what would happen in the construction if $C = emptyset$. In particular, we never experience a $C$-change.
At no time would a #cycle($chi$) need to return to an earlier numbered state due to a computation being destroyed.
So long as it is not reset, $chi$ will only ever make progress, or (at worst) stay put.
This means that no strategy will act infinitely often.
(Otherwise, by Lemmas~#thmref(<lemma3.18>) and~#thmref(<lemma3.19>),
 some cycle would act infinitely without being reset infinitly often).
In other words, _each strategy causes only finitely much injury._
Once we have a finite injury argument, we can do away with the entire apparatus of the priority tree.

The finite injury nature of the construction also means that the functionals $Gamma_j$ and $Delta$
do not need to be constructed "on the fly", but can be extracted without too much trouble after the face, in the verification,
under the assumption that the construction has failed. This allowed us to completely avoid the problems of
$Delta$-inconsistency in the original Cooper, Lempp, and Watson method.
Hence there was no need for the special method we used above

An interest artifact of the finite injury construction is that witnesses are enumerated out of our set~$F$ only
when we want them to be, in forcing the opponent set, $E$, to change. That is, when avoiding an $n$-r.e. set,
the value of $(udvd)(x)$, for a given witness, will change at most $n+1$ times: the constructed set will be $(n+1)$-r.e.
Hence we have the following.
#theorem[
    Given an r.e. set $G ident.not_T emptyset$, there is r.e. $D leqt G$ such that for all $n in omega$
    there is a set $F$ which is simultaneously $dreInAbove(D)$ and $(n+1)$-r.e. but not of $n$-r.e. degree.
    <theorem3.30>
]
When combining requirements corresponding to different values of $n$ we can tell for the sake of which $n$-value a specific
witness $x$ was chosen, and hence the maximum number of times that $(udvd)(x)$ will change. We thereforew have the following result,
which corresponds to #thmref(<theorem3.29>) just as #thmref(<theorem3.30>) corresponds to #thmref(<theorem3.28>)[Theorem].
#theorem[
    Given an r.e. set $G ident.not_T emptyset$, there is r.e. $D leqt G$ and a set $F$ which is
    simultaneously $dreInAbove(D)$ and $omega$-r.e., but not of $n$-r.e. degree for any $n in omega$.
    <theorem3.31>
]

=== A related result

In @ALS1998 the following is proved

#theorem(name: [Arslanov, LaForte and Slaman])[
    Any $omega$-r.e. set with is 2-REA is actually of 2-r.e. degree.
    <theorem3.32>
]
The question then occurs: does the behaviour occur for numbers greater than 2?
The same paper answers the question negatively:
#theorem(name: [Arslanov, LaForte and Slaman])[
    There is a set F which is both 3-REA and $(n+1)$-r.e. but fails to be of $n$-r.e. degree.
    <theorem3.33>
]
In that paper, $F$ is constructed to be 3-REA by making it recursively enumerable in, and above, a d.r.e. set $D$.
(The names for these sets are different in~@ALS1998.)

In the present paper we also construct such a set, $F$. Our $F$ is certainly 3-REA, as it is above and d.r.e. in (and hence 2-REA in)
an r.e. set $D$. By using the construction corresponding to #thmref(<theorem3.30>)[Theorem] we can
take $F$ to be $(n+1)$-r.e. and the whole point of $F$ is that it is not of $n$-r.e. degree.

The proof in @ALS1998 of #thmref(<theorem3.33>)[Theorem] is of finite injury, and involves a construction using two anchor-points.
Thus an adaption is possible, involving cycles, which will find the d.r.e. set $D$ below any previously given, non-recursive,
r.e. set~$G$. Therefore Theorem~11 in @ALS1998 may be slightly strengthened to read
#theorem[
    Given any non-recursive, r.e. set $G$ there is a d.r.e set $D leqt G$ such that, for every $n geq 3$, there exists
    a set $F_n$ which is simultaneously $reInAbove(D)$ and $(n+1)$-r.e. but is not of $n$-r.e. degree.
    <theorem3.34>
]


////////////////////////////////////////
// Chapter IV
= For high $C$ the properly $reInAbove(C)$ intervals are weakly dense <chapter4>

== Introduction

In #chapRef(3) we gave a generalization of (a weaker form) of the origianl Soare and Stob result.
In #chapRef(5) we will prove a generalization in another direction:
// TODO: label this 5.2
#theorem[
    For any non-recursive r.e. set $C$, there are $reInAbove(C)$ sets $A$ and $B$ such that $A ltt B$
    and there is no r.e. set $D in turinginterval(A, B)$.
]

In this chapter we consider the latter result from the point of density: can such r.e.-free intervals be
found densely in the r.e. degrees?
#conjecture[
    For all r.e. sets $C$, $G$ and $H$ such that $emptyset ltt C leqt G ltt H$ there
    are $reInAbove(C)$ sets $D ltt F$ such that $turinginterval(D, F) subset turinginterval(G, H)$
    and there is no r.e. set $E in turinginterval(D, F)$.
    <conjecture4.1>
]
This (and even the weaker version in which we allow $D = F$) is false because of
#theorem(name: [Arslanov, Lempp and Shore, @ALS1996])[
    There is a recursively enuemrable set $C$ with $emptyset ltt C ltt emptyset'$ such that
    every $reInAbove(C)$ set $A$ with $C leqt A leqt emptyset'$ is of r.e. degree.
    <theorem4.2>
]
However, we can succeed if $C$ is high:
#theorem[
    If $C$ is r.e. and high and $G ltt H$ are r.e. with $C leqt H$ there are $reInAbove(C)$ sets
    $D ltt F$ such that $turinginterval(D, F) subset turinginterval(G, H)$ and there is no r.e. set $E$ with
    $E in turinginterval(D, F)$. Furthermore, $D$ and $F$ may be chosen to be d.r.e.
    <theorem4.3>
]

== The construction

The proof we give is derived from one given in @ALS1996 of the similar statement
// This appears to be Thm 2.1 in the other paper
#theorem[
    If $C leqt H$ are r.e. and high (that is, $C' ident_T H' ident_T emptyset'$), there is a d.r.e. set
    $E$ which is $reInAbove(C)$ but not of r.e. degree such that $C ltt E ltt H$.
    <theorem4.4>
]
That proof suffers from several flaws. It is based on the original proof of #theoremRef(<theorem2.1>) given in @CLW1989,
and hence has the same problems: injury caused by "weaker" strategies (noted and fixed by LaForte) and $Delta$-inconsistency.
It also has a flaw all its own (see @section4.4[Section] below)

As well as strengthening #theoremRef(<theorem4.4>) we simplify the argument, fixing at a stroke
both the $Delta$-consistency and local problems. The method of previous chapters is used for the remaining obstacle.

The simplification which allows us to do away with $Delta$-inconsistency without the need for the "waiting states"
of earlier chapters is the reduction of the cycle structure from two dimensions to one. For each witness we still need
two layers of $H$-permission, but we get the second one (almost) for free, from the "high permitting" argument
inherent in the construction. The use in~@ALS1996 of a two dimensional cycle structure is overkill.

To see how we will use the hypothesis that $C$ is high consider the following.
By a result of Robinson~@Robinson we may assume (perhaps by replacing $C$ with a Turing equivalent r.e. set)
that we can find a recursive enumeration ${C_s st s in omega}$ such that the _computation function_
$
  c_C(x) = (mu s)[restr(C_s, x) = restr(C, x)]
$
dominates all (total) recursive functions.
That is, if $f$ is a total, recursive function, there is $n in omega$ such that $(forall m > n)[c_C(m) > f(m)]$.
(Roughly speaking, our construction will require $C$-permission "late" in the strategy, and the fact that $c_C$
 dominates every recursive function means that we get this permission when we need it. Whenever you
 (recursively) guess how long it takes initial segments of $C$ to converge, you are wrong confinitely often.)
Fix such an enumeration, and enumerations ${G_s}_(s geq 0)$ and ${H_s}_(s geq 0)$.

We will construct an auxiliary r.e. set $B$ and arrange things so that $D = G join A$ and $F = G join A join B$
have the required properties. That $D$ and $F$ are d.r.e will follow from the fact that the approximations to
the set~$A$ will change at most twice on any element (at worst, $x$ will be enumerated into $A$, and later removed forever.)

We must satisfy all the requirements of the form
$
R_e: quad A neq Phi_e(E_e) thick or thick E_e neq Psi_e(G join A join B)
$
and
$
N_e: quad B neq Theta_e(G join A)
$
where ${angletup(E_e, Phi_e, Psi_e)}_(e geq 0)$ enumerates all triples in which $E_e$ is an r.e. set and $Phi_e$ and $Psi_e$
are recursive functionals, and ${Theta_e}_(e geq 0)$ simply enumerates all recursive functionals.
We will ensure that $A leqt H$ by a combination of direct permitting, and the high permitting used to make $A$ r.e. in~$C$.
We ensure $B leqt H$ by direct permitting.  As in earlier chapters all of the permission is potentially delayed.

=== The Basic Modules

==== The $R_e$ requirements

For the requirements of the first type (the "r.e.-avoiding" requirements) the basic module is
a simplified version of the one used in @ALS1996[Theorem 2.1]. This in turn is basically the approach used in
@CLW1989[Theorem 1], but incorporating high permitting. The strategy used to satisfy $R_e$ consists of a
(potentially unbounded) number of _cycles_, each of which tries to satisfy the requirement in a very simplistic way.
If each cycle fails, we argue that $H leqt G$, contradicting the typothesis of the theorem.

Suppose $e$ is fixed, and write $angletup(E, Phi, Psi)$ for $angletup(E_e, Phi_e, Psi_e)$. We will describe the strategy
for satisfying~$R_e$.  It consists of an $omega$-sequence of cycles. Cycle~0 starts first, and each #cycle($k$) can start
cycle $k+1$, as well as stopping all cycles $k' > k$. The strategy as a whole threatens to demonstrate that
$H leqt G$ by constructing a functional $Gamma(G) = H$. The #cycle($k$) may define the value $Gamma(G\; k)$. The strategy
also defines values for an auxiliary (partial) recursive function~$m$, used in the high permitting part of the argument.

All cycles begin in #state(0).
A cycle is _started_ by letting it pass from #state(0) to another state,
depending on its history, as in earlier chapters. Again, a cascade of cycle-startings might occur.
A cycle is _reset_ by putting it back into #state(0), returing its restraints to 0 and undefining the values of its
parameters, $u$, $x$, and $p$.
A cycle is _abandoned_ by returing its restraints to 0 and (permanently) stopping all activity for that cycle.
This is done when a cycle has categorically failed to satisfy $R_e$, as in the earlier chapters.
A cycle is said to _act_ when it moves from one state to another.

Cycle~$k$ proceeds as follows.

// reset to default
#show: doc => setupenum(doc)
0. Until given the go-ahead, just hang out with the other cycles.
   When told to start first check if #cycle($k$) has been abandoned at any time. If so jump straight to #state(6)
   and follow the instructions there. Otherwise choose a witness, $x$, larger than any number mentioned in the construction
   so far (including all currently defined $A$-restraints and the current stage) and larger than $k$.

+ Let $Eq(x, s)$ denote the condition
  $
  (A(x) = Phi(E\; x))[s] squad and squad (restr(E, phi(x)) = restr(hat(Psi)(G join A join B), phi(x)))[s]
  $
  Wait for a stage $s_1$ at which $Eq(x, s_1)$ holds and let $u = (hat(phi) phi(x))[s_1]$, the total use of the
  $hat(Psi)(G join A join B)$ computations.
  [Note that if no such $s_1$ exists, then $x$ witnesses the success of our strategy.]

  If $H_(s_1)(k) = 1$ then we have no hope ever of seeing the $H$-change we need for permission, so go to #state(6).

  Otherwise restrain $restr(A, u)$ and $restr(B, u)$ from now on, set $Gamma(G\; k) = H_(s_1)(k) (= 0)$ with
  use~$u$, and start cycle $k+1$ to run simultaneously. Advance to #state(2).

+ Wait for a stage $s'$ at which either

  + $restr(G_(s'), u) neq restr(G_(s_1), u)$, or
  + $H_(s')(k) neq H_(s_1)(k)$

  On reaching $s'$, reset all cycles $k' > k$ of strategy $alpha$. Then

  + if $restr(G, u)$ changes first, drop the $A$- and $B$-restraints of #cycle($k$) back to 0
    and return to #state(1).
    (Note that the change in $G$ will automatically undefine the values $Gamma(G\; k')$ for $k' geq k$,
     allowing these values to be redefined later, keeping $Gamma$ consistent.) While
  + if $H(k)$ changes first, let $p in omega$ be least such that
    $m(p)$ is not defined yet. Enumerate $x$ into $A$ with $C$-use $p$. This enumeration has just been permitted by the change
    in $restr(H, x)$ (since, by choice, $x > k$.) Proceed to #state(3).

    Note that we now know that $H(k) = 1$: it will never change again, as $H$ is r.e.
    Thus, if we ever subsequently get a change in $G$ below $u$, we may redefine $Gamma(G\; k) = 1$ with use~0,
    and be sure that $Gamma(G\; k) = H(k)$. From now on, if we see such a change in $G$, jump straight to #state(6).

+ Set the marker $xi(x) = p$ and wait for a stage $s_2$ at with either

  + $restr(G_(s_2), u) neq restr(G_(s_1), u)$; or
  + $restr(G_(s_2), u) = restr(G_(s_1), u)$ and $Eq(x, s_2)$.

  Note that if such a $s_2$ does not exist, $x$ again witnesses our success.

  It in entirely possible that while we are wating for $s_2$, $C$ changes below $xi(x)$, ejecting $x$ from $A$.
  We waint $x$ to remain in $A$ for now, so we "artificially" keep it there by enumerating new axioms
  $angletup(x, restr(C_t, p))$ into $U$ (where we are constructing $A = U^C$) whenever $restr(C_t, p) neq restr(C_(t-1), p)$.
  (Note that this is enough to keep $A$ d.r.e. We consider $x$'s ejection from $A$ a transitory phenomenon, not affecting
   the enumeration of $A$ that our algorithm defines. To decide whether $x in A$ at #stg($s$), check if $x in A$ at
   the _end_ of the stage.)

  When we reach such a stage, set $m(p) = s_2$. If we have just seen a $G$-change, jump straight to #state(6).
  Otherwise, proceed to #state(4). Note that in the latter case we have $A_(s_1)(x) = 0$ and $A_(s_2)(x) = 1$
  and so we must have $restr(E_(s_1), phi_(s_1)(x)) neq restr(E_(s_2), phi_(s_1)(x))$.
  This change is irreversible, as $E$ is r.e., and we attempt to exploit this, by waiting for
  $x$ to be enumerated out of $A$ by a $C$-change. Start #cycle($k+1$) to run simultaneously.

  (Note that, although in #state(2) we reset all cycles $k' > k$, this resetting cannot destroy the
   computations $Gamma(G \; k+1), Gamma(G \; k+2), dots$ that these cycles may have defined:
   there has not been a convenient $G$-change. Thus the restarted $k+1$ (and its cronies $k+2, k+3, dots$)
   may produce values for $Gamma(G)$ at points where it is already defined.
   We will argue that such multiple definitions only persist when #cycle($k$) gets permanently stuck
   in #state(4) and this will only happen to finitely many cycles.)

+ Wait for a #stg($s dubpr$) at which $restr(C, xi(x))$ changes. Let this change in $C$ remove $x$ from A,
  reset all cycles $k' > k$ and go to #state(5).

  Now if $restr(G, u) = restr(G_(s_1), u)$, $x$ finally witnesses the success of our strategy, since
  $
  restr(hat(Psi)(G join A join B), phi_(s_1)(x))
     &= (restr(hat(Psi)(G join A join B), phi(x)))[s_1] \
     &= restr(E_(s_1), phi_(s_1)(x)) \
     &neq restr(E, phi_(s_1)(x))
  $

  Note that we are potentially stuck with the disagreement $Gamma(G\; k) neq H(k)$
  (if we don't see the desired change in $restr(C, xi(x))$, or a change in $G$ below $u$ which would allow
   us to redefine our (incorrect) value $Gamma(G\; k)$.)
  The fact that the computation function $c_C$ is dominant means that we will only have to put up with this
  finintely often (see #lemmaRef(<lemma4.6>)), and we will still be able to threaten to compute $H$ recursively from $G$.

+ Wait for $restr(G, u) neq restr(G_(s_1), u)$. If this never happens, the strategy succeds by the argument in #state(4),
  above. If it does happen, reset all cycles $k' > k$ and advance to #state(6) to redefine $Gamma(G\; k)$ as a value
  we now know to be correct, and abandon the cycle.
  (Note that the change in $G$ automatically undefines any values $Gamma(G\; k+1), Gamma(G\; k+2), dots$ which where
   defined while #cycle($k$) was waiting in #state(4). Thus, so long as we don't get permanently stuck in~4, the
   extraneous $Gamma$ values that are defined while we wait for the $G$-change don't persist. Of course, leaving~4
   but failing to reach 6 means we get stuck in 5, which leads to success.)

+ Redefine $Gamma(G\; k) = H(k) = 1$ with use 0, abandon #cycle($k$) and start #cycle($k+1$).

==== The $N_e$ requirements

The requirements $N_e$ are simpler that those of the first kind, are we implement a standard
diagonalizatin approach to satisfy them.  This is slightly complicated by the fact that we must
ensure that $B leqt H$, but we can just us a stripped-down version of the Cooper, Lempp and Watson method.

Again, suppose $e$ is fixed, and write $Theta$ for $Theta_e$. The strategy for $N_e$ has the same cycle
structure as that for $R_e$. Cycle~0 starts first. We again threaten to show $H leqt G$, this time by
constructing a functional $Delta(G) = H$. We don't need any auxiliary function like~$m$.
_Starting_, _resetting_, _abandoning_ and _acting_ all have the same definitions as before.

Call a node at which this strategy is being pursued $alpha$. Cycle~$k$ proceeds as follows.

#show: doc => setupenum(doc, prefix: "N")
0. Until given the go-ahead, do nothing. When given the signal to proceed, check if
  #cycle($k$) has been abandoned in the past. If so jump straight to #nstate(4).
  Otherwise choose a witness, $y$, larger than any number mentioned so far in the constuction
  (including all currently defined $B$-restraints and the current stage), and larger than~$k$.

+ Wait for a stage $s_1$ at which
  $
  (B(y) = hat(Theta)(G join A; y))[s_1]
  $
  and let $v = hat(theta)_(s_1)(y)$, the use of the $hat(Theta)(G join A)$ computation. Restrain $restr(A, v)$
  from now on. Set $Delta(G\; k) = H_(s_1)(k)$ with use $delta(k) = v$ and start cycle $k+1$ to run simultaneously.

+ Wait for a stage $s'$ at which

  + $restr(G_(s'), v) neq restr(G_(s_1), v)$, or
  + $H_(s')(k) neq H_(s_1)(k)$.

  On reaching $s'$, reset all cycles $k' > k$. Then
  + if $restr(G, v)$ changes first, return the $A$-restraint of this cycle to 0 and return to #nstate(1).
    (As before, the $G$-change undefined $Delta(G\; k')$ for $k' > k$.) While
  + if $H(k)$ changes first and enumerate $y$ into $B$. This has just been permitted by the change in $restr(H, y)$.
    Proceed to #nstate(3).

+ Wait for a stage $s_2$ at which
  $
  (B(y) = hat(Theta)(G join A; y))[s_2]
  $
  If there is no such state, $y$ witnesses the success of our strategy.

  If such an $s_2$ exists, note that we have
  $
  (Theta(G join A\; y))[s_2] = B_(s_2)(y) = 1 neq 0 = B_(s_1)(y) = (Theta(G join A\; y))[s_1]
  $

  By the restraint on $A$, $restr(A_(s_1), v) = restr(A_(s_2), v)$, so we must have $restr(G_(s_1), v) neq restr(G_(s_2), v)$.
  We reset all cycles $k' > k$ and advance to #nstate(4).
  Note that the $G$-change has undefined all computations for $Delta(k')$, $k' > k$, except those computations with 0 use
  (which are correct anyway).

+ We set $Delta(G\; k) = 1$ (with use 0) a value we now know to be correct, start cycle $k+1$, and abandon #cycle($k$).

Note that at all times, $Delta(G)$ is defined consistently.

#lemma[
    TODO
    <lemma4.6>
]

=== Combining the modules

We use much the same tree argument as previous chapters to combine our strategies.
As each cycle (in either basic strategy) imposes only one "wave" of restraint, we need only
one outcome corresponding to each cycle.

Let $Lambda = {-1} union omega$, with the natural ordering and let $T = finseq(Lambda)$ be the
tree of strategies, with the standard partial ordering $<_L$.
If $alpha in T$ is of length $|alpha| = 2e$ then $alpha$ will work towards satisfying requirement $R_e$,
while if $|alpha| = 2e+1$, $alpha$ will work towards satisfying $N_e$.
We make no distinction between a node and the strategy it is employing.
A strategy/node is _cancelled_ by resetting all of its cycles and discarding any functional
it may have (partially) defined. Any parameter, once defined, keeps that value until it is redefined or undefined.

The construction proceeds as follows.

Stage 0: #h(1em) All parameters are undefined or $emptyset$, as appropriate,
all functionals are completely undefined and all cycles are in #state(0) or #nstate(0), as appropriate.

Stage $s+1$: #h(1em) We define, in substages $t < s$, a finite path, $f_(s+1)$, through $T$, of length $s$.
We think of $f_(s+1)$ as our approximation to the "true" path defined at stage $s+1$.
So, suppose we have reached substage~$t$, and $alpha = restr(f_(s+1), t)$ is already defined.
If no cycle of #strat($alpha$) is started, we start $alpha$'s #cycle(0), and set $f_(s+1)(t) = 0$.
Otherwise, we have two cases.

- #case(1) Some (least) #cycle($k$) of $alpha$ is able (or forced, by a $G$-injury) to act

We allow #cycle($k$) to act.
Let $l$ be the rightmost cycle of #strat($alpha$) now imposing restraint (if there is any such cycle)
and put $f_(s+1)(t) = l$. If there is no such #cycle($l$) then put $f_(s+1)(t) = -1$.
Cancel all strategies $beta$ with $concatone(alpha, f_(s+1)(t)) <_L beta$.
If $l = k$ and the action of #cycle($k$) involved enumerating a number into or out of $A$
or into $B$ then also cancel all strategies $beta supset concatone(alpha, f_(s+1)(t))$.

- #case(2) No cycle of #strat($alpha$) is able, or forced, to act.

We do nothing, and there are no strategies to cancel. Define $f_(s+1)(t)$ just as above.

If $t + 1 < s$, we advance to substage $t+1$.

The strategies $alpha subset f_(s+1)$ are said to be _accessible_ at stage $s+1$.

== The flaw in the proof of #thmref(<theorem4.4>) <section4.4>

= Chap 5 <chapter5>

#bibliography("works.yml", style: "ieee")
