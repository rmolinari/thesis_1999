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

// Convenience symbols
#let phi = sym.phi.alt
#let epsilon = sym.epsilon.alt
#let join = sym.plus.circle
#let neq = sym.eq.not // not equal
#let leq = sym.lt.eq  // greater than or equal
#let geq = sym.gt.eq  // less than or equal
#let st = sym.bar.v   // vertical bar: "such that"
#let dubpr = sym.prime.double // double primes
#let trippr = sym.prime.triple // triple!


////////////////////////////////////////
// Some standard notation

// Set difference
#let setdiff(a, b) = $#a tilde.op #b$
// Turing interval
#let turinginterval(a, b) = $[#a, #b]_T$
// Turing less than and leq. Note that we have extra space after this symbol. See https://github.com/typst/typst/issues/877. The
// workaround is to specify 0 space ourselves.
#let ltt = $<_T$
#let leqt = $lt.eq_T$
#let notleqt = $lt.eq.not_T$
#let equivt = $ident_T$
#let emptyset = $nothing$
// "Zero jump"
#let zerojump = $emptyset'$
// Pseudojump V applied to X
#let pseudojump(X, V) = $#X join #V^(#X)$

// Logical implication, informally
#let implies = $arrow.r.double$
#let iff = $arrow.l.r.double$

// Calculation converges
#let converge = $#h(0em) arrow.b #h(0.05em)$
#let diverge = $#h(0em) arrow.t #h(0.05em)$

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

// Standard pairing function
#let pair(a, b) = $angletup(#a, #b)$

// Restriction of a to b
#let restr(a, b) = $#a harpoon.tr #b$
// Concatenation of sequences a and b
#let concat(a, b) = $#a paren.t #b$
#let concatone(a, b) = $concat(#a, #angletup(b))$

// Functional F relativized by Y, evaluated at x
// Define a macro because of the tedium of backslashing the semicolon
// Note the semicolon after #F to force the parser out of code-mode.
#let fff(F, Y, x) = $#F;(#Y\; #x)$

#let setconcat(M, N) = $#M\; #N$

//  Inline 1/2. Typst does a bad job with fractions inline, insisting on using a vertical layout. It is surprising.
#let half = $1\/2$

// "Finite sequences of"
#let finseq(a) = $#a^(< infinity)$

// A "column" of a set: those pairs selected on the second coordinate by b.
#let column(a, b) = $#a^([#b])$

// Row j of an omega^2 set of cycles, and a more general "slice" of a higher-dimensional set
#let row(j) = $cal(R)_#j$
#let slice(..j) = $cal(S)_(#j.pos().join([,]))$
// A cycle pattern. Note awkward negative space to get good placement of the subscript
#let pattern(s) = $cal(P)#h(-0.2em)_#s$

// State/stage/strategy/row numbers/names, with nonbreaking space
//#let set-normal(z) = text(style: "normal")[#z]
#let state(num) = [state~#num]

// it's oddly difficult to make the prefix upright in all contexts. I couldn't work out how to use text styling: it kept coming out
// italic inside math mode. (See #set-normal, just above.)
#let named-state(prefix, num) = [state~$upright(prefix)$#num]
#let nstate(num) = named-state("N", num)
#let pstate(num) = named-state("P", num)
#let strat(s) = [strategy~#s]
#let stalpha = [#strat($alpha$)]
#let stg(num) = [stage~#num]
#let theRow(j) = [row~$row(#j)$]
#let cycle(name) = [cycle~#name]

// The "equality" property
#let Eq(x, y) = $sans("Eq")(#x, #y)$
#let blankEq = $Eq(ast.op, ast.op)$ // with stars as arguments

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
#let phase(name) = {
    set text(font: "Sans Serif")
    [Phase #name #h(1em)]
}
#let squad = h(1em)

// The and wedge doesn't get enough space around it in display math. Try this
#let sand = $#h(0.5em) and #h(0.5em)$

////////////////////////////////////////
// Global formatting
#set par(justify: true)

#set text(font:"New Computer Modern")

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
    pagebreak(weak: true)
    v(2in)
    set text(weight: "bold")
    align(center)[
      CHAPTER #counter(heading).display()\
      #v(0.5em)
      #it.body
      #v(0.8in)
    ]

    // We number footnotes by chapter.
    // This doesn't really belong here, in a formatting function, but where else?
    // Maybe define a new function #chapter that makes the header and resets this counter.
    counter(footnote).update(0)
}

= Introduction
== Definitions and notation

The notation used in this paper is largely standard, and the reader is directed to @Soare1987 for an exposition. We note the
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
The point of all this is the following. If $Phi\(C; x) converge$, then cofinitely often $hat(Phi)_s(C; x) converge$, and for every
$C$-true stage $s$, $hat(Phi)_s(C_s; x) arrow.r.double hat(Phi)(C; x) converge$. The hattrick serves to weed out at $C$-true stages
all but the correct computations.

Finite sequences are denoted variously with parentheses, $(x_0, dots, x_(n-1))$ and angle brackets $angle.l x_0, dots, x_(n-1)
angle.r$. The length of the sequence $alpha$ is denoted $|alpha|$. The empty sequence, $angle.l angle.r$, is written as $emptyset$.
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
$reIn(Y)$ set $U^Y$. $U$ then becomes a _pseudojump operator_, $U : Y arrow.r.bar pseudojump(Y, U)$. These operators will appear in
#chapRef(6).

A set $Y$ is _recursively enumerable in, and above_ $X$ ("Y is $reInAbove(X)$") if $Y$ is $reIn(X)$ and $X leqt Y$.
If, instead, $Y$ is the difference of two $reIn(X)$ sets, and $X leqt Y$ then Y is said to be $dreInAbove(X)$.

= A patched proof of the weak density of the properly d.r.e. degrees <chapter2>

== Introduction

In @CLW1989 a proof is given of the weak density of the properly d.r.e. degrees:
#theorem[
Given recursively enumerable sets $C ltt G$ there is a d.r.e. set $D$ not of r.e. degree such that $C ltt D ltt G$.
<theorem2.1>
]

The proof given in @CLW1989 has two technical but important flaws. The first, involving the timing of injuries caused by different
strategies competing on the priority tree, was noted and fixed by LaForte in @LaForte. The second, involving the claim that the
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
cycles attempt to define functionals $Delta(C)$ and $Gamma_j(C)$ (for $j in omega$) such that, if the strategy fails to satisfy
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
need to keep the definition of $Gamma_j(C)$ synchronized with enumerations into the set $G$ conflicts with the more subdued approach
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

The basic module is very nearly the same as the one given in @CLW1989. (It appears to be somewhat different here,
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
state 0, returning its restraints to 0 and undefining the values of its parameters $u$ and $v$.
//
(Note that the paper @CLW1989 uses
"_cancelled_" for this operation. We reserve this word for another purpose: see the description of the priority tree construction in
@section2.2.3 below.)
//
A cycle is _abandoned_ by returning its restraints to 0 and stopping all activity for that cycle. This is done when a cycle has
categorically failed to satisfy $R_e$, due to the squandering of the various $G$-changes to which it has access. We gain through
this failure the correct definition of a value for one of the functionals $Gamma_j(C)$ or $Delta(C)$. A cycle is said to _act_
whenever it moves from one state to another. An exception to this is the transition from state~2 to state~3: this transition is made
purely for bookkeeping purposes.

Also, when (say) cycle $(j, k)$ acts and in doing so resets cycles to its right, we entirely discard any functionals $Gamma_l(C)$
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
    ( A(x) = Phi(E \; x) )[s_1] sand (restr(E, phi(x)) = ( restr(hat(Psi)(C join A join B), phi(x)) )[s_1]
  $
  [Note that if $s_1$ doesn't exist, we automatically satisfy the requirement.]

  If $G_(s_1)(k) = 1$ we jump straight to state~7 and follow the instructions there.

  Otherwise put $u = (hat(psi) phi(x))[s_1]$. Restrain $restr(A, u)$ and $restr(B, u)$, put $Gamma_j(C; k) = G_(s_1)(k) thin (= 0)$
  with use $gamma_j(k) = u$ and start cycle $(j, k+1)$ to run simultaneously. Advance to state~2.

+ Wait for a stage $t_1$ at which either
  + $restr(C_(t_1), u) neq restr(C_(s_1), u)$; or
  + $G_(t_1)(k) neq G_(s_1)(k)$.

  [Note that we do not wait for a stage $t_1$ at which $C_(t_1) neq C_(t_1 - 1)$, (or where there is similar change in $G$) but
   rather for a change from the situation at stage $s_1$. In either case, once we combine the various strategies using a priority
   tree (see @section2.2.3 below) #stalpha is not "accessible" at every stage. There may be times at which a relevant $G$- or
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
  cannot enumerate its witness into $A$, as the $G$-change it needs has already come and gone.  Although it is possible that $(j,
  k)$ will be able to succeed in this manner, it is improbable. More likely is that cycle $(j, k)$ will be eventually stuck in state
  2, waiting forlornly for an impossible $G$-change, but in the meantime computing a correct value for $Gamma_j(C; k)$. We may as
  well cut our losses and simplify by abandoning this cycle: we content ourselves with the modest gain of a single correct value for
  $Gamma_j(C; k)$ and the knowledge that if we end up permanently abandoning _all_ cycles like this, we'll be able to compute $G$
  from $C$ (see #lemmaRef(<lemma2.17>) below), a contradiction.

+ We only reach _this_ state if it is similarly safe to set $Delta(C\; j) = 1$ with use 0. Do so, unless it has already been done.
  We permanently abandon the whole of row $row(j)$, and since there is no need to keep any of this row in business, it is convenient
  for technical reasons to reset every cycle in row $row(j)$, put cycle $(j, 0)$ into stage 8, and start cycle $(j+1, 0)$.

  The same comments as in state~7 just above apply here, but the result of the failure of cycle $(j, k)$ is even more stark. Now we
  have defined a correct value for $Delta(C; j)$, and have seen (and "wasted") the only change in $G(j)$ that will ever occur. Thus
  all cycles which rely on a change in $G(j)$ at some point are our of luck in the future, and we may as well not bother with
  them. These cycles include _all_ of row $row(j)$, which is why we permanently abandon this whole row. We content ourselves now
  with the single correct value $Delta(C\; j)$.

=== The basic module for $P_e$

The $P_e$ requirements are simpler than those of the first kind, and we implement a standard diagonalization approach to satisfy
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
  (hat(Theta)(C join A\; y))[s_2] = B_(s_2)(y) = 1 neq 0 = B_(s_1)(y) = (hat(Theta)(C join A\; y))[s_1].
  $
  By the restraint on $A$, $restr(A_(s_2), u) = restr(A_(s_1), u)$ so we must have $restr(C_(s_2), u) neq restr(C_(s_1), u)$.
  This change in $C$ allows us to redefine $Xi(C\; k)$, which we do after advancing to state P4.

+ It is now safe and correct to define $Xi(C\; k) = 1$ with use 0. Do so, unless this has already been done, permanently abandon
  cycle $k$, and start cycle $k+1$.

  [This is just like state~7 in the basic module for the $R_e$ requirements.]

// TODO: hacky (see above)
#show: doc => setupenum(doc)

=== Combining the modules <section2.2.3>

Now that we have described the strategy for satisfying a single requirement in isolation we must consider how to satisfy all
requirements simultaneously. Since each strategy may well act infinitely often we must use a _priority tree_ to manage this. The
standard reference for this technique is Chapter XIV of Soare @Soare1987.

#let outcome = $concatone(alpha, (j, k))$

In @LaForte LaForte introduced a path restraint to deal with a problem in the original construction in @CLW1989. Basically, that
construction worked the tree angle in an "obvious" way. As soon a #stalpha's cycle $(j, k)$ became "active" we use #outcome
as the outcome; this happens as soon as cycle $(j, k)$ chooses a witness. (For the moment the consider the case of
$R_e$-strategies.) However, if cycle $(j, k)$ later sees a relevant computation converge and imposes a restraint $r$, those
strategies in the subtree below #outcome started in the meantime will not have chosen witnesses to respect this new restraint. This
is naturally a Bad Thing. LaForte ingeniously solves the problem by introducing the path restraint: as the new restraint is imposed
it is incorporated into the path restraint for strategies below #outcome and respected "after the fact."  Strategies below #outcome
constantly check the extent of the path restraint being imposed on them.

#let outcome = none

This method works fine, as seen in @LaForte. However, it not particularly pretty. In particular, the point of tree-based arguments is
to remove the need for strategies to themselves keep an eye on the restraints set by other strategies. If possible, we would like to
avoid the path restraint, and there is a simple trick that lets us do so. We only follow a child corresponding to cycle $(j,k)$ when
cycle $(j, k)$ has actually imposed a restraint. Until that happen we follow a child corresponding to the rightmost cycle to the
left of $(j, k)$ which imposes restraint. This is perfectly safe, as, so long as $(j, k)$ imposes no restraint, we cannot injure any
computations by letting the strategies below the leftward cycle operate. Once such a restraint is imposed, we automatically respect it
by starting to follow a child corresponding to $(j, k)$. The only trick we actually need is to add a new child,
$concatone(alpha, -1)$, to be followed when no cycles at all of #stalpha impose a restraint.

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
parameter, once defined, keeps that value until it is redefined or undefined.

The construction proceeds as follows.

Stage 0: #h(1em) All parameters are undefined or $emptyset$ as appropriate, and all cycles are in state 0 or state P0.

#let nextval = $f_(s+1)(t)$
Stage $s+1$: #h(1em) We define, in substages $t < s$, a finite path $nextval$ through the tree, of length $s$. So, suppose $alpha =
(restr(nextval, t)) in T$ is defined. If no cycle of #stalpha has been started since $alpha$ was last cancelled, start
$alpha$'s cycle $(0, 0)$ or $0$, as appropriate, and put $nextval(t) = -1$.

Otherwise, first suppose that $|alpha|$ is even, so that $alpha$ is using an $R_e$ strategy. Allow any cycles of #stalpha
able to make the transition from state~2 to state~3 do so. Now there are 2 cases.
- #smallcaps("Case 1") #h(1em) Some least cycle $nu$ of #stalpha is able (or forced by a $C$-change) to act.

We allow cycle $nu$ to act. Let $lambda$ be the rightmost cycle of #stalpha now imposing restraint
(if there is any such cycle.) It is not necessarily the case that $lambda = nu$. If cycle $lambda$ is now in state~2, 3, or 4 then put
$nextval = (lambda, 1)$. If instead, $lambda$ is in stage 5 or 6 then put $nextval = (lambda, 2)$. Cancel all strategies
$beta$ with $concatone(alpha, nextval) <_L beta$. If $lambda = nu$ and the action of cycle $nu$ involved enumerating a number into
or out of $A$ or into $B$ we also cancel all strategies $beta supset concatone(alpha, nextval)$.

If there is no such cycle $lambda$ then put $nextval = -1$ and cancel all strategies $beta$ with $concatone(alpha, -1) <_L beta$.

- #smallcaps("Case 2") #h(1em) No cycle of #stalpha is able, or forced, to act.

We do nothing, and nothing needs to be cancelled. Define $nextval$ just as above. No strategies need to be cancelled.

If $|alpha|$ is odd, then we behave similarly. Now, given the rightmost cycle, $lambda$, imposing restraint, we simply put
$nextval = lambda$, rather than worrying about two kinds of restraint.

If $t + 1 < s$ we advance to substage $t + 1$.

We say that the strategies $alpha subset f_(s+1)$ are _accessible_ at stage $s+1$.

== Verification

The verification of the construction is a long and tedious one, and is broken up into a sequence of lemmas. As the arguments for the
two types of module are of necessity quite different, for the first part of the verification we discuss the modules separately.

We will refer to the parameters associated with cycle $nu$ of #stalpha as they are defined at stage $s$ like so:
$u_s(alpha, nu)$, $v_s(alpha, nu)$, _etc_. When the strategy is clear from context (as it usually will be), we will drop it.

=== Lemmas for the $R_e$ strategy <section2.3.1>

==== The layout of the cycle states

We begin with a sequence of lemmas which describes the different arrangements possible of the states of the various cycles at any time.
The aim is to formalize the intuitive ideas that develop from an understanding of the way the construction works.

We assume that we have a certain, fixed strategy, $alpha$, of even length in mind, and that all cycles mentioned belong to this
strategy. Also, we ignore the fact that #stalpha may not be accessible at all (or even all sufficiently large) stages: we
just treat the stages mentioned as being the successive ones at which #stalpha _is_ accessible.

It will be convenient to refer to a cycle with is in either stage 5 or state~6 as being "in state~5/6".

#lemma[
    For any row $row(j)$, at most one cycle $(j, k)$ is in state~5/6.
    <lemma2.3>
]
#proof[
    We show that if cycle $(j, k)$ is in state~5 or state~6 at stage $s$ then nothing to the right of $(j, k)$ in row $row(j)$
    (namely, a cycle $(j, k') > (j, k)$) is in either of these states at stage $s$.

    If cycle $(j, k)$ entered state~5 from state~4 (and there is no other way), no cycles to the right of $(j, k)$ are in any state
    other than 0 at the start of stage $s$, because by entering state~4, cycle $(j, k)$ reset every cycle to its right, and no new
    cycles were started so long as $(j, k)$ remained in state~4. Upon entering state~5, cycle $(j, k)$ starts cycle $(j+1, 0)$,
    and no cycle to the right of $(j, k)$ in row $row(j)$ is started so long as $(j, k)$ stays in state~5.

    On entering state~6, cycle $(j, k)$ resets every cycle to its right (including those in rows $row(j')$ for $j' > j$), and no
    cycle to its right will be started so long as $(j, k)$ remains in this state.
]

// p.14
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
    cycle $(j, k')$ would be reset. We may may immediately discount the possibility that $(j, k dubpr)$ is in state~7,
    because a cycle in this state cannot act. Thus, as stage $t$ starts, cycle $(j, k dubpr)$ is in state~2 or state~3.

    We first claim that $(j, k dubpr)$ can't make the transition from state~2 to state~1. Indeed, such a transition indicates a change
    in $restr(C, u(j, k dubpr))$. But cycle $(j, k')$ starts after cycle $(j, k dubpr)$ enters state~2, so by construction,
    $v_t(j, k') > x(j, k') > u(j, k dubpr)$, and we have a change in $restr(C, v_t(j, k'))$ at stage $t$, which is a contradiction.

    Cycle $(j, k dubpr)$ can't go from state~2 to state~3 at stage $t$, as this does not count as an action, so the only remaining
    possibility is the $3 arrow.r.bar 4$ transition, so that there is a change in $restr(C, mu_t(x(j, k dubpr)))$.
    We claim that $mu_t(x(j, k dubpr)) = v_t(j, k')$, and obtain the contradiction of a change in $restr(C, v_t(j, k'))$.

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

Consider a stage $s$, and the states that all the various cycles of #stalpha are in at the end of stage $s$.  We will call
this arrangement the _pattern of #stalpha at stage $s$_, and denote it by $pattern(s) = pattern(s)(alpha)$.  The notation
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

The claim is now that if #stalpha has been started since last being cancelled, its pattern in "valid":
#lemma(name: "Pattern Lemma")[
    If #stalpha has at least one cycle not in state 0 at stage $s$, $pattern(s) in validPattern$.
    <patternLemma>
]

#proof[
    #let angle8 = angletup(8)
    We proceed by induction on the number of stages since the last time #stalpha had a cycle started after previously being
    cancelled.

    When a strategy is started up (perhaps not for the first time), as stage $s$, cycle $(0, 0)$ is started. If this cycle, or row
    $row(0)$, has been abandoned before, subsequent cycles are automatically started as well in the cascading effect mentioned at
    the start of @basicModuleRe. Let $j = min_iota{ "row" row(iota) "never abandoned" }$,
    and let $k = min_kappa { "cycle" (j, k) "never abandoned" }$. Then the pattern at stage $s$ is
    $
      pattern(s) = angletup(angle8, angle8, dots, angle8, angletup(7, 7, dots, 7, 1)_(k+1))_(j+1).
    $
    This is a valid pattern, as $angle8 in prelimRow$ and $angletup(7, dots, 7, 1) in uncrampedRow subset finalRow$.

    Now suppose that $alpha$'s pattern is valid coming into stage $s$, that #stalpha is not cancelled at $s$, and that something
    actually happens: some cycle of the strategy changes state.  We let $pattern(s-1) = angletup(p_0, p_1, dots, p_n, f)$, where
    $p_i in prelimRow$ and $f in finalRow$. First consider any $2 arrow.r.bar 3$ transitions. These can occur only in a crampedRow,
    as only such rows have anything in state~5/6. But a 3 in place of a 2 leaves the type of crampedRow
    (either #patternName("prelim") or #patternName("final")) unchanged, so the pattern is still valid after such changes.  From now on let
    $pattern(s-1)$ represent the pattern after all $2 arrow.r.bar 3$ state transitions are taken into account, bet before any action is
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
       where $b' = 1$ or $b' = 4$ according to how the cycle
       // p.18
       acted. In either case, $f' in uncrampedRow$,
       and the new pattern for the strategy is $pattern(s) = angletup(p_0, dots, p_n, f')$ is still valid.

  + $j < n+1$. Row $row(j)$ can't ever have been abandoned, as otherwise no cycle it in could act, so
    the part of the pattern corresponding to #theRow($j$) is
    $p_j = angletup(h_0, dots, h_m, 5) in prelimCrampedRow$. Note that for $i leq m$, $h_i in {2, 3, 7}$.

    + $k = m+1$, so cycle $(j, k)$ is in state~5.

      If the action consists of returning to state~4, no cycles in row $row(j)$ to the left of
      $(j, k)$ can still be in state~3, by Lemmas #thmref(<lemma2.4>) and #thmref(<lemma2.5>).
      Thus $h_i in {2, 7}$ for $i < m+1$. The action resets all cycles to the right of $(j, k)$ (including
      those in rows $row(l)$, $l > j$), so the new pattern for row $row(j)$ is
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
// p.19
#lemma[
    For all $j$ and $k$, if cycle $(j, k)$ is in state~5 at stage $s$, then $(Delta(C\; j))[s] converge$.
    The same conclusion can be made if row $row(j)$ was abandoned at some stage before $s$.
    <lemma2.7>
]
#proof[
    If cycle $(j, k)$ is in state~5, we must have in particular $restr(C_s, v(j, k)) = restr(C_(s_2), v(j, k))$.
    But $v(j, k) = delta_(s_2)(j)$, so the computation for $Delta(C\; j)$ that was defined by cycle $(j, k)$
    when it entered state~5 is still defined.

    If, instead, row $row(j)$ was abandoned at some earlier stage, this abandonment was accompanied by
    a definition of $Delta(C\; j)$ with use 0. Such a computation can never become undefined, and must persist to stage $s$.
]

#lemma[
    If some cycle $(j, k)$ acts at stage $s$ to define a computation for $Delta(C\; j)$,
    then for each $i < j$, ($Delta(C\; i))[s] converge$.
    <lemma2.8>
]
#proof[
    Such a cycle can act in this way only by moving from state~4 to either state~5 or state~8. In either case,
    the pattern corresponding to row $row(j)$ coming into stage $s$ must have been an uncrampedRow.
    So, by the Pattern Lemma, for each $i < j$, the pattern for row $row(i)$ must either be angle8
    (indicating that row $row(i)$ was abandoned at some time) or an element of prelimCrampedRow. In the latter
    case, each row $row(i)$ has some cycle in state~5 as we enter stage $s$. But no cycle in any row $row(i)$, $i < j$
    acts at stage $s$, as otherwise cycle $(j, k)$ would be reset and unable to act. Thus the pattern of each of these rows
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
    Notice that we may assume that the strategy in question is not cancelled during
    any of the stages of interest to us in this lemma. If such a cancellation were to occur, all functionals
    associated with our strategy would be discarded and the lemma follows trivially.

    We proceed by induction. Assume that (I) and (II) hold for $0, 1, dots, j-1$.

    First note that when any cycle $(j, k)$ of $row(j)$ starts it chooses a witness $x(j, k)$ larger than
    any number mentioned so far. In particular, $x(j, k)$ is larger than the use of any $Delta(C\; i)$
    computation (for $i < j$) still defined when the witness is chosen. As the definition of such
    a new computation would involve the resetting of cycle $(j, k)$ (by the Pattern Lemma), $x(j, k)$
    will remain larger than the use of any currently defined $Delta(C\; i)$ computation. But
    if cycle $(j, k)$ ever defines a computation for $Delta(C\; j)$, then $delta(j) = v(j, k) > x(j, k)$
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
    // p.21
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
    $Gamma_j(C; i)$ with $i < k$ such that $gamma_(j,s)(i) geq gamma_(j,s)(k) > 0$. Let $t < s$ be the stage at which the current
    computation for $Gamma_j(C; k)$ was defined. By #lemmaRef(<lemma2.9>), $(Gamma_j(C; i))[t] converge$ and by the minimality of
    $s$, $gamma_(j,t)(i) < gamma_(j,t)(k) = gamma_(j,s)(k)$.  But the computation for $Gamma_j(C; i)$ valid at stage $t$ must get
    undefined before stage $s$, by the inductive hypothesis, so $restr(C_s, gamma_(j,t)(i)) neq restr(C_t, gamma_(j,t)(i))$ which
    implies $restr(C_s, gamma_(j,s)(k)) neq restr(C_t, gamma_(j,s)(k))$.  This means that the computation $(Gamma_j(C; k))[s]$
    actually becomes undefined at some stage between $t$ and $s$, a contradiction. This establishes (I) for $k$.

    Now suppose that (II) fails for k: at stage $s$ cycle $(j, k)$ defines $Gamma_j(C; k)$ but another
    computation, $(Gamma_j(C; k))[t]$, exists from an earlier stage $t < s$. Note that
    $restr(C_s, u_t(j, k)) = restr(C_t, u_t(j, k))$. Note also that $gamma_(j,t)(k) > 0$, since the definition
    of a computation of use 0 would lead to the permanent abandonment of cycle $(j, k)$ at stage $t$. This cycle
    would therefore be unable to act at stage $s$.

    Now, only cycle $(j, k)$ can define a computation for $Gamma_j(C; k)$. It cannot merely have returned to state~1 and again to
    state~2 between stages $t$ and $s$, as this requires a change in $restr(C, u_t(j, k))$. Neither can it advance from state~2 to
    state~7 between stages $t$ and $s$, as entering state~7 entails the same $C$-change. Thus in order to have another crack at
    // p.22
    defining $Gamma_j(C; k)$, cycle $(j, k)$ must be reset and later restarted. If ever something in row $row(i)$, for $i < j$,
    acts, the functional $Gamma_j(C)$ is discarded wholesale, preventing any conflicting definition
    at stage $s$. So, at some stage $t' in (t, s)$ some cycle $(j, k') < (j, k)$ acts, resetting $(j, k)$
    (if it hadn't been reset since stage $t$ already.) By #lemmaRef(<lemma2.9>), $(Gamma_j(C; k'))[t'] converge$ and by part (I)
    $gamma_(j,t')(k') < gamma_(j,t')(k)$. Before #stg($s$) #cycle($(j, k')$) must restart #cycle($(j, k' + 1)$), and at the same
    time define a new computation for $Gamma_j(C; k')$. But by the inductive hypothesis the previous such computation
    (_i.e._ that valid at stage $t$) must have become undefined. This means that there has been a change
    since stage $t$ in $restr(C, gamma_(j,t)(k')) subset restr(C, gamma_(j,t)(k))$. But $gamma_(j,t)(k) = u_t(j, k)$,
    so this is a contradiction.

    The lemma is proved.
]

=== Lemmas for the $P_e$ strategy <section2.3.2>

@section2.3.1 was a long and complicated one. As the $P_e$ strategy is so much simpler than the $R_e$ one,
the corresponding set of lemmas is also. We assume we have fixed a #stalpha of odd length. Again
we treat all stages mentioned as being the successive ones at which #stalpha is actually accessible.
We start by discussing the patterns that the cycle states can make. We again refer to the pattern at stage $s$
as $pattern(s)$.

As the $P_e$ strategy involves a one-dimensional array of cycles, the pattern formed by the cycle-states
in this case is simply a finite sequence of state-names. There is no need for the sequence of sequences
used in the $R_e$ strategy argument.

#let plabel(n) = $upright(P)#n$
Let $Y = {plabel(0), plabel(1), ..., plabel(4)}$. Using the same notation as in the definition of #validPattern we may
define a single subset of $finseq(Y)$:
$
  validPatternForP = setconcat(finseq({plabel(2), plabel(4)}), angletup({plabel(1), plabel(3)})).
$
We then have the following analogue to the Pattern Lemma.#footnote[We don't refer to this result as a "Pattern Lemma",
                                                                   as it is too simple to deserve a name.]

#lemma[
    If #stalpha has at least one cycle not in state #plabel(0) at stage $s$, $pattern(s) in validPatternForP$.
    <lemma2.12>
]
#show: doc => setupenum(doc, formats: ("I.", "1.", "a."))
#proof[
    If #stalpha is started at stage $s$, cycle 0 is started, perhaps having been abandoned in the past.
    Let $j = min_iota{ "cycle" iota "never abandoned" }$. Then the pattern at the end of stage $s$
    is $pattern(s) = angletup(plabel(4), dots, plabel(4), plabel(1))_(j+1) in validPatternForP$.

    Now suppose that $pattern(s-1)$, $alpha$'s pattern coming into stage $s$, was valid and that #stalpha
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
    If cycle $k$ is in state #plabel(2) or state #plabel(4) at stage $s$ then $fff(Xi, C, k)[s] converge$.
    <lemma2.13>
]
#proof[
    If cycle $k$ is in state #plabel(2) at stage $s$ then, in particular, $restr(C_s, u_t(k)) = restr(C_t, u_t(k))$
    where $t < s$ is the stage at which cycle $k$ last entered state #plabel(2). This means that $(Xi(C\; k))[t]$,
    the computation defined at $t$, is still valid at $s$.

    If cycle $k$ is in state #plabel(4) then it must have been abandoned at some earlier stage.
    The abandonment was accompanies by a definition of $Xi(C\; k)$ with use 0, so this computation must persist to stage $s$.
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
    As in Lemmas~#thmref(<lemma2.10>) and~#thmref(<lemma2.11>) we may assume that #stalpha is not cancelled during
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
    is not reset before stage $s$ it cannot reenter state~#plabel(1) before $s$. It must
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

    + $restr(f, (n+1))$ is cancelled only finitely often (note that $restr(f, 0) = emptyset$ is never cancelled);

    + #strat($restr(f, n)$) satisfies the requirement towards which it works; and

    + for all sufficiently large $C$-true stages $t$, $restr(f, (n+1)) subset f_t$.
    <prop2.16>
]

So, inductively assume 1, 2, 3, and 4 for $n = eta - 1$, and let $alpha = restr(f, eta)$. Fix a stage $s_0$
so large that $alpha$ is not cancelled after $s_0$, and for every $C$-true stage $t > s_0$, $alpha subset f_t$.

We say that #stalpha _acts finitely_ if there is a stage $s$ after which no cycle of $alpha$ every
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
    must eventually get permanently stuck in state~2 or state~3, or is abandoned.

    By #lemmaRef(<lemma2.4>) a cycle gets permanently stuck in #state(3) only if another cycle in its
    row gets permanently stuck in #state(5) or #state(6), which we have seen does not happen to row~$row(j)$.
    Thus in fact every cycle of row~$row(j)$ eventually gets permanently stuck in #state(2) or is
    abandoned in #state(7). In the latter case, $Gamma_j(C; k)$ is correctly defined to be
    $1 = G(k)$ with use~0. We claim that the cycles which get permanently stuck in #state(2) also
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
    Given s #stalpha, if $chi$ is the leftmost cycle of #stalpha to act infinitely
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
    let $nu$ be the leftmost cycle of #stalpha which acts infinitely often. By #lemmaRef(<lemma2.18>)
    choose $s > s_0$ large enough that cycle $nu$ is not reset after stage $s$ by the action of any $alpha$-cycles
    to its left. Suppose for the moment that $nu^-$ is the rightmost cycle of $alpha$ to the left of $nu$
    imposing restraint at stage $s$. (That is, suppose such $nu^-$ exists.) Note that cycle~$nu^-$ will never
    change state after stage $s$, and so will impose the same restraint forever more. Cycle $nu$ must return
    // p.27
    infinitely often either to #state(1)
    (at which time either $concatone(alpha, (nu^-, 1))$ or $concatone(alpha, (nu^-, 2))$ will be accessible
     as appropriate to the state in which $nu^-$ finds itself) or to
    state 4 (so that $concatone(alpha, (nu, 1))$ will be accessible.)
    If there is no such $nu^-$ then the respective cases find $concatone(alpha, -1)$ and $concatone(alpha, (nu, 1))$
    accessible.

    If $|alpha|$ is odd then the argument similar, simpler, and omitted.
]

This establishes part 1 of the Proposition for $n = eta$ and we may assume that there is a value, $epsilon$, for $f(eta)$.  We write
this value variously as $epsilon = (nu_eta, i_eta)$ (for some $nu_eta in omega^2$ and $i_eta in {1, 2}$, if $|alpha|$ is even),
$epsilon = nu_eta in omega$ (if $|alpha|$ is odd), or $epsilon = -1$ (if appropriate). If there is a cycle of
#stalpha which acts infinitely often then we denote the leftmost one by $nu^+$.

It will be convenient to make the following definition. If $|alpha|$ is even and $i = 1$ or~2, then
we say that cycle $nu$ of #stalpha is _lacking for $i$ at stage~$s$_ if, at that stage,
cycle $nu$ imposes less restraint than is indicated by an outcome of $(nu, i)$. That is, if $i = 1$
and $nu$ imposes no restraint at stage $s$, or if $i = 2$ and $nu$ imposes only the restraints
$restr(A, u)$ and $restr(B, u)$. If $|alpha|$ is odd then we say that cycle $nu$ is _lacking at stage~$s$_
if it imposes no restraint at that stage.

#lemma[
    Suppose that $nu_eta$ is defined (that is, $epsilon neq -1$).
    If $|alpha|$ is even then $nu_eta$ is lacking for $i_eta$ at only finitely many stages.
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
     (if there is such a $nu_eta^-$ as defined in the proof of #lemmaRef(<lemma2.19>)) or $concatone(alpha, -1)$
     is accessible infinitely often. Both of these contradict the definition of $nu_eta$.

    + $i_eta = 2$ and $nu_eta$ is infinitely often in a state numbered less than 4.

     Once cycle $nu_eta$ reaches #state(4) it can only return to a lower numbered state by being reset.
     But by definition this cycle is not reset after state~$s$, so the only way it can infinitely often
     be in a state numbered less than 4 is if it never reaches #state(4). This contradicts the definition of $i_eta$.

    In the case $|alpha| = 2e + 1$ the argument is again similar and simpler.
]

#lemma[
    $restr(f, (eta + 1)) = concatone(alpha, epsilon)$ is cancelled only finitely often.
    <lemma2.21>
]
#proof[
    If $alpha$ acts only finitely, then $concatone(alpha, epsilon)$ is certainly not
    cancelled after the last time any cycle of #stalpha acts.

    Otherwise, we note that by assumption $alpha$ is cancelled only finitely often, so
    after stage $s_0$, $concatone(alpha, -1)$ is never cancelled. For other possible
    values of $epsilon$, $concatone(alpha, epsilon)$ is cancelled only when

    #show: doc => setupenum(doc, formats: ("1.",))
    + cycle $nu_eta$ is lacking for $i_eta$ (or just lacking, if $|alpha|$ is odd); or

    + cycle $nu_eta$ of #stalpha enumerates something into or out of $A$,
      or something into $B$.

    By #lemmaRef(<lemma2.20>) cancellations of the first kind happen only finitely often.

    We claim also that cancellations of the second kind can happen only finitely often.
    By #lemmaRef(<lemma2.20>) choose $s > s_0$ so large that $nu_eta$ is not lacking for $i_eta$
    (or just lacking) after stage~$s$. In particular, cycle $nu_eta$ is not reset after stage~$s$,
    as in being reset it would (temporarily) be lacking. Thus $eta_nu$ works only with its final witness, $x$ (resp.~$y$),
    after $s$. But the worst $nu_eta$ can now do is enumerate $x$ into $A$ and out again (or into $B$) once.

    Thus $concatone(alpha, epsilon)$ is cancelled only finitely often.
]

This establishes part 2 of the Proposition for $n = eta$.

#lemma[
    #stalpha satisfies the requirement towards which it was working.
    <lemma2.22>
]
#proof[
    By Lemmas #thmref(<lemma2.17>), #thmref(<lemma2.18>), and #thmref(<lemma2.21>) we have just two possibilities.

    #show: doc => setupenum(doc, formats: ("1.",))
    + Only finitely often does any cycle of #stalpha act.

    + Either $epsilon neq -1$ and cycle $nu^+$ acts infinitely often, but is only reset finitely often,
      or $epsilon = -1$ and cycle $(0, 0)$ (resp. 0) returns infinitely often to #state(1) (resp. #state(plabel(0))).

    We start with the argument for $|alpha| = 2e$.

    In the first case, some cycle gets permanently stuck in #state(1), #state(4), or #state(6). In any of these cases,
    we satisfy the requirement through a successful diagonalization.

    In the second case, let $sigma = nu^+$ if $epsilon neq -1$, and $sigma = (0,0)$ otherwise. Let $s > s_0$ be
    large enough that cycle~$sigma$ is not reset after stage~$s$, so that it works with the same witness, $x$, after~$s$.
    The only way that cycle $sigma$ can act infinitely often is if it alternates infinitely
    between states~1 and~2, or (if $epsilon neq -1$) between states~4 and~5. This implies that at least one of
    $Phi_e(E_e)$ and $Psi_e(C join A join B)$ is partial.

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

Naturally, #lemmaRef(<lemma2.22>) describes what "really" happens to #stalpha: the construction
of $Gamma_j$ and $Delta$ is only a threat to ensure that we get $G$-changes when we need them, and not too
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

    Now, if $nu^+$ remains in #state(2) at a $C$-true stage $t > q$ then it will never subsequently
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
then either #stalpha is accessible at stage~$t$, or is cancelled before ever being accessible
again. This allows us to get a handle on the delayed permitting nature of the argument.

#lemma[
    Suppose that $t > s^(concatone(alpha, nu))$ is a $C$-true stage, and that $alpha$'s cycle $nu$ is in a state
    other than 0, 1, and~4 (if $|alpha|$ is even), or a state other than #plabel(0) and~#plabel(1) (if $|alpha|$ is odd).
    Then if cycle $nu$ does not act at stage $t$ it will never act subsequently without first being reset.
    <lemma2.24>
]
#proof[
    We consider the case $|alpha| = 2e$. The case $|alpha| = 2e + 1$ is much the same, and simpler, as we don't have to worry
    about the parameter~$mu$.

    We immediately dispense with the case in which $nu$ is in #state(7) or #state(8) at stage~$t$, as by construction such
    a cycle needs to be reset to act again. Thus $nu$ is in #state(2), 3, 5, or~6.

    Since $t$ is $C$-true, $nu$'s failure to act at $t$ due to a $C$-change
    (so as to make a state-transition #trans(2, 1), #trans(3, 4), #trans(5, 4), or #trans(6, 7))
    means that such action is also impossible in the future.
    Also, $t > s^(concatone(alpha, nu))$, so (writing $nu = (j,k)$), ${j, k} sect G = {j, k} sect G_t$,
    and so by stage~$t$ cycle~$nu$ will have seen all of the explicit $G$-permission it will ever see.
    Finally, if $nu$ makes the transition #trans(2, 3) at stage~$t$, then the value of $mu$ just calculated
    is based on some computations in some cycle to the right, and these computations will never be subsequently injured by
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

    Suppose cycle~$nu$ of #strat($beta$) is reset at some $tau in (s, s']$. As $beta$ isn't cancelled at $tau$,
    $nu$ is reset by the action at $tau$ of some cycle $nu' < nu$ of #strat($beta$). By construction,
    this leads to the cancellation of node $beta^+$.

    (In what follows it will be convenient to refer to a cycle which is not in #state(0) or #state(plabel(0))
     as _awake_. Cycles in #state(0) or #state(plabel(0)) are _asleep_.)

    So it remains to consider the case in which $nu$ is not reset at any $tau in (s, s']$. The following
    argument applies necessarily to the case $|alpha| = 2e$. The case $|alpha| = 2e + 1$ is much the same.
    It is also simpler because we do not have to worry about the parameter~$mu$.

    Write $nu = (j, k)$. $beta^+ = concatone(beta, nu) subset f_s$, so cycle $nu$ is awake at stage $s$.
    As it is not reset in $(s, s']$ it remains awake during this period, and in particular is awake at
    stage~$t$. But $beta^+ subset.not f_t$, so some cycle to the right of $nu$ must also be awake at $t$.
    This means that $(j, k)$ must be in one of the states 2, 3, 5, 7, or~8 by the Pattern Lemma.
    Now, $t > s^alpha geq s^(beta^+)$, so we may apply #lemmaRef(<lemma2.24>) to see that cycle~$nu$
    does not act before being first reset. As it is not reset in $(s, s']$, it cannot act at or before $s'$,
    and $concatone(beta, (j, k)) subset.not f_(s')$, a contradiction.

    If, instead, $beta^+ = concatone(beta, -1) subset alpha$, assume that $beta^+ subset.not f_t$. This means
    that, at stage $t$, some (leftmost) cycle~$chi$ of #strat($beta$) is imposing restraint $r$. As $t$
    is $C$-true this restraint is based on computations which will never be injured by a later $C$-change.
    Thus $chi$ will always impose at least $r$-much restraint unless #strat($beta$) (and hence #strat($beta^+$))
    is cancelled. Thus, if $beta^+ subset f_(s')$ then #strat($beta^+$) is cancelled by stage~$s'$.
]

Now we can show that the permitting works.

#lemma[
    $A join B leqt G$.
    <lemma2.26>
]
#proof[
    Let $x in omega$. If $x$ is not chosen as a witness by stage~$x$ then it never will be, and $x in.not A union B$.
    Otherwise, suppose $x$ is chosen at stage $s_0$ to be the witness for a cycle $nu = (j,k)$ of #stalpha
    of even length. Note that $alpha subset f_(s_0)$, and that $x in.not B$.

    If $k in.not G$ or $G_(s_0)(k) = 1$ then $alpha$'s cycle~$nu$ will never get the first permission that it needs,
    and $x in.not A$.

    Suppose now that $k in setdiff(G_s, G_(s-1))$. Let $t$ be the first $C$-true stage larger than each of
    $s$, $s_0$, and $s^(concatone(alpha, nu))$. We claim that if $x$ is not enumerated into $A$ by stage $t$
    it never will be. Well, if $alpha subset.not f_t$ then by #lemmaRef(<lemma2.25>) #stalpha will be
    cancelled (and witness $x$ forgotten) before $alpha$ gets a chance to act again. So if $x$ hasn't entered $A$
    before~$t$, we must have $alpha subset f_t$ if $x$ is ever to have a chance. If some cycle $(j', k') < nu$
    of #stalpha acts at $t$ then cycle~$nu$ will be reset, and its witness forgotten. Otherwise, if cycle $nu$
    acts at or after stage~$t$ due only to $Eq(x, s_1)$ holding, then certainly $x in.not A$, as by construction
    cycle~$(j,k)$ will jump straight to #state(7) rather than attempt to enumerate $x$ into $A$. If $nu$ is in #state(4)
    // p.32
    at stage~$t$ then $x$ would have already entered $A$.  So we may assume that cycle~$nu$ is in a state
    other than 0, 1, or~4 at stage~$t$, and by #lemmaRef(<lemma2.24>) is unable ever to act again without getting
    reset first.

    So if $x in.not A_t$, $x in.not A$.

    If $x in A_t$ we must check to see if $x$ ever gets removed from $A$. If $j in.not G$ then cycle $nu$ will never
    see the necessary permission, and $x in A$. Otherwise, let $j in setdiff(G_w, G_(w-1))$. Let $t'$ be the first
    $C$-true stage greater than both $t > s^(concatone(alpha, nu))$ and $w$. The same reasoning as before
    shows that $x$ will have been removed from $A$ by stage $t'$ if it ever will be.

    Thus $A(x) = A_w(x)$.

    If $x$ is chosen at $s_0$ to be a witness for cycle $k$ of #stalpha of _odd_ length then the same
    basic argument applies, but now we need not worry about $x$ being enumerated out of $B$: we just check if it
    ever gets enumerated in.

    All of the above can be done by asking questions of a $C$ oracle and a $G$ oracle. As $C ltt G$, a $G$ oracle
    suffices, and $A join B leqt G$.
]


////////////////////////////////////////
// Chapter 3
// p.33

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
    such that for all $i geq 0$, $F ident.not_T A_i$.
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
    Given any nonrecursive, r.e. set $G$ there is a $dreInAbove(G)$ set $F$ not of d.r.e. degree.
    <theorem3.5>
]
This result has been strengthened by Hinman, @Hinman:
#theorem[
    Given a nonrecursive, r.e. set $G$ there is a $dreInAbove(G)$ set $F$ not of 3-r.e. degree.
    <theorem3.6>
]

Can we avoid 4-r.e. degrees _via_ $dreInAbove(G)$ sets in this way? $n$-r.e. degrees in general?
We cannot answer these questions at the moment. However, if we drop the requirement that
the constructed set be Turing-above $G$, we can avoid $n$-r.e. degrees, and at the same time
place the "base set" $G$ (which we now call $D$) in a prescribed r.e.~interval.
#theorem[
    For any $n in omega$ and any r.e.sets $C ltt G$ there is r.e. $D in turinginterval(C, G)$
    and $dreInAbove(D)$ $F$ such that $F$ is not of $n$-r.e. degree.
    <theorem3.7>
]
Note that $D leqt F$, but we do not know whether or not we can ensure $G leqt F$.

This result is in some sense a middle point between Theorems~#thmref(<theorem3.1>) and~#thmref(<theorem3.4>).
We maintain some control over the base set by allowing more flexibility in the construction of $F$ from it.


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

Where the structure $D = C join A$ is important, we will write it out in full.
In other places we will just use $D$.


=== The basic module <section3.2.1>

The construction used to satisfy the requirements is (loosely) based on the basic module given in @CLW1989.
It is similar to the module in #chapRef(2). The strategy for a single requirement consists of a
// p.35
(potentially unbounded) number of cycles, each of which makes a very simplistic attempt
to satisfy the requirement. We argue that if no cycle succeeds then we have $G leqt C$, a contradiction.

So, fix $e in omega$. We describe the strategy for satisfying requirement $R_e$. To simplify notation
we write $angletup(R, Phi, Psi)$ for $angletup(E_e, Phi_e, Psi_e)$.

In #chapRef(2) we avoided an r.e.~opponent by changing our constructed set twice. When avoiding
a 4-r.e. set we must change our set 5 times. This is not as bad as it seems as we have sweeping
powers over the set, $F$, we construct. Firstly, $F$ is (the join of an r.e.~set with) the difference
of two r.e.[$D$] sets, and membership of individual numbers in such sets may change
many times during a construction due to changes in $D$. Furthermore, $D = C join A$ and we have complete control
over $A$. This will allow us to eject elements from $udvd$ with great flexibility.

Now, as we wish to ensure $A leqt G$ we must ask for $G$-permission each time we put an element into~$A$.
It turns out that in the $n = 4$ case we must do this twice, which leads to a two dimensional cycle layout, as in #chapRef(2).

Thus, the strategy consists of an $(omega^2)$-sequence of cycles ordered lexicographically. Cycle $(0,0)$ starts first.
Cycle $chi = (j, k)$ may start $(j, k+1)$ and $(j+1, 0)$ as well as stopping all cycles $> chi$.
Cycle $chi$ may define the values $Gamma_j(C; k)$ and $Delta(C\; j)$.
Again we refer to rows of cycles, $row(j) = {(j,k) st k in omega}$.

Cycles may declare various numbers to be _levers_. These are used when we want to remove some some element, $x$, from $V^D$.
When $x$ is enumerated into $V^D$ we choose some new large element, $lambda$, not already a member of $D$
(actually, not a member of $A$, over which we have control) and put $x$ into $V^D$ with an $A$-use that is larger than $lambda$.
When it comes to remove $x$ from $V^D$ we "pull the lever": we enumerate $lambda$ into $A$, thus ejecting $x$ from $V^D$.

Each cycle begins in #state(0). A cycle is _started_ by letting it pass from #state(0) to another state,
as determined by its history in much the same way as in #chapRef(2); we have the same cascading effect.
A cycle is _reset_ by putting it back into #state(0), returning its restraints to 0 and undefining its
parameters $x, u, tilde(u), v, tilde(v), lambda^1(x)$, and $lambda^2(x)$.
A cycle is _abandoned_ by returning its restraints to 0 and stopping all activity for that cycle. This is done in much
the same situations as in #chapRef(2): a cycle has failed to satisfy $R_e$.
A cycle is said to _act_ whenever it moves from one state to another, except in the case of the bookkeeping
transition from #state(4) to #state(5).

Cycle $chi = (j, k)$ proceeds as follows.

#show: doc => setupenum(doc, formats: ("1.", "(i)",))
0. Until given the go-ahead, do nothing. When told to start, if $k=0$ or row $R_j$ has previously been abandoned _in toto_,
   advance directly to #state(11) and follow the instructions there. Otherwise, check if cycle $chi$ has been abandoned
   in the past. In this case jump straight to #state(10) and follow the instruction there. Otherwise, choose a witness~$x$,
   // p.36
   larger than any number mentioned in the construction so far, including all currently defined $(udvd)$-restraints,
   and larger than both $j$ and~$k$. Advance to #state(1).

+ Let $Eq(x, s)$ denote the condition
  $
    ((udvd)(x))[s] = (Phi(E\; x))[s] #h(1fr) \ #h(1fr)
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
  Note that the change in $C$ automatically ejects the witness $x$ from $U^D$.

  If we have (ii) let $v = (hat(psi)phi(x))[s_2] > u$, the total use of the
  $hat(Psi(C join A join udvd))$ computations at stage~$s_2$, and define $tilde(v) > tilde(u)$ analogously
  to~$tilde(u)$. Note that because of the enumeration at #state(1) info $(udvd)$ we have
  $(Phi(E\; x))[s_2] = 1 neq 0 = (Phi(E\; x))[s_1]$, so that $restr(E_(s_2), phi_(s_1)(x)) neq restr(E_(s_1), phi_(s_1)(x))$.
  Also note that by reaching this point we still have $restr(C_(s_2), tilde(u)) = restr(C_(s_1), tilde(u))$.

  We set
  $
    lambda^1(x) = (min lambda)[lambda > tilde(v) sand lambda > k sand lambda > s_2 sand lambda in.not A_(s_2) \
                               and lambda "is larger than any number mentioned in the construction so far"].
  $
  // p.37
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
  In case (ii), return to #state(2), setting the $(udvd)$-restraint to $u$, and the $A$-restraint to $tilde(u)$.
  In either of these cases we also discard our choice of the lever, $lambda^1(x)$.
  Note that in case~(i) (resp.~(ii)), $x$ has been ejected from both $U^D$ and $V^D$ (resp. from $V^D$)
  by the change in $C$.
  In either of these cases we also reset all cycles $> chi$.

  In case (iii) we have $restr(E_(s_3), phi_(s_1)(x)) = restr(E_(s_1), phi_(s_1)(x))$, so there is a
  $y < phi_(s_1)(x)$ such that $E_(s_3)(y) = E_(s_1)(y) neq E_(s_2)(y)$. Thus $E$ has changed (at least)
  twice on $y$ so far. Fix this $y$ in subsequent discussion.

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

  // p.38
  In cases (i) and (ii) we reset all the cycles $> chi$ and behave as we did in #state(3), returning to #state(1)
  or #state(2) as appropriate. We also declare $lambda^1(x)$ not to be a lever any more.

  In case (iii) we have two subcases, just as in #state(2) of the strategy for $R_e$-requirements in #chapRef(2):
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
    lambda^2(x) = (min lambda)[lambda > tilde(v) sand lambda > j sand lambda > s_4 sand lambda in.not A_(s_4) \
                               and lambda "is larger than any number mentioned in the construction so far"].
  $
  Declare $lambda^2(x)$ to be a lever and restrain $restr(A, lambda^2(x) + 1)$.
  (The restraint $restr((udvd), v)$ is still in place from before.)
  Enumerate $x$ into $V^(C join A)$ with $C$-use $tilde(v)$ and $A$-use $lambda^2(x) + 1$.
  // p.39
  This enumeration ensures that
  $
  (restr((C join A join (udvd)), u))[s_4 + 1] = (restr((C join A join (udvd)), u))[s_1].
  $
  Advance to #state(7).

+ Wait for a stage $s_5$ such that $Eq(x, s_5)$ holds. Now we have
  $restr(E_(s_5), phi_(s_1)(x)) = restr(E_(s_1), phi_(s_1)(x))$ so that
  $E_(s_5)(y) = E_(s_3)(y) = E_(s_1)(y) neq E_(s_4)(y) = E_(s_2)(y)$.
  $E$ has changed 4~times on $y$ and, being 4-r.e., can't change again. We want
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
  abandon cycle $(j, k)$, and start cycle $(j, k+1)$.

+ Arriving here means we can with confidence set $Delta(C\; j)$ with use~0.
  Do so, unless it has already been done, (permanently) abandon row $row(j)$, and start cycle $(j+1, 0)$.
  For technical reasons also reset every cycle in row $row(j)$ and put cycle $(j, 0)$ into #state(11).

=== Combining the modules

The basic modules are combined in much the same way as we used in #chapRef(2) with a tree.
However, there is a very important difference.

In #chapRef(2) a cycle could act infinitely often without being reset: it could bounce back and forth
between states 1 and~2, or between states 4 and~5. It was important in that construction
that such infinite action was not accompanied by any enumerations into or out of the sets
// p.40
under construction. The proof of #lemmaRef(<lemma2.21>) depended on this fact: after
a cycle is reset for the last time it can only cause finitely much enumeration.
In the present construction, however, this is not true. A cycle returning infinitely often
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

// p.41
#stage-hdr($s+1$) We defined, in substages $t < s$ a finite path $f_(s+1)$ through the tree, of length $s$.
Suppose $alpha = (restr(f_(s+1), t)) in T$ has been defined by substage $t-1$. If no cycle of #stalpha has been
started since $alpha$ was last cancelled then start $alpha$'s cycle $(0,0)$ and set $nextval = -1$.

Otherwise let any cycles of #stalpha able to make the transition from #state(4) to #state(5) do so.
Let any cycle forced solely by a $C$-change to change state do so. There are now two cases.
- #case(1) Some leftmost cycle $nu$ of #stalpha is able to act.

#let bigS = $sans(upright("S"))$
We allow cycle $nu$ to act. Let $lambda$ be the rightmost cycle of #stalpha now imposing restraint of some sort
(if there is such a cycle). Let $lambda$ be in state~#bigS (note that $bigS neq 0, 1, 10, 11$) and let $i$ be defined by
$
i = cases(
    1 quad & "if" bigS = 2\,,
    2      & "if" bigS = 3\, 4\, "or" 5\,,
    3      & "if" bigS = 6\,,
    4      & "if" bigS = 7 "or" 8\,,
    5      & "if" bigS = 9.
)
$
Now set $nextval = (nu, i)$. If there is no such cycle $lambda$ put $nextval = -1$.

In any case, cancel all strategies $beta$ with $concatone(alpha, nextval) <_L beta$.

- #case(2) No cycle of #stalpha is able to act.

We do nothing at this substage. Define $nextval$ just as above. There is nothing to cancel.

If $t + 1 < s$ we advance to substage $t+1$.

A node $alpha$ is _accessible_ at stage $s+1$ if $alpha subset f_(s+1)$.

One of the points of multiple outcomes for each cycle is to cope with the coming and going
of elements of $udvd$ as $C$ changes. It is important to observe that every time $concatone(alpha, (nu, i))$
($i = 1, 2, 3, 4, 5$) is accessible, $(udvd)(x(alpha, nu))$ is the same, where $x(alpha, nu)$ is the witness chosen by
cycle~$nu$ of #stalpha.

== Verification for $n = 4$ <section3.3>

At heart this construction is very like the one in #chapRef(2). We use the same mechanism
to avoid $Delta$-inconsistency, and the underlying aim is the same: change the constructed set
frequently enough that our opponent (previously an r.e.~set; here a 4-r.e.~set) cannot keep up with us.
As such, we would expect the verification to take largely the same tack. This is the case.

The verification argument given in #chapRef(2) is detailed#footnote[The less charitable reader may prefer another word.]
and it would please no-one to go through the same sort of thing again in its entirety. So, when an argument follows the
// p.42
same lines as the corresponding discussion in #chapRef(2) we will just indicate the essential modifications, if any.

As in #chapRef(2), we will refer to parameters associated with cycle~$nu$ of #stalpha as they are defined
at stage~$s$ like so: $u_s(alpha, nu)$, $lambda^1_s(alpha, x(nu))$.
Whenever it is made possible by context we will drop the strategy name.

=== Layout of the cycle states

We begin again with a description of the possible state-arrangements, and state a Pattern Lemma.
We assume we have a certain, fixed #stalpha in mind, and all cycles mentioned are assumed to belong
to it. As before, we regard the stages mentioned as being the successive ones at which #stalpha
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
it must reach either #state(10) (if it sees a change in $restr(C, tilde(v)_t(chi'))$ while in #state(8))
or #state(11) (if that $C$-change is seen while in #state(9)).
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
doesn't count as an action. The transitions~#trans(4,1) and~#trans(4,2) entail a change in $restr(C, tilde(v)_t(chi dubpr))$.
But $tilde(v)_t(chi dubpr) < tilde(v)_t(chi')$ since cycle~$chi'$ starts after $chi dubpr$ reaches #state(2)
and $tilde(v)_t(chi dubpr)$ is defined. Thus such a $C$-change is impossible.

// p.42
Thus, the only possible transition left is~#trans(5,6). That this is impossible follows from the same
argument as was used for the #trans(3,4) transition in #chapRef(2).
]

#lemma[
    Given $j$, if cycles $chi, chi' in row(j)$ are both in #state(5) at stage~$s$ then
    $(mu(x(chi)))[s] = (mu(x(chi')))[s]$.
    <lemma3.10>
]
#proof[
    As #lemmaRef(<lemma2.5>).
]

We are now ready to state the Pattern Lemma for this construction.

Let $X = {0, 1, dots, 11}$ and recall that for sets $M, N$ of finite sequences
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

As in #chapRef(2) we define by $pattern(s)(alpha)$ the cycle-state arrangement of the #stalpha at stage~$s$.
We also refer to the cycle arrangements of individual rows as "patterns".

#lemma[
    If #stalpha has at least one cycle not in #state(0) at #stg($s$), $pattern(s)(alpha) in validPattern$.
    <lemma3.11>
]
#proof[
    The arguments are very similar to those in the corresponding proof in #chapRef(2), and consist of an exhaustion of cases.
    The same follow-your-nose approach works just fine; nothing is to be gained by repeating it.
]

=== Consistency of the functions $Gamma_j(C)$ and $Delta(C)$

Now we prove the consistency of the constructed functions $Gamma_j(C)$ and $Delta(C)$.
The proofs need little beyond the corresponding ones in #chapRef(2). The only change necessary is typically
// p.44
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
    If some cycle $(j, k)$ acts at #stg($s$) to define $Delta(C\; j)$ then for each
    $i < j$, $(Delta(C\; i))[s] converge$.
    <lemma3.13>
]
#proof[
    As #lemmaRef(<lemma2.8>).
]

Similarly we have
#lemma[
    If some cycle $(j, k)$ acts at #stg($s$) to define $Gamma_j(C; k)$ then for each
    $i < k$, $(Gamma_j(C; i))[s] converge$.
    <lemma3.14>
]

The consistency of $Delta(C)$ and $Gamma_j(C)$ are proved just as they were in #chapRef(2).
#lemma[
    For all $j in omega$, row~$row(j)$ defines a computation for $Delta(C\; j)$ only when no
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

    + $restr(f, (n+1))$ is cancelled only finitely often (note that $restr(f, 0) = emptyset$ is never cancelled);

    + #strat($restr(f, n)$) satisfies requirement $R_n$;

    // p.45
    + for all sufficiently large $C$-true stages $t$, $restr(f, (n+1)) subset f_t$.
    <prop3.17>
]

So, inductively assume 1, 2, 3, and 4 for $n = eta - 1$ and let $alpha = restr(f, eta)$.
Fix a #stg($s_0$) so large that $alpha$ is not cancelled after~$s_0$ and that for for every
$C$-true stage $t > s_0$, $alpha subset f_t$.
// This notation is mystifying. See github ticket #48
//, $rho(alpha, t) = liminf_s rho(alpha, s)$,
//and $tilde(rho)(alpha, t) = liminf_s tilde(rho)(alpha, s)$.

Recall that we say _$alpha$ acts finitely_ if there is a stage after which no cycle of #stalpha acts,
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
    Given a #stalpha, if $chi$ is the leftmost cycle of #stalpha to act infinitely often
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
We say that #cycle($nu$) of #stalpha is lacking for~$i$ at #stg($s$) if $nu$ is in #state(10)
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
    #stalpha satisfies requirement $R_(|alpha|)$. <lemma3.23>
]
#lemma[
    For all sufficiently large $C$-true stages $t$, $restr(f, (eta+1)) = concatone(alpha, epsilon) subset f_t$. <lemma3.24>
]

These results establish parts 2-4 of the Proposition and complete the inductive step.
#thmref(<prop3.17>)[Proposition] is proved. #qed


Thus all of the requirements are satisfied, and we have constructed r.e. $D gt.eq_T G$ and
two r.e.[$D$] sets $U^D$ and~$V^D$ such that $D join (udvd)$ is not of 4-r.e. degree.
It remains only to show that in fact $D leq_T G$. We use the same method as we did in #chapRef(2).

// p.46
For $alpha in T$ we set
$
e^alpha = max ( {j, l | (exists beta in T, i = 1, dots, 5)[concatone(beta, ((j, k), i)) subset alpha]})
$
the largest number which occurs in the path leading to $alpha$ and which may be called upon
by a cycle of some strategy on that path to be a witness to a $G$-change. We set
$
s^alpha = min { s | restr(G_s, e^alpha) = restr(G, e^alpha)}
$
and recall that $lambda alpha [s^alpha]$ is $G$-recursive.

#lemma[
    Suppose that $t > s^(concatone(alpha, nu))$ is a $C$-true stage, and that $alpha$'s cycle $nu$
    is in state 4, 5, 8, 10, or 11. Then if #cycle($nu$) does not act at #stg($t$) it will never act
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

We can now prove that the delayed permitting works.

#lemma[
    $A leqt G$.
    <lemma3.27>
]
#proof[
    Let $y in omega$. As the construction always picks levers to be larger than the current stage,
    if $y$ has not been chosen as a lever by #stg($y$) it never will be and $y in.not A$. Otherwise,
    suppose that $y$ is chosen at #stg($s_0$) to be a lever for cycle~$chi = (j,k)$ of #stalpha.
    Note that $alpha subset f_(s_0)$.

    Assume that $y$ is actually chosen as $lambda^1_(s_0)(x(chi))$. If $k in.not G$ or $k in G_(s_0)$
    then #cycle($chi$) will never get the $G$-permission it needs to enumerate $y$ into $A$ and $y in.not A$.
    Otherwise let $k in setdiff(G_s, G_(s-1))$ and let $t$ be the first $C$-true stage larger than each
    of $s_0$, $s$, and $s^(concatone(alpha, chi))$. We claim that $y$ is enumerated into $A$ by #stg($t$)
    or not at all, so that $G(y) = G_t(y)$.

    If $a subset.not f_t$ then by #lemmaRef(<lemma3.26>) #stalpha will be cancelled before
    being accessible again, and $y$ will be lost. If some cycle $chi' < chi$ of #stalpha acts
    at #stg($t$) then $chi$ will be reset and again $y$ will be lost.
    Otherwise, if $chi$ is in #state(1) or~2 at #stg($t$) then the lever~$y$ has already been discarded since being chosen,
    and will never get a chance after $t$ to be enumerated.
    If $chi$ is in #state(3) then, since $G_t(k) = 1$, $y$ will never be enumerated into~$A$.
    If $chi$ is in #state(6), 7, or~8 then by construction, $y in A_t$.
    Otherwise we apply #lemmaRef(<lemma3.25>) to see that #cycle($xi$) must act at #stg($t$)
    if it ever will without first being reset, and lever~$y$ is lost.

    // p.47
    If $y$ is chosen as $lambda^2_(s_0)(x(chi))$ the argument is similar, with $j$ replacing $k$.
]

== The cases $n > 4$ <section3.4>

The complications which arise as $n$ gets larger are of notation, rather than of approach.
When avoiding $n$-r.e. sets we must change our constructed set $n+1$ times, leading to
an $(n+1)$-dimensional cycle structure.
This leads to an increase in the number of times that we must ask for $G$-permission for the levers
corresponding to a given witness~$x$, and in the number of different functionals we construct.

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
// p.48
Well, most obviously, the cycle structure will now be an $(omega^3)$-sequence of cycles $chi = (j, k, l)$,
to accommodate the 3 layers of permission that we will (potentially) need for each witness.
Secondly, in addition to constructing functions $Gamma_j(C)$ and $Delta(C)$ we will need a third tier,
$Upsilon_(j,k)$ to handle the extra layer of $G$-permission.
With the extra dimension, we need a more general concept than "row".
In general, for the $n$-dimensional structure $omega^n$, we define an $(n-i)$-dimensional _slice_
by specifying the first $i < n$ components:
$
slice(c_1, dots, c_i) = {(c_1, dots, c_i, c_(i+1), dots, c_n) | c_(i+1), dots, c_n in omega}.
$

Just as before we had a $Delta$-protecting, "waiting" state, 5, which was used to prevent the over-eager
employment of $G$-changes leading to the inconsistent definition of $Delta(C)$, we must now have states
which protect both $Gamma_j$ and $Delta$.
Before, the trigger for entering #state(5) was the existence of some cycle of slice~#slice($j$) in state~8/9.
To allow us some abstraction, call this double state the _endgame for $Delta$_.
In the new construction, there will be endgames for $Gamma_j$ and $Delta$.
In each case, the endgame consists of the two states immediately following the definition
of $Gamma_j(C;k)$ and $Delta(C\; j)$, respectively, in which the functional value
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
// p.49
Every time an increase in $n$ requires the addition of an extra dimension to the cycle-structure
(that is, every time $n$ is increased from $2m-1$ to $2m$), we just "bolt" one to the front:
add an extra tier of functionals, with a corresponding waiting stage to protect all of the existing tiers.

== Further comments

As all of the strategies are self-contained, it does not hurt to combine strategies corresponding to different values of $n$, so
long as we associate their enumerations with different $dreInAbove(D)$ sets.  So, those strategies concerning themselves with
avoiding 5-r.e. degrees (say) work with the set $C join A join (setdiff(U^(D_5)_5, V^(D_5)_5))$, while those avoiding
13-r.e. degrees work with the separate $C join A join (setdiff(U^(D_(13))_13, V^(D_(13))_13))$. A description of the priority tree then
becomes more complicated (as different nodes will have different successor-sequences), but in principle the construction is no
different. Indeed, as all of the strategies for all $n$ can be combined, we can actually construct a single $D leqt G$ for which,
given $n$, there is a $dreInAbove(D)$ set not of $n$-r.e. degree: #theorem[ Given r.e. sets $C ltt G$ there is r.e. $D in
turinginterval(C, G)$ such that for all $n in omega$ there is a $dreInAbove(D)$ set $F_n$ not of $n$-r.e. degree.  <theorem3.28> ]
In fact, there is no need to keep enumerations for different values of $n$ separate: we can construct a single $dreInAbove(D)$ set
$F$ with is not $n$-r.e. for any $n$: #theorem[ Given r.e. sets $C ltt G$ there is r.e. $D in turinginterval(C, G)$ and a
$dreInAbove(D)$ set $F$ not of $n$-r.e. degree for any $n in omega$.  <theorem3.29> ]

It is also interesting to note that the sets $F_n$ we construct are just barely $dreInAbove(D)$.
In the construction, elements are only ever enumerated into $U^D$ once, at least modulo "unwanted"
ejections due to $C$-changes. In the absence of these $C$-changes the set $U^D$ would be
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
// p.50
put a bound, _before any cycle of the strategy starts_, on how many times we will have to flip-flop.

Consider what would happen here if we tried to construct $F = C join A join V^D$, an $reInAbove(D)$ set.
At our equivalent of #state(1) we would choose a lever $lambda^1(x)$ larger than $tilde(u)$
and enumerate $x$ into $V^D$ with use $lambda^1(x) + 1$.  Then, when we see $s_2$, the next stage of agreement,
with total use $tilde(v)$, we would (after waiting for permission) kick $x$ out of $V^D$ by pulling the
lever~$lambda^1(x)$. However, it is impossible for us to restrain $restr(A, tilde(v))$ from #stg($s_2$)
onwards, as we cannot be sure that $lambda^1(x) > v$. The very act of returning $V^D$ to its $s_1$ shape
may change $restr(A, tilde(v))$. Thus, instead of two anchor-points, we will only have one,
$restr(E_(s_1), phi_(s_1)(x))$, to which we can be sure of returning each time. Thus, while we can say each time that
$
restr(E_(s_("odd")), phi_(s_1)(x)) = restr(E_1, phi_(s_1)(x)) neq restr(E_(s_("even")), phi_(s_1)(x)),
$
there is no coordination between $E$ at the $s_("even")$
stages,#footnote[Of course, $s_("even")$ should in no way be confused with #[_s_]even or even _seven_.]
and we cannot be sure that $E$ changes on the same element each time.
Thus, instead of the number of changes in $restr(E, phi_(s_1)(x))$ that we must wait for being bounded in advance by~$n$,
we must allow $E$ (potentially) to change $n$ times on each element less than $phi_(s_1)(x)$. Thus, instead of
needing to change our constructed set $n+1$ times, we may need to change it
$m(x) = m(x, s_1) = (1 + n dot phi_(s_1)(x))$ times for the witness~$x$.
This bound is clearly not known before the cycle starts: we have to wait until stage~$s_1$ to find it.

This, of course, is where the problems start. Before, we knew that all the witnesses chosen by a given strategy
would be content with just $n+1$ changes and could therefore do with an $omega^(floor(n\/2))$ cycle structure.
Now, as we choose larger and larger witnesses for the various cycles, the potential number of times that we must seek
permission may grow without bound. This fact by itself does not make the construction impossible: we can
use $omega^(< omega)$ (ordered lexicographically) to organize our cycles, and we can speak of slices of all finite
dimensions. Define the _slice dimension_ of a #cycle($chi$) as the dimension of the smallest
slice containing $chi$ and all of its predecessors. Thus the slice dimension of cycle $(1, 1, 1)$ is 3, while
that of $(1, 0, 0, 0)$ is 4. Various cycles will now have varying (finite) numbers of internal states
(determined by each cycle dynamically as soon as $phi_(s_1)(x)$ is calculated), and the strategy
as a whole may have infinitely many different ones. There is now a fundamentally different kind of possibility
that must be considered in the proof of #lemmaRef(<lemma3.18>) (which is really just the proof of #lemmaRef(<lemma2.17>)):

($infinity$) #h(0.5em) For all $i in omega$ a non-zero number of cycles of slice dimension greater than $i$ act.

The author has been unable to turn a failure of this type into a demonstration that $G leqt C$.
In the $dreInAbove(D)$ construction, possibility~(A), say, of #lemmaRef(<lemma3.18>) (actually of #lemmaRef(<lemma2.17>))
// p.51
led to computation of $G$ from $C$ "along the first component". In general, for any $n$, a failure of
the $dreInAbove(D)$ computation leads a computation of $G$ along one of the components. Outcome ($infinity$) allows no
such computation.

The same problems occur, even when we allow $F$ to be $dreInAbove(D)$, if we try to avoid $omega$-r.e. degrees,
as again the number of flip-flops depends on the particular witness chosen.

=== The special case $C = emptyset$

The case in which $C = emptyset$ was the first to be proved by the author.
It was obtained before the method was developed to ensure the consistency of the $Delta$ functional,
as that method is not needed in the special case. The overall construction is in any case vastly simplified.

To see why, consider what would happen in the construction if $C = emptyset$. In particular, we never experience a $C$-change.
At no time would a #cycle($chi$) need to return to an earlier numbered state due to a computation being destroyed.
So long as it is not reset, $chi$ will only ever make progress, or (at worst) stay put.
This means that no strategy will act infinitely often.
(Otherwise, by Lemmas~#thmref(<lemma3.18>) and~#thmref(<lemma3.19>),
 some cycle would act infinitely without being reset infinitely often.)
In other words, _each strategy causes only finitely much injury._
Once we have a finite injury argument, we can do away with the entire apparatus of the priority tree.

The finite injury nature of the construction also means that the functionals $Gamma_j$ and $Delta$
do not need to be constructed "on the fly", but can be extracted without too much trouble after the face, in the verification,
under the assumption that the construction has failed. This allows us to completely avoid the problems of
$Delta$-inconsistency in the original Cooper, Lempp, and Watson method.
Hence there was no need for the special method we used above.

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
witness $x$ was chosen, and hence the maximum number of times that $(udvd)(x)$ will change. We therefore have the following result,
which corresponds to #thmref(<theorem3.29>) just as #thmref(<theorem3.30>) corresponds to #thmref(<theorem3.28>)[Theorem].
#theorem[
    Given an r.e. set $G ident.not_T emptyset$, there is r.e. $D leqt G$ and a set $F$ which is
    simultaneously $dreInAbove(D)$ and $omega$-r.e., but not of $n$-r.e. degree for any $n in omega$.
    <theorem3.31>
]

// p.52
=== A related result

In @ALS1998 the following is proved.

#theorem(name: [Arslanov, LaForte, and Slaman])[
    Any $omega$-r.e. set with is 2-REA is actually of 2-r.e. degree.
    <theorem3.32>
]
The question then occurs: does the behavior occur for numbers greater than 2?
The same paper answers the question negatively:
#theorem(name: [Arslanov, LaForte, and Slaman])[
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
// p.53
= For high $C$ the properly $reInAbove(C)$ intervals are weakly dense <chapter4>

== Introduction

In #chapRef(3) we gave a generalization of (a weaker form) of the original Soare and Stob result.
In #chapRef(5) we will prove a generalization in another direction:
// TODO: label this 5.2
#theorem[
    For any non-recursive r.e. set $C$, there are $reInAbove(C)$ sets $A$ and $B$ such that $A ltt B$
    and there is no r.e. set $D in turinginterval(A, B)$.
]

In this chapter we consider the latter result from the point of density: can such r.e.-free intervals be
found densely in the r.e. degrees?
#conjecture[
    For all r.e. sets $C$, $G$, and $H$ such that $emptyset ltt C leqt G ltt H$ there
    are $reInAbove(C)$ sets $D ltt F$ such that $turinginterval(D, F) subset turinginterval(G, H)$
    and there is no r.e. set $E in turinginterval(D, F)$.
    <conjecture4.1>
]
This (and even the weaker version in which we allow $D = F$) is false because of
#theorem(name: [Arslanov, Lempp and Shore, @ALS1996])[
    There is a recursively enumerable set $C$ with $emptyset ltt C ltt emptyset'$ such that
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
    If $C leqt H$ are r.e. and high (that is, $C' equivt H' equivt emptyset'$), there is a d.r.e. set
    $E$ which is $reInAbove(C)$ but not of r.e. degree such that $C ltt E ltt H$.
    <theorem4.4>
]
// p.54
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
 (recursively) guess how long it takes initial segments of $C$ to converge, you are wrong cofinitely often.)
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

// p.55
=== The Basic Modules

==== The $R_e$ requirements

For the requirements of the first type (the "r.e.-avoiding" requirements) the basic module is
a simplified version of the one used in @ALS1996[Theorem 2.1]. This in turn is basically the approach used in
@CLW1989[Theorem 1], but incorporating high permitting. The strategy used to satisfy $R_e$ consists of a
(potentially unbounded) number of _cycles_, each of which tries to satisfy the requirement in a very simplistic way.
If each cycle fails, we argue that $H leqt G$, contradicting the hypothesis of the theorem.

Suppose $e$ is fixed, and write $angletup(E, Phi, Psi)$ for $angletup(E_e, Phi_e, Psi_e)$. We will describe the strategy
for satisfying~$R_e$.  It consists of an $omega$-sequence of cycles. Cycle~0 starts first, and each #cycle($k$) can start
cycle $k+1$, as well as stopping all cycles $k' > k$. The strategy as a whole threatens to demonstrate that
$H leqt G$ by constructing a functional $Gamma(G) = H$. The #cycle($k$) may define the value $Gamma(G\; k)$. The strategy
also defines values for an auxiliary (partial) recursive function~$m$, used in the high permitting part of the argument.

All cycles begin in #state(0).
A cycle is _started_ by letting it pass from #state(0) to another state,
depending on its history, as in earlier chapters. Again, a cascade of cycle-startings might occur.
A cycle is _reset_ by putting it back into #state(0), returning its restraints to 0, and undefining the values of its
parameters, $u$, $x$, and $p$.
A cycle is _abandoned_ by returning its restraints to 0 and (permanently) stopping all activity for that cycle.
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
  // p.56
  use~$u$, and start cycle $k+1$ to run simultaneously. Advance to #state(2).

+ Wait for a stage $s'$ at which either

  + $restr(G_(s'), u) neq restr(G_(s_1), u)$, or
  + $H_(s')(k) neq H_(s_1)(k)$

  On reaching $s'$, reset all cycles $k' > k$ of #stalpha. Then

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

  It in entirely possible that while we are waiting for $s_2$, $C$ changes below $xi(x)$, ejecting $x$ from $A$.
  We want $x$ to remain in $A$ for now, so we "artificially" keep it there by enumerating new axioms
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
   // p.57
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
  finitely often (see #lemmaRef(<lemma4.6>)), and we will still be able to threaten to compute $H$ recursively from $G$.

+ Wait for $restr(G, u) neq restr(G_(s_1), u)$. If this never happens, the strategy succeeds by the argument in #state(4),
  above. If it does happen, reset all cycles $k' > k$ and advance to #state(6) to redefine $Gamma(G\; k)$ as a value
  we now know to be correct, and abandon the cycle.
  (Note that the change in $G$ automatically undefines any values $Gamma(G\; k+1), Gamma(G\; k+2), dots$ which where
   defined while #cycle($k$) was waiting in #state(4). Thus, so long as we don't get permanently stuck in~4, the
   extraneous $Gamma$ values that are defined while we wait for the $G$-change don't persist. Of course, leaving~4
   but failing to reach 6 means we get stuck in 5, which leads to success.)

+ Redefine $Gamma(G\; k) = H(k) = 1$ with use 0, abandon #cycle($k$) and start #cycle($k+1$).

==== The $N_e$ requirements

The requirements $N_e$ are simpler that those of the first kind, are we implement a standard
diagonalization approach to satisfy them.  This is slightly complicated by the fact that we must
ensure that $B leqt H$, but we can just us a stripped-down version of the Cooper, Lempp and Watson method.

Again, suppose $e$ is fixed, and write $Theta$ for $Theta_e$. The strategy for $N_e$ has the same cycle
structure as that for $R_e$. Cycle~0 starts first. We again threaten to show $H leqt G$, this time by
constructing a functional $Delta(G) = H$. We don't need any auxiliary function like~$m$.
_Starting_, _resetting_, _abandoning_, and _acting_ all have the same definitions as before.

Call a node at which this strategy is being pursued $alpha$. Cycle~$k$ proceeds as follows.

// p.58
#show: doc => setupenum(doc, prefix: "N")
0. Until given the go-ahead, do nothing. When given the signal to proceed, check if
  #cycle($k$) has been abandoned in the past. If so jump straight to #nstate(4).
  Otherwise choose a witness, $y$, larger than any number mentioned so far in the construction
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

// p.59
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
all functionals are completely undefined, and all cycles are in #state(0) or #nstate(0), as appropriate.

Stage $s+1$: #h(1em) We define, in substages $t < s$, a finite path, $f_(s+1)$, through $T$, of length $s$.
We think of $f_(s+1)$ as our approximation to the "true" path defined at stage $s+1$.
So, suppose we have reached substage~$t$, and $alpha = restr(f_(s+1), t)$ is already defined.
If no cycle of #stalpha is started, we start $alpha$'s #cycle(0), and set $f_(s+1)(t) = 0$.
Otherwise, we have two cases.

- #case(1) Some (least) #cycle($k$) of $alpha$ is able (or forced, by a $G$-injury) to act

We allow #cycle($k$) to act.
Let $l$ be the rightmost cycle of #stalpha now imposing restraint (if there is any such cycle)
and put $f_(s+1)(t) = l$. If there is no such #cycle($l$) then put $f_(s+1)(t) = -1$.
Cancel all strategies $beta$ with $concatone(alpha, f_(s+1)(t)) <_L beta$.
If $l = k$ and the action of #cycle($k$) involved enumerating a number into or out of $A$
or into $B$ then also cancel all strategies $beta supset concatone(alpha, f_(s+1)(t))$.

- #case(2) No cycle of #stalpha is able, or forced, to act.

We do nothing, and there are no strategies to cancel. Define $f_(s+1)(t)$ just as above.

If $t + 1 < s$, we advance to substage $t+1$.

The strategies $alpha subset f_(s+1)$ are said to be _accessible_ at stage $s+1$.

== Verification

We do not state a Pattern Lemma or proofs of the consistency of the functions $Delta(G)$.
This is immediate from the construction.
(Note that we do not claim that the functionals $Gamma(G)$ are consistent, as we may indeed have
 multiple definitions. We prove below that this happens only finitely often.)

As usual in an infinite injury construction, the key object in the verification is the _true path_
though the tree~$T$, defined by $f(n) = k$, where $concatone((restr(f, n)), k)$ is the leftmost
successor of $restr(f, n)$ accessible infinitely often.

// p.60
When needed, we will refer to parameters associated with a particular cycle, $k$,
of a particular strategy, $alpha$, like so: $x(alpha, k)$, $u(alpha, k)$, etc.
We will drop the strategy name whenever possible.

To show that all the requirements are satisfied we prove the following, now familiar, result.
#proposition[
    #show: doc => setupenum(doc, formats: ("1.", "a."))
    For all $n in omega$

    + $f(n)$ is defined;

    + $restr(f, (n+1))$ is cancelled only finitely often, (note that $restr(f, 0) = emptyset$ is never cancelled);

    + #strat($restr(f, n)$) satisfies the requirement towards which it was working;

    + for all sufficiently large $G$-true stages $t$, $restr(f, (n+1)) subset f_t$.
    <proposition4.5>
]

So, inductively assume the proposition for $n = eta - 1$, let $alpha = restr(f, eta)$
and let $s_0$ be a stage so large that $alpha$ is not cancelled after~$s_0$, and for every $G$-true stage
$t > s_0$, $alpha subset f_t$.

We say that #stalpha _acts finitely_ if there is a #stg($s$) after which no cycle of $alpha$
acts. Otherwise, we way that $alpha$ _acts infinitely_.

#lemma[
    If $alpha$ acts infinitely then some single cycle of $alpha$ acts infinitely often.
    <lemma4.6>
]
#proof[
    Suppose otherwise, and suppose that $|alpha| = 2e$, so that #stalpha works towards
    satisfying requirement~$R_e$. Each #cycle($k$) must end up getting stuck in a state such that
    #cycle($k+1$) is no prevented from acting. Thus each $k$ either
    (a) gets stuck in #state(2),
    (b) gets stuck in #state(4), or
    (c) is abandoned.

    Suppose first that (b) happens to only finitely many cycles.
    Let $s > s_0$ be a stage so large that all the cycles which eventually get stuck in #state(4) have
    already entered that state for the last time by #stg($s$), never to leave. Consider the finite set
    $
    cal(G) = {x st Gamma(G\; x) "is defined at " stg(s)}.
    $
    If $x in cal(G)$ it is possible that $Gamma(G\; x)$ is (or will end up being) defined more than once:
    if #cycle($k$) gets permanently stuck in~4, cycles $k+1, k+2, dots$ may "write-over"
    values for $Gamma(G\; k+1), dots$ defined earlier.
    However, if $g = max(cal(G))$ and $macron(k) > g$, cycle $macron(k)$ does not get stuck in~4.
    Indeed, if it did it would have done so by #stg($s$), and then $x(alpha, macron(k)) in cal(G)$.
    But by construction $macron(k) < x(alpha, macron(k))$, which contradicts the definition of $macron(k)$.
    Thus either $macron(k)$ gets stuck in #state(2), or successfully passes through~4 and reaches~6.
    Either way, #cycle($macron(k)$) successfully computes a value $Gamma(G\; macron(k))$ which agrees with $H(macron(k))$.
    Thus
    $
    H(k) = cases(
        H(k)              & "if" k leq g\,,
        Gamma(G\; k) quad & "otherwise"\,,
    )
    $
    // p.61
    contradicting the assumption that $G ltt H$. Hence we need only consider the case in which infinitely
    many cycles get stuck in #state(4). We show that this leads to a contradiction.

    In this case, each of these cycles will have defined a value for the function~$m$ (this is done in #state(3).)
    As each cycle chooses its~$p$ to be the least without an $m$-value the construction ensures that function~$m$
    will be _total_ recursive, and hence dominated by $c_C$.
    For each #cycle($k$) that gets stuck in~4, let $x_k$ be the last witness it ever
    chooses#footnote[There must be a last, as $k$ only gets to choose a new one after it is reset.],
    let $p_k$ be the final value for which #cycle($k$) defines $m(p_k)$, and let $s_(2,k)$ be the final stage
    at which #cycle($k$) passes from #state(3) to #state(4) before getting stuck there. Note that $xi(x_k) = p_k$
    and that $m(p_k) = s_(2,k)$.

    Now, since $m$ is dominated by $c_C$, there is a $macron(p)$ such that
    $(forall p geq macron(p))[m(p) < c_C(p)]$ and so, by the definition of $c_C$
    $
    (forall p geq macron(p))[restr(C_(m(p)), p) neq restr(C, p)]
    $
    and
    $
    (forall p geq macron(p))[restr(C_(m(p)), xi(x)) neq restr(C, xi(x))]
    $
    whenever $xi(x) geq p$. Now let $k_0$ be minimal such that $p_(k_0) geq macron(p)$ and #cycle($k_0$) gets stuck in~4.
    Then $m(p_(k_0)) = s_(2,k_0)$ and
    $
    restr(C_(s_(2,k_0)), xi(x_(k_0))) neq restr(C, xi(x_(k_0))),
    $
    so #cycle($k_0$) does in fact see a $C$-change after #stg($s_(2,k_0)$).
    Let $q$ be the first $G$-true stage after after $q'$, the first $C$-true stage after $s_(2,k_0)$.
    As $q'$ involves a $C$-change on the smallest element for which a change is still to take place,
    it must involve a change in $C$ below $xi(x_(k_0))$.
    By assumption, $alpha$ will be accessible after $q'$ no later than #stg($q$), and so #cycle($k_0$)
    will be released from #state(4), contradicting our assumption about #cycle($k_0$).

    If $|alpha| = 2e + 1$, so that $alpha$ works towards $N_e$, the proof is much simpler. Now
    every cycle must end up getting stuck in #nstate(2) or being permanently abandoned.
    In either case, the #cycle($k$) computes a value $Delta(G\; k)$ which agrees with $H(k)$, and
    we demonstrate $H leqt G$, a contradiction.

    The lemma is proved.
]

The rest of the verification follows just as in #chapRef(2). The arguments are somewhat simpler,
as we have only a one-dimensional cycle-structure to worry about.
#lemma[
    Some (leftmost) successor of $alpha$ is accessible infinitely often.
    <lemma4.7>
]
#proof[
    As #lemmaRef(<lemma2.19>).
]

// p.62
This establishes part 1 of the Proposition, and we assume we have a value $k_eta$ for $f(eta)$.
#lemma[
    $restr(f, (eta+1)) = concatone(f, k_eta)$ is cancelled only finitely often.
    <lemma4.8>
]
#proof[
    As #lemmaRef(<lemma2.21>).
]

This establishes part 2 of the Proposition for $n = eta$.

#lemma[
    #stalpha satisfies requirement the corresponding requirement.
    <lemma4.9>
]
#proof[
    As #lemmaRef(<lemma2.22>).
]

This establishes part 3 of the Proposition for $n = eta$.

#lemma[
    For sufficiently large $G$-true stages $t$, $restr(f, (eta+1)) = concatone(alpha, k_eta) subset f_t$.
    <lemma4.10>
]
#proof[
    As #lemmaRef(<lemma2.23>).
]

This establishes part 4 of #thmref(<proposition4.5>) for $n = eta$, and the Proposition is proved. #qed

Thus all of the requirements are satisfied, and $turinginterval(D, F)$ forms a proper interval with $reInAbove(C)$
endpoints, free of r.e.~degrees. It remains to show that the permitting used in the construction
sufficed to ensure that $D ltt H$ and $F ltt H$.

We use the same method as in chapters @chapter2 and @chapter3. For $alpha in T$ let
$
e^alpha = max { n | (exists beta in T)[concatone(beta, n) subset alpha] },
$
the largest number which occurs as an outcome in the path leading to $alpha$. We also define
$
s^alpha = (mu s)[restr(H_s, e^alpha) = restr(H, e^alpha)].
$
Our technical lemma is the same as before.

#lemma[
    Suppose that $alpha subset f_s$, $t > max{s, s^alpha}$ is a $C$-true stage, $t' geq t$ is a $G$-true
    stage, and $s' > t'$.
    Then for $beta subset alpha$, if $beta subset.not f_t$ and $beta subset f_(s')$ then there is
    a stage $tau$ such that $s < tau leq s'$ and $beta$ is cancelled at #stg($tau$).
    <lemma4.11>
]
#proof[
    As #lemmaRef(<lemma2.25>). We use the assumption that $s'$ is greater than the first $G$-true stage
    after the first $C$-true stage after both $s$ and $s^alpha$ when we argue that it is "now or never"
    for some action out of #state(4).
    (In this state the cycle is waiting for a $C$-change, rather than a $G$-change.)
]

Now permitting follows much as it did before.
// p.63
#lemma[
    $A join B leqt H$.
    <lemma4.12>
]
#proof[
    The argument proceeds in almost the same way as #lemmaRef(<lemma2.26>).
    Note that, in line with the statement of #lemmaRef(<lemma4.11>), we must work with the first $G$-true
    stage after the first $C$-true stage, etc.
    This stage may be computed with the use of both a $G$-oracle and a $C$-oracle.
    As, by assumption, $C join G leqt H$, we can still answer all the necessary questions with an $H$-oracle.
]

== The flaw in the proof of #thmref(<theorem4.4>) <section4.4>

As well as simplifying it, the proof of #theoremRef(<theorem4.3>) given above appears to correct an error
in the proof of #theoremRef(<theorem4.4>) given in @ALS1996.
That proof adopts the two levels of $H$-permission that are used in @CLW1989 and #chapRef(2) of this thesis.,
and the two-dimensional cycle structure.
But the second layer of $H$-permission is redundant, as the $C$-permitting actions of #state(4) give default
$H$-permission, as $C leqt H$ by assumption.

In @ALS1996 #state(3) defines a second tier functional, which we will here call $Upsilon$. There is also an
extra state (which we will call #state(3.5)) between our states 3 and~4, corresponding to #chapRef(2)'s #state(5).
As in the earlier chapter, @ALS1996's construction returns from #state(3.5) to #state(3) upon certain $C$-changes.

As well as being redundant, this seems to break the $C$-permission argument, or rather the argument that shows
that $C$-permission does not interfere with our attempts to threaten $H leqt C$.
We must be able to show that we don't get stuck infinitely often in #state(4).
To do this, in the original proof of~@ALS1996, we must show that (apart from finitely many cases)
we get a $C$-change after the _last_ time that we pass out of #state(3)
(since we can have several $restr(C, u_2)$ changes, we may jump from 3.5 back to 3 several times).
But this is now a problem: we know that $c_C$ dominates the function $m$, but $m$ no longer records
the _last_ time we find a stage $s_2$ in 3, but merely the first.
We can't redefine $m(p)$ each time we return to~3, as the $m$ must be recursive.
We can't use larger and larger values for $p$ each time, as the argument requires that $xi(x) geq p$.
We can't even redefine $xi(x)$ each time we get a $C$-change, as we would then not be able to $H$-recursively
compute the final value for $xi(x)$, needed for the proof of #lemmaRef(<lemma4.12>).

////////////////////////////////////////
// Chapter V
// p.64
= A Theorem of Soare and Stob in an Interval <chapter5>
== Introduction

In @CholakHinman Cholak and Hinman give a proof of a result of Soare and Stob.
#theorem(name: [Soare and Stob, @SoareStob1982])[
    For any non-recursive r.e. set $C$, there exists an $reInAbove(C)$ set which is not of r.e. degree.
    <theorem5.1>
]

In this chapter we will prove the following generalization:
#theorem[
    For any non-recursive r.e. set $C$, there are $reInAbove(C)$ sets $D ltt F$ such that there is no r.e.~set
    $E in turinginterval(D, F)$.
    <theorem5.2>
]

The proof is based closely on that of Cholak and Hinman, but we recast it in the cycle method of earlier chapters.

== The construction

As shown in Corollary 4.3 of @SoareStob1982 we cannot find the sets $D$ and $F$ "effectively" from the set~$C$.
That is, given (an index for) $C$ we cannot recursively compute indices for the $C$-recursive enumerations of $D$ and~$F$.
We actually construct two pairs of $reInAbove(C)$, $(D_0, F_0)$ and $(D_1, F_1)$, and prove that one pair
satisfies the requirements of the theorem, without knowing which one.

We will satisfy all requirements
$
R_e:      quad & or.big_(i=0,1) [A_k neq Phi_(e,i)(E_(e,i)) or E_(e,i) neq Psi_(e,i)(C join A_i join B_i)],\
P_(2e):   quad & B_0 neq Theta_e(C join A_0),\
P_(2e+1): quad & B_1 neq Theta_e(C join A_1).
$
Here ${angletup(Phi_(e,0), Phi_(e,1), Psi_(e,0), Psi_(e,1), E_(e,0), E_(e,1))}_(e geq 0)$ enumerates all sextuples of four
recursive functionals and two r.e. sets, and ${Theta_e}_(e geq 0)$ simply enumerates the recursive functionals.
The
// p.65
$R$-requirements ensure that at least one of the intervals
$turinginterval(D_i, F_i) = turinginterval(C join A_i, C join A_i join B_i)$
is free of r.e. sets, while the $P$ requirements make sure that both of these intervals are proper.

=== The basic module for $R_e$

Fix $e geq 0$ and write $angletup(Phi_0, Phi_1, Psi_0, Psi_1, E_0, E_1)$
for $angletup(Phi_(e,0), Phi_(e,1), Psi_(e,0), Psi_(e,1), E_(e,0), E_(e,1))$.

The basic module again consists of cycles, this time in an $omega$-sequence, each
trying simplistically to satisfy requirement~$R_e$. As noted below (@section5.2.3[section])
we do not need to observe path restraint as we did in earlier constructions.
Cycle~0 starts first. Cycle~$k$ may start cycle $k+1$ and stop all cycles $k' > k$
In addition, if $k > 0$, cycle $k$ may instruct cycle $k-1$ to perform an enumeration. This is detailed below.
Even numbered cycles will enumerate witnesses into $A_0$, while the odd numbered will enumerate into $A_1$.
To this end it will be useful to use the notation $pi(l)$ for the parity of $l$.

All cycles begin in #state(0). A cycle is _started_ by letting it pass from #state(0) to #state(1),
choosing a witness on the way. A cycle is _reset_ by putting it back into #state(0), returning
its restraint to 0, and undefining the values of its parameters $x$, $u$, and $v$.
Unlike earlier constructions, a cycle is never permanently abandoned.

Where necessary we will indicate the value of a parameter corresponding to #cycle($l$) like so: $x(l)$, $u(l)$, $v(l)$.

Cycle $k$ proceeds as follows.

#show: doc => setupenum(doc)
0. Until told to start, do nothing. When started, choose a new witness~$x$ larger than any number mentioned in the
  construction so far (including all currently imposed $A$-restraints). Advance to #state(1).

+ Denote by $Eq(x, s)$ the condition
$
and.big_(k=0,1) [(restr(A_k, x + 1))[s] = (restr(Phi_(e,k)(E_(e,k)), x+1))[s] and
                 (restr(E_(e,k), hat(phi)(x)))[s] = (restr(hat(Psi)_(e,k)(C join A_k join B_k), hat(phi)(x)))[s]],
$
where $phi_s(x) = max{phi_(0,s)(x), phi_(1,s)(x)}$. (Note that $Eq(x, s)$ implies $Eq(y, s)$ for all $y < x$.)

Wait for a stage $s_1$ at which $Eq(x, s_1)$ holds. Set $u = phi_(s_1)(x)$ and put
$
v = max{(hat(psi)_0(phi(x)))[s_1], (hat(psi)_1(phi(x)))[s_1]}.
$
If $k > 0$ then instruct cycle $k-1$ to enumerate its witness $x(k-1)$ into $A_(pi(k-1))$ with use $v(k)$.
Restrain $restr((A_i join B_i), v(k))$ for $i = 0, 1$, start cycle $(k+1)$ to run simultaneously, and advance to #state(2).

[If there is no such stage then the requirement is satisfied.]

// p.66
+ Wait for a #stg($s_2$) at which

  + $restr(C_(s_2), v) neq restr(C_(s_1), v)$; or

  + #cycle($k$) is instructed by #cycle($k+1$) to enumerate $x$.

  If we have case (i) reset all cycles $l > k$, forget the current values of $u$ and~$v$,
  drop this cycle's restraint back to~0, return to #state(1), and (if $k > 0$) return cycle $k-1$ to #state(2).

  If we have case (ii) enumerate $x$ into $A_(pi(k), s_2+1)$ with use $v(k+1)$, and advance to
  #state(3). (Note that we do _not_ reset any cycles to the right.)

+ Wait for a #stg($s_3$) at which $restr(C_(s_3), v) neq restr(C_(s_1), v)$.

  If this happens reset all cycles to the right, forget the values of $u$ and~$v$, drop this cycle's restraint back to~0,
  return to #state(1),and (if $k > 0$) return cycle $k-1$ to #state(2). The $C$-change ejects $x(k-1)$ from $A_(pi(k-1))$
  (Note further than since $v < x(k+1) leq v(k+1)$, $x$ is ejected from $A_(pi(k))$ by this change in $C$.)

We note (without proof) that the valid patterns corresponding to this module are
exactly $setconcat(finseq({3}), {angletup(2, 1)})$.

=== The basic module for the $P$-requirements

Consider the requirement $P_(2e)$. (The $P_(2e+1)$ is the same, with $A_0$ and $B_0$ replaced with $A_1$ and $B_1$.)
Write $Theta$ for~$Theta_e$.
The strategy for satisfying $P_(2e)$ has no cycle-structure, but has 3 internal states.

#show: doc => setupenum(doc, prefix: "P")
0. Wait for the strategy to be started.
  When it is, choose a new witness, $y$, larger than any number mentioned in the construction so far
  (in particular, larger than any currently imposed $B$-restraint.) Advance to #pstate(1).

+ Wait for a #stg($t_1$) such that
  $
  (hat(Theta)(C join A_0; y))[t_1] = 0.
  $
  Put $w = hat(theta)_(t_1)(y)$, restrain $restr(A_0, w)$, and enumerate $y$ into $B_(0, t_1 +1)$ with $C$-use~$w$.
  Advance to #pstate(2).

+ Wait for a #stg($t_2$) at which $restr(C_(t_2), w) neq restr(C_(t_1), w)$.
  If this happens forget the value of~$w$, drop this cycle's restraint back to~0, and return to #pstate(1).
  (Note that $y$ has been ejected from $B_0$ by the $C$-change.)

// p.67
=== Combining the modules <section5.2.3>

As usual, we combine the basic modules by means of a strategy tree, $T$.
Let $Lambda = {-1} union omega$, and define the strategy tree
$T = {f in finseq(Lambda) st n "odd" arrow.r.double f(n) in {0, 1} }$,
with the standard partial ordering $<_L$.
If $alpha in T$ has even length $|alpha| = 2e$ then $alpha$ aims to satisfy requirement~$R_e$, while
if $|alpha| = 2e + 1$ it works towards satisfying~$P_e$.
(Hence the definition of the priority tree: strategies for satisfying $P_e$ will have just two outcomes: 0 and~1.)
As before we make no distinction between a node on the tree and (the instance of)
the strategy.
An $R$-strategy is cancelled by resetting all of its cycles.
A $P$-strategy is cancelled merely by putting it into #pstate(0) and discarding its witness.

The construction proceeds as follows.

Stage 0: #h(1em) All strategies are cancelled.

Stage $s+1$: #h(1em) We define, in substages $t < s$, a finite path $f_(s+1)$, through the tree, of length~$s$.
So, suppose $alpha = restr(f_(s+1), t) in T$ is defined.
We have two cases to consider, depending on the parity of~$t$.

- #case(1) $t$ is even, so #stalpha is trying to satisfy an $R$-requirement.

  If no cycle of #stalpha has been started since $alpha$ was last cancelled, start $alpha$'s #cycle(0).

  Otherwise see if there is a leftmost #cycle($k$) able to make one of the state transitions
  #trans(1, 2), #trans(2, 1), or #trans(3, 1).
  If so, let this cycle make this transition, resetting cycles to the right if indicated.
  In the case of the #trans(1,2) transition, if $k > 0$ we also let #cycle($k-1$) perform the required
  enumeration and move from #state(2) to #state(3).
  If one of the other transitions takes place cancel all strategies $beta$ with
  $concatone(alpha, k) subset beta$ or $concatone(alpha, k-1) <_L beta$.
  If also $k > 0$ we return #cycle($k-1$) to #state(2).
  If there is no such #cycle($k$) there is nothing to do at this substage.

  In any case, let $l$ be the rightmost cycle of $alpha$ in a state other than~0.
  (This cycle must be in #state(1), and if $l > 0$ then cycle $l - 1$ is in #state(2) and imposing restraint.)
  Let $f_(s+1)(t) = l - 1$.

- #case(2) $t$ is odd, so #stalpha is trying to satisfy a $P$-requirement.

If #stalpha is in #pstate(0) then let it advance to #pstate(1), choosing a witness on the way.

Otherwise, if $alpha$ is able to make a state transition #trans("P1", "P2") or #trans("P2", "P1") let it do so.
If the latter transition was made we cancel all strategies $beta supset concatone(alpha, 1)$.

In any case, let $f_(s+1)(t) = 0$ if $alpha$ is now in #pstate(1), and $f_(s+1)(t) = 1$ otherwise
(that is, if $alpha$ is in #pstate(2).)

If $t + 1 < s$ advance to substage $t+1$.

If $alpha subset f_(s+1)$ then $alpha$ is _accessible_ at stage $s+1$.

// p.68
== Verification

In what follows we will denote the values at #stg($s$) of parameters associated with #cycle($k$)
of #stalpha like so: $u_s(alpha, k)$, $x_s(alpha, k)$.
For parameters associated with $P$-requirement strategies we naturally omit any reference to the cycle.
Wherever context makes it possible, we omit as many of the stage, the strategy, and the cycle as we can.

Our verification follows Cholak and Hinman, @CholakHinman.

#lemma[
    #show: doc => setupenum(doc, formats: ("(i)",))
    For $alpha, beta in T$, where $|alpha| = 2e$ and $|beta| = 2e' + 1$ we have:
    + $x_s(alpha, k) in A_(pi(k),s)$ iff #cycle($k$) of #stalpha is in #state(3) at #stg($s$).
      Similarly, $y_s(beta) in B_(pi(e'),s)$ iff #strat($beta$) is in #pstate(2) at #stg($s$).
    + For stages $t < s$, if $x_t(alpha, k)$ is defined, and either $x_t(alpha, k) neq x_s(alpha, k)$,
      or $x_s(alpha, k)$ is undefined, then for all $s' geq s$, $x_t(alpha, k) in.not A_(pi(k),s')$.
      Similarly for any witness $y_t(beta)$ and the set $B_(pi(e'))$.
    <lemma5.3>
]
#proof[
    We start with (i). Certainly $x_s(alpha, k)$ is enumerated into $A_(pi(k))$ exactly when $alpha$'s #cycle($k$)
    enters #state(3). We claim that whenever this cycle leaves #state(3), for whatever reason, $x_s(alpha, k)$
    is ejected from $A_(pi(k))$.

    There are three ways that this cycle could leave #state(3).
    #show: doc => setupenum(doc, formats: ("(a)",))
    + Cycle $k$ sees a #stg($s_3$) such that $restr(C_(s_3), v) neq restr(C_(s_1), v)$.

      Well, the $C$-use of the enumeration that put $x_s(alpha, k)$ into $A_(pi(k))$ is
      $v(k+1) geq x(k+1) > v$ so this $C$-change indeed ejects $x_s(alpha, k)$ from $A_(pi(k))$.

    + Some cycle $l < k$ of #stalpha resets $k$ due to a change in $restr(C, v(l))$.

      But $v(l) < x_s(alpha, k) leq v(k) < v(k+1)$ as before, so again $x_s(alpha, k)$ is ejected from $A_(pi(k))$.

    + Strategy $alpha$ is cancelled by some cycle $beta subset.neq alpha$ or $beta <_L alpha$ seeing a $C$-change
      below $v(beta, l)$ for some~$l$ (or below $w(beta)$, as appropriate.)

      We consider the case where $|beta|$ is even, so that the $C$-change is below $v(beta, l)$.
      The $|beta|$ odd case is the same.
      If $beta subset.neq alpha$ then, by construction, $x_s(alpha, k)$ is chosen to be larger than $v(beta, l)$,
      as $alpha$ becomes accessible only after #cycle($l$) of #strat($beta$) imposes restraint and defines $v(beta, l)$.
      But now, as above, $v(alpha, k+1) > v(beta, l)$ and $x_s(alpha, k)$ is again ejected.

      If $beta <_L alpha$ then let $gamma$ be the longest common initial segment of $alpha$ and~$beta$.
      At the stage $t < s$ when $v(beta, l)$ is defined, either the action of #strat($gamma$) cancelled #stalpha,
      or no cycle of $alpha$ had been started since #stalpha was last cancelled.
      Thus $x_s(alpha, k)$ is chosen after $v(beta, l)$ is defined, so $x_s(alpha, k) > v(beta, l)$, and
      as before we have the result we want.

    // p.69
    A similar argument establishes the result for the $y$-witness.

    For (ii), notice that the witness $x(alpha, k)$ changes or becomes undefined only when
    #stalpha's #cycle($k$) is reset. When this occurs, #cycle($k$) leaves #state(3) (if it was there,)
    so by part~(i), $x(alpha, k)$ certainly leaves $A_(pi(k))$.
    As it will never again be chosen as a witness, it never reenters $A_(pi(k))$.
]

The rest of the verification revolves around the true path, $f$, through the priority tree,
defined as usual by $f(n) = nu$, where $concatone((restr(f, n)), nu)$ is the left most successor $restr(f, n)$
accessible infinitely often.

We have the following (now familiar) result.

#proposition[
    #show: doc => setupenum(doc, formats: ("1.",))
    For all $n in omega$

    + $f(n)$ is defined;

    + $restr(f, (n+1))$ is cancelled only finitely often, (note that $restr(f, 0) = emptyset$ is never cancelled);

    + #strat($restr(f, n)$) satisfies the requirement towards which it works;

    + for all sufficiently large $C$-true stages $t$, $restr(f, (n+1)) subset f_t$.
    <proposition5.4>
]

We proceed by induction. Assume 1, 2, 3, and 4 for $n = eta - 1$ and let $alpha = restr(f, eta)$.
Fix a stage $s_0$ so large that $alpha$ is not cancelled after $s_0$, and for every $C$-true
$t > s_0$, $alpha subset f_t$.

For the moment, assume $eta$ is even. For $l geq -1$ define
$
s(l) = (mu s geq s_0)(forall t > s)[alpha's "cycle" l+1 "is in state 1, 2, or 3 at stage" t],
$
if such exists. Clearly , if $s(l)$ is defined then so is $s(l') < s(l)$ for all $l' < l$.

When it exists, $s(l)$ has all sorts of nice properties.

#lemma[
    #show: doc => setupenum(doc, formats: ("(i)",))
    If $s(l)$ exists then

    + for each $k leq l$, $x_t(alpha, k)$, $u_t(alpha, k)$, and $v_t(alpha, k)$ have the same values for all $t > s(l)$,
      (these fixed values will be referred to as $macron(x)(alpha, k)$, $macron(u)(alpha, k)$, and $macron(v)(alpha, k)$);

    + $Eq(macron(x)(alpha, l), s(l))$ holds;

    + $restr(C_(s(l)), macron(v)(alpha, l)) = restr(C, macron(v)(alpha, l))$;

    + for all $s geq s(l)$ and $k leq l - 2$, $macron(x)(alpha, k) in A_(pi(l),s)$;

    + If $l > 0$ then $macron(x)(alpha, l - 1) in.not A_(pi(l-1), s(l))$ but for all $s > s(l)$,
      $macron(x)(alpha, l - 1) in A_(pi(l-1), s)$.
    <lemma5.5>
]
#proof[
    For (i), note that since cycle $l+1$ is in a state numbered 1 or higher for $s > s(l)$,
    all cycles $k leq l$ are in #state(2) or~3 for these stages. Thus the values of the parameters
    $x$, $u$, and $v$ associated with these cycles will have no chance to change value.

    // p.70
    (ii) follows from the minimality of $s(l)$.

    For (iii), if $restr(C, macron(v)(alpha, l))$ after #stg($s(l)$) then $alpha$'s #cycle($l$) would
    return to #state(1), resetting cycle $l+1$ and contradicting the definition of~$s(l)$.

    For all $s geq s(l)$ and all $k leq l-2$, $alpha$'s #cycle($k$) is in #state(3) at #stg($s$),
    so by #lemmaRef(<lemma5.3>);(i), $macron(x)(alpha, k) in A_(pi(k), s)$.
    This establishes~(iv).

    (v) follows as did (iv) once we note that, by the minimality of $s(l)$, $alpha$'s #cycle($l-1$)
    is still in #state($s$) at #stg($s(l)$), only reaching 3 at #stg($s(l) + 1$).
]

#lemma[
    For all $l$ and $s > s_0$, if #cycle($l+1$) of #stalpha is in a state numbered 1 or higher
    at #stg($s$) and $restr(C_s, v_s(alpha, l)) = restr(C, v_s(alpha, l))$ then $s(l)$ exists and is less than~$s$.
    <lemma5.6>
]
#proof[
    Cycle $l+1$ can only be reset (and hence sent to a state other than 1, 2, or 3) by
    a change in~$C$. The argument in #lemmaRef(<lemma5.3>);(i) shows that this change must be
    below $v_s(alpha, l)$, a contradiction.
]

The following result is vitally important, if tedious to prove.
#lemma[
    If $s(l+1)$ exists then
    $
    restr(A_(pi(l), s(l+1)), macron(v)(alpha, l)) = restr(A_(pi(l), s(l)), macron(v)(alpha, l)),\
    restr(B_(pi(l), s(l+1)), macron(v)(alpha, l)) = restr(B_(pi(l), s(l)), macron(v)(alpha, l)).
    $
    <lemma5.7>
]
#proof[
    We give the argument for $A_(pi(l))$. The $B_(pi(l))$ case is essentially the same.

    It suffices to show that for all $beta in T$ with $|beta|$ even, and all
    $t leq s(l+1)$ and $k in omega$ with $x_t(beta, k) < macron(v)(alpha, l)$, that
    $
    A_(pi(l),s(l+1))(x_t(beta, k)) = A_(pi(l),s(l))(x_t(beta, k)).
    $
    Again, we give the argument to deal with $A$-witnesses.

    If $concatone(alpha, l+1) <_L beta$ then strategy $beta$ is cancelled at #stg($s(l)$), and we
    use #lemmaRef(<lemma5.3>);(ii).
    Otherwise we actually have to do some work. We have several cases to consider.

    - $concatone(alpha, l+1) subset.neq beta$ for some $j leq l+1$.

      Note that we can actually assume that $j < l$, since if $j = l$ or $j = l+1$ then
      by construction #strat($beta$) automatically respects the restraint $macron(v)(alpha, l)$.

      If $t leq s(l)$ and $x_t(beta, k) in A_(pi(l), s(l))$ then by #lemmaRef(<lemma5.3>);(i)
      #strat($beta$)'s #cycle($k$) is in #state(3) at #stg($s(l)$).
      For $x_t(beta, k)$ to leave $A_(pi(l))$ between stages $s(l)$ and $s(l+1)$, $beta$'s
      #cycle($k$) must leave #state(3), due to a $C$-change, necessarily below $macron(v)(alpha, l)$.
      But this implies that $alpha$'s #cycle($l+1$) is reset, contradicting the definition of~$s(l)$.

      // p.71
      If $x_t(beta, k) in.not A_(pi(l), s(l))$ then $x_t(beta, k)$ can enter $A_(pi(l))$ only by $beta$'s
      #cycle($k$) entering #state(3).
      But this requires $beta$ being accessible, and hence the accessibility of $concatone(alpha, j)$.
      This can happen only if $alpha$'s #cycle($l+1$) is in #state(0), which does not happen after #stg($s(l)$).

      Note that no new witness $x_t(beta, k)$ is chosen for $s(l) < t leq s(l+1)$, as this would again imply
      $alpha$'s #cycle($l+1$) being in #state(0).

    - $beta <_L alpha$

      Any change in the value of $A_(pi(l))(x_t(beta, k))$ between stages $s(l)$ and $s(l+1)$ implies the
      accessibility or cancellation of #strat($beta$), and hence the cancellation of #stalpha,
      which by assumption does not happen.

    - $beta subset.neq alpha$

      If $t leq s(l)$ and $x_t(beta, k) in A_(pi(l), s(l))$,
      then $concatone(beta, k) <_L alpha$ or $concatone(beta, k) subset alpha$.
      (Otherwise #cycle($k$) of $beta$ is reset at #stg($s(l)$), as $alpha$ is inaccessible at $s(l)$.)
      Note that $beta$'s #cycle($k$) is in #state(3) at #stg($s(l)$).
      If this changes at any time before #stg($s(l+1)$) then $alpha$ is cancelled, by construction,
      which would contradict the definition of~$s(l)$.

      Suppose $t leq s(l)$ and $x_t(beta, k) in.not A_(pi(l), s(l))$, but that $x_t(beta, k)$ enters $A_(pi(l))$
      at some stage $t'$ with $s(l) < t' leq s(l+1)$.
      Then either $concatone(beta, k) subset alpha$ or $alpha <_L concatone(beta, k)$, as otherwise the entry
      of $x_t(beta, k)$ entails the cancellation of~$alpha$.
      But $alpha$ is accessible at #stg($s(l+1)$), so either
      #cycle($k$) of $beta$ is reset by $s(l+1)$ (if $alpha <_L concatone(beta, k)$), or
      $beta$'s #cycle($k$) is in #state(2) at #stg($s(l+1)$)
      In either case, $x_t(beta, k) in.not A_(pi(l), s(l+1))$, by #lemmaRef(<lemma5.3>);(i).

      If $s(l) < t leq s(l+1)$ (so $x_t(beta, k) in.not A_(pi(l), s(l))$) then $alpha <_L concatone(beta, k)$,
      for otherwise (since $concatone(beta, k-1)$ is accessible at~$t$) $alpha$ would have been cancelled
      between stages $s(l)$ and~$t$.
      Thus, since $alpha$ is accessible at $s(l+1)$, $beta$'s #cycle($k$) is in #state(0) at #stg($s(l+1)$),
      and $x_t(beta, k) in.not A_(pi(l), s(l+1))$.

    - $beta = alpha$

      If $k > l+1$ we just use #lemmaRef(<lemma5.3>) (ii). No $x_t(alpha, l+1)$ is ever in $A_(pi(l))$,
      as $pi(l+1) neq pi(l)$.
      If $j leq l$, $t < s(l)$, and $x_t(alpha, j) neq macron(x)(alpha, j)$ then again we use #lemmaRef(<lemma5.3>) (ii).
      So we are just left to consider the witnesses $macron(x)(alpha, j)$ for $j leq l$, and by parity,
      we need only consider those with $j ident l thin (mod 2)$.

      Well, for such $j leq l - 2$, $macron(x)(alpha, j) in A_(pi(l), s)$ for all $s geq s(l)$ by #lemmaRef(<lemma5.5>) (iv).
      Now $alpha$'s #cycle($l$) is in #state(1) at #stg($s(l)$), so by #lemmaRef(<lemma5.3>);(i),
      $macron(x)(alpha, l) in.not A_(pi(l), s(l))$.
      By #lemmaRef(<lemma5.5>) (v), $macron(x)(alpha, l) in.not A_(pi(l),s(l+1))$.

]
This result is used to prove the crucial
// p.72
#lemma[
    #show: doc => setupenum(doc, formats: ("(i)",))
    + If $s(l+1)$ exists then $restr(E_(pi(l), s(l+1)), macron(u)(alpha, l)) = restr(E_(pi(l), s(l)), macron(u)(alpha, l))$.

    + If $s(l+2)$ exists then there is an $s > s(l)$ such that
      $restr(E_(pi(l), s), macron(u)(alpha, l)) neq restr(E_(pi(l), s(l)), macron(u)(alpha, l))$, and if $t(l)$ is the least such~$s$,
      then $s(l+1) < t(l)$.
    <lemma5.8>
]
#proof[
    For (i), if $s(l+1)$ exists then both $Eq(macron(x)(alpha, l), s(l+1))$ and $Eq(macron(x)(alpha, l), s(l))$ hold,
    // note: Eq(*,*) hold in previous line by Lemma 5.5(ii)
    so
    $
    restr(E_(pi(l),s(l+1)), macron(u)(alpha, l))
             &= (restr(hat(Psi)_(pi(l))(C join A_(pi(l)) join B_(pi(l))), macron(u)(alpha, l)))[s(l+1)] \
             &= (restr(hat(Psi)_(pi(l))(C join A_(pi(l)) join B_(pi(l))), macron(u)(alpha, l)))[s(l)] \
             &= restr(E_(pi(l),s(l)), macron(u)(alpha, l)).
    $

    For (ii), if $s(l+2)$ exists, then since both
    $Eq(macron(x)(alpha, l), s(l+2))$ and $Eq(macron(x)(alpha, l), s(l))$ hold,
    if equality held for $s = s(l+2)$ we would have
    $
    0 &= A_(pi(l),s(l))(macron(x)(alpha,l)) \
      &= (hat(Phi)_(pi(l))(E_(pi(l)); macron(x)(alpha,l)))[s(l)] \
      &= (hat(Phi)_(pi(l))(E_(pi(l)); macron(x)(alpha,l)))[s(l+2)] \
      &= A_(pi(l),s(l+2))(macron(x)(alpha,l)) \
      &= 1.
    $
    By part (i) we must have $s(l+1) < t(l)$.
]

#lemma[
    If $alpha$ acts infinitely (that is, if infinitely often some cycle of #stalpha changes state,)
    then some (leftmost) cycle of $alpha$ must change state infinitely often.
    <lemma5.9>
]
#proof[
    Suppose not. Then each cycle must eventually get stuck in #state(3), never to leave.
    Thus $s(l)$ exists for all~$l$, and also each~$t(l)$.

    But $s(-1) = 0$ and
    $s(l+1) = (mu s < t(l))[Eq(macron(x)(alpha, l+1), s) sand restr(C_s, v_s(alpha, l+1)) = restr(C_(t(l)), v_s(alpha, l+1))]$.
    Moreover by Lemmas~#thmref(<lemma5.8>);(ii) and~#thmref(<lemma5.5>);(i) both $t(l)$ and $macron(x)(alpha, l)$ are
    recursively computable from $s(l)$, so the function $lambda l[s(l)]$ is recursive.

    But $restr(C_(s(l)), macron(v)(alpha, l)) = restr(C, macron(v)(alpha, l))$ by #lemmaRef(<lemma5.5>);(iii),
    and $macron(v)(alpha, l) geq macron(x)(alpha, l) > l$ so $C(l) = C_(s(l))(l)$, and $C$ is a recursive set,
    which contradicts the assumption of the theorem.
]

From now on we consider both $eta$ even and $eta$ odd.

#lemma[
    Some (leftmost) successor of $alpha$ is accessible infinitely often.
    <lemma5.10>
]
#proof[
    If $eta$ is even and $alpha$ acts only finitely, then after some stage $s geq s_0$ no cycle of $alpha$
    ever changes state again. If $k$ is the rightmost cycle of $alpha$ in a state other than 0 at #stg($s+1$)
    // p.73
    then $concatone(alpha, k-1)$ will be accessible whenever $alpha$ is after #stg($s$).
    But by the inductive hypothesis $alpha$ is accessible at every $C$-true stage after $s_0$,
    of which there are infinitely many.

    If $eta$ is even and $alpha$ acts infinitely, then by #lemmaRef(<lemma5.9>) some leftmost #cycle($k$) changes
    state infinitely often. Strategy~$alpha$ is not cancelled after #stg($s$), so it must be that either
    (a)~#cycle($k$) eventually switches infinitely often between states 2 and~3, and is never in another state; or
    (b)~$k = 0$ and #cycle($k$) returns infinitely often to #state(1).
    In case~(a), $concatone(alpha, k)$ is accessible infinitely often, while
    in case~(b), $concatone(alpha, -1)$ is.
    Note that in case~(a) #cycle($k+1$) is reset only finitely often.

    If $eta$ is odd, then let
    $
    h = cases(
        0\, quad & "if" stalpha "is in" pstate(1) "infinitely often,",
        1\, quad & "otherwise, (that is, if" alpha "is in" pstate(2) "cofinitely often)".
    )
    $
    Then $concatone(alpha, h)$ is accessible infinitely often.
]

Thus we have established part 1 of the Proposition for $n = eta$, and that we have a
value $epsilon$ for $f(n)$.

#lemma[
    $restr(f, (eta+1)) = concatone(alpha, epsilon)$ is cancelled only finitely often.
    <lemma5.11>
]
#proof[
    By assumption, after #stg($s_0$) #stalpha is not cancelled.

    If $eta$ is even, the by construction $concatone(alpha, epsilon)$ is cancelled after #stg($s_0$)
    only if $epsilon geq 0$, and even then only when #cycle($epsilon$) of #stalpha is reset or returns to #state(1).
    The argument in the proof of #lemmaRef(<lemma5.10>) shows that this happens only finitely often.

    If $epsilon$ is even, then if $epsilon = 0$, #strat($concatone(alpha, epsilon)$) is never cancelled after #stg($s_0$).
    If $epsilon = 1$ then there is a stage $s > s_0$ after which #stalpha is never in a state other than #pstate(2),
    and $concatone(alpha, 1)$ is not cancelled after #stg($s$).
]

This establishes part 2 of the Proposition.

#lemma[
    Strategy $alpha$ satisfies the requirement to which it works.
    <lemma5.12>
]
#proof[
    First consider $|eta| = 2e$.

    If $alpha$ acts only finitely, then $alpha$'s #cycle($epsilon + 1$) must get permanently stuck in #state(1).
    In particular, it never reaches its instance of $blankEq$.
    Thus either $A_i neq Phi_(e,i)(E_(e,i))$ or
    $E_(e,i) neq Psi_(e,i)(C join A_i join B_i)$ (for some $i = 0,1,$) and the requirement is satisfied.

    If $alpha$ acts infinitely, let $s > s_0$ be so larger than that #cycle($epsilon + 1$) of #stalpha
    is not reset after #stg($s$).
    Thus #cycle($epsilon + 1$) works with the same witness, $x$, from now on.
    As this cycle returns infinitely often to #state(1) we must have that one the functions
    $Phi_(e,i)(E_(e,i))$, $Psi_(e,i)(C join A_i join B_i)$ (for some $i = 0, 1$) is partial.
    (The argument is the same as in the proof of #lemmaRef(<lemma2.22>).)

    // p.74
    Now consider $eta = 2e+1$.
    Without loss of generality we assume that $e = 2e'$ is even,
    so that #stalpha works with $A_0$ and~$B_0$.
    Since $alpha$ is not cancelled after #stg($s_0$), the strategy works with the same witnesses, $y$,
    forever after~$s_0$.
    If $epsilon = 0$ then $alpha$ is infinitely often in #pstate(1).
    Thus either $Theta_(e')(C join A_0; y) converge$, but converges to something other than~0,
    (if only finitely often does #stalpha advance to #pstate(2)); or $Theta_(e')(C join A_0; j) diverge$.
    But if $alpha$ is in #pstate(1) infinitely often, then $y in.not B_0$, so either way
    $Theta_(e')(C join A_0) neq B_0(y)$.
]

This establishes part 3 of the Proposition. Only one part now remains.

#lemma[
    For all sufficiently large $C$-true stages~$t$, $concatone(alpha, epsilon) subset f_t$.
    <lemma5.13>
]
#proof[
    First suppose that $eta$ is even.

    Let $s > s_0$ be a stage so large that #cycle($epsilon + 1$) is not reset after #stg($s$),
    and is in a state other than~0 at #stg($s$).
    Suppose $t > s$ is a $C$-true stage such that #cycle($epsilon + 1$) finished #stg($t$) in a
    state numbered greater than~1.
    Then #cycle($epsilon + 1$) will never again return to #state(1), as the only way it can do so it through
    a change in $restr(C, v)$.
    But the combination of the use of the hat-trick functional $hat(Psi)$ in the definition of $blankEq$,
    and the fact that $t$ is a $C$-true stage, means that this cannot happen after #stg($t$).
    But this is a contradiction, as by construction #cycle($epsilon + 1$) is infinitely often in #state(1).

    If $eta$ is odd then a similar argument shows that (with #stg($s$) defined as above) #stalpha
    every $C$-true #stg($t$) after $s$ in #state($epsilon$).
]

This concludes the proof of the Proposition, and of #theoremRef(<theorem5.2>).

// Chapter 6
// p.75
= A generalization of a result of Coles et al <chapter6>

== Introduction

In previous chapters we have typically been given a starting r.e. set $X$ and have constructed
an $reInAbove(C)$ set~$Y$ by specifying an algorithm to do so.
In each case we have (essentially explicitly) specified a pseudojump operator~$V$ such that
$Y = pseudojump(X, V)$.
In #chapRef(3) we also constructed our base set~$X$; we only had to ensure
$X in turinginterval(C, G)$. There are four different ways we may be asked to go about building $V^X$:
#[
#set align(center)
#tablex(
    columns: (1.3in,) * 3,
    rows: (auto, 3em),
    align: horizon + center,
    $X$, $V$, [Example],
    [we construct], [we construct], [#theoremRef(<theorem3.7>)],
    [given],        [we construct], [Theorems #thmref(<theorem2.2>), #thmref(<theorem4.3>)],
    [we construct], [given],        [Hmmmm #sym.dots],
    [given],        [given],        [Boring:\ $V^X$ is fixed]
)
]

In this chapter we consider the situation in which we are given a pseudojump operator~$V$.
Jockusch and Shore, in @JockuschShore1983[Thm 3.1], show the following.
#theorem[
    Given a pseudojump operator $V$ there is a non-recursive r.e. set $A$ such that
    $pseudojump(A, V) equivt K$.
    <theorem6.1>
]

This is generalized in @CDJF to obtain.
#theorem[
    Given a pseudojump operator $V$ such that $V^X notleqt X$ for all r.e. sets $X$,
    there exist incomparable r.e. sets $A$ and $B$ such that
    $pseudojump(A, V) equivt pseudojump(B, V) equivt K$.
    <theorem6.2>
]

A stronger conclusion is possible from a weaker assumption, with a simpler proof.

// p.76
#theorem[
    Given a pseudojump operator $V$ such that $V^X notleqt X$ for all recursively enumerable sets $X equivt K$,
    there exist pairwise incomparable r.e. sets $D_0, D_1, D_2, dots$ such that
    for each $i$, $pseudojump(D_i, V) ident_T K$.
    <theorem6.3>
]

== The construction

As pointed out in @CDJF, theorem~#thmref(<theorem6.2>) may be proved as follows.
By Corollary~4.2 in @JockuschShore1983 we have
#theorem[
    For any low r.e. set $L$ and any pseudojump operator~$V$, there is an r.e. set
    $A geq_T L$ such that $pseudojump(A, V) equivt K$.
    <theorem6.4>
]

Now, using the Sacks splitting theorem we can split $K$ into two low r.e. sets $L_1$ and~$L_2$.
Taking a pseudojump~$V$ which acts non-trivially on the all r.e. sets and applying theorem~#thmref(<theorem6.4>)
to $L_1$ and $L_2$ in turn we obtain r.e. sets $A_1$ and $A_2$ such that $A_1 join A_2 equivt K$
and $pseudojump(A_i, V) equivt K$.
We have that $A_1$ and $A_2$ are incomparable, because if, say, $A_1 leqt A_2$ then $A_2 equivt K$ and
$V$ would not act non-trivially upon it.

The direct proof in @CDJF in a complex one and is at times difficult to follow.
The proof given here uses a more naïve approach.
We simply combine proofs of #theoremRef(<theorem6.4>) and of (an extremely weak version of) the
Sacks splitting theorem. These proofs mesh quite well and the combination
generalizes easily to produce infinitely many incomparable sets.
Therefore, the present author didn't so much discover the proof as assemble it from bits that were lying around.

We will construct for each $i in omega$ an r.e. set $D_i = A_i join B_i join C_i$.
The sets~$A_i$ will receive the elements of $K$ along the lines of the splitting theorem in such a way that
if $0 leq i < j$ we have $A_i union A_j = K$ so $K equivt A_i join A_j$ and $K equivt D_i join D_j$.
The sets $C_i$ will receive trace-markers which will attempt to encode $K$ into each $D_i$ separately,
using the method of @JockuschShore1984.
The sets $B_i$ receive enumerations of a technical nature, needed for the recovery of these encodings.

We represent elements $(x, y)$ of $omega times omega$ using the standard pairing function $pair(x, y)$.
Note that for all $i in omega$ we have $x < y implies pair(i, x) < pair(i,y)$.

We aim to satisfy the following requirements, for all $i, x in omega$
$
N_(i,x): quad & (exists^infinity s)[x in V^(D_i)[s]] implies x in V^(D_i),\
P_x:     quad & x in K iff x "is missing from at most one of" A_0, A_1, A_2, dots,\
R_(i,x): quad & x in K iff (exists y leq h(i,x))[y in column(omega, x) sand y in C_i],
$
where $lambda x[h(i,x)] leqt pseudojump(D_i, V)$.

We assume that we have an enumeration ${K_s}_(s geq 0)$ such that
$(forall s)[thin |setdiff(K_(s+1), K_s)| leq 1]$.
Following~@CDJF we also assume that the pseudojump $V$ has the property that for all r.e.
// p.77
sets $X$ given $x$, $s$, and $t > s$:
$
[x in V^X[s] sand restr(X_t, r_X(x, s)) neq restr(X_s, r_X(x, s))]
implies
(exists u)[s < u leq t sand x in.not V^X[u]]
$
where $r_X(x, s)$ is the $X$-use of the axiom witnessing $x in V^X[s]$.
Essentially , we identify $V$ with its hat-trick counterpart,~$hat(V)$.

The construction progresses as follows.

#let stage-hdr-local(name) = [#smallcaps[Stage] #name: #h(1em)]
#stage-hdr-local($s = 0$) For $i in omega$, $A_i = B_i = C_i = emptyset$.
Also, for all $i, s, x in omega$ put (as boundary conditions)
$h(i, x, -1) = l(i, x, -1) = 0$ and $h(i, -1, s) = -1$.

#stage-hdr-local($s+1$) Each stage has two "phases". The first aims to satisfy
the requirements $P_x$ and the second to satisfy the $R_(i,x)$. We will call the point between the two phases
stage $s + 1\/2$.

If $setdiff(K_(s+1), K_s) = emptyset$ then there is nothing to do.
Otherwise let $setdiff(K_(s+1), K_s) = {k}$ and proceed as described.

#phase("I") For all $i, x in omega$ define
$
r(i, x, s) = cases(
    "the" D_i"-use of" x in V^(D_i)[s] quad & "if" x in V^(D_i)[s]\,,
    0                                       & "otherwise"
)
$
Now put
$rho(i, x, s) = max{r(i, y, s) st y leq x}$ and
$rho^-(i, x, s) = max{r(i, y, s) st y < x}$.
Define
$
l(i,x,s) = (mu y) [ y in column(omega, x) sand y in.not B_(i,s) sand y geq l(i, x, s-1) sand y > rho^-(i, x, s)].
$
Let $pair(i_0, x_0)$ be the least pair $pair(i, x)$ such that $k leq r(i, x, s)$.
We now mimic the proof of Sacks' Splitting Theorem and"protect" the pair $pair(i_0, x_0)$ by
enumerating $k$ "everywhere else". For each $j neq i_0$ do the following:

#show: doc => setupenum(doc)
+ Enumerate $k$ into $A_(j, s + half)$,
+ Let $z$ be least such that $k leq r(j, z, s)$ and enumerate $l(j, z, s)$ into $B_(j, s+ 1\/2)$.
  If there is no such $z$, do nothing here.#footnote[
      Strictly speaking, we are being a little loose. After all, it is not $k$ that gets enumerated into $D_j$, but its
      encoding, $2k$, and we are only concerned with things if _this_ enumeration injures some restraint $r(j, z, s)$.
      However, if $2k < r(j, z, s)$ then certainly $k < r(j, z, s)$, and it does not seem worth the trouble to keep track
      of the difference between $k in A_i$ and what that means to $D_i$.
]

(This is the purpose of the enumerations into $B_j^([z])$: they witness the fact that $N_(j,z)$ was injured by
 an enumeration forced on us to protect a higher-priority pair. We do this only for the least pair $pair(j, z)$
 so affected, because if $pair(j, z') > pair(j, z)$ is also affected, this can be detected
 ($pseudojump(D_i, V)$)-recursively _via_ the implied change in $h(j, z, s)$. See lemma~#thmref(<lemma6.7>) below.)


If there is no such $pair(i_0, x_0)$, then just enumerate $k$ into $A_(i,s + half)$ for every $i in omega$.
In this case there is no enumeration into any $B_i$.

// p.78
#phase("II") For every $i$ such that $A_i$ just received an enumeration, we recompute $r(i, x, s)$,
and hence $rho(i, x, s)$ based on $D_(i,s+half)$.
(Even in the case where $k$ doesn't thereby injure anything we might get a new element in
 $setdiff(V^(D_i)[s+half], V^(D_i)[s])$, so we may as well recompute.)
Now, for all $i, x in omega$, (even~$i_0, x_0$) put
$
h(i, x, s) = (mu y)[ y in column(omega,x) sand y > h(i, x-1, s) sand y geq h(i, x, s-1) sand y > rho(i, x, s)]
$
and enumerate $h(i, k, s)$ into $C_(i, s + 1)$.

This ends the description of the construction.

== Verification

We have a sequence of lemmas which together demonstrate that all of the requirements are met.

#lemma[
    If $i neq j$ then $K = A_i union A_j$. Thus each requirement $P_x$ is satisfied.
    <lemma6.5>
]
#proof[
    Only elements appearing in $K$ at some time are ever enumerated into any $A_k$, and if (say)
    $y in K$ and $y in.not A_i$ then by construction, $y$ was enumerated into $A_j$.
]

Now for each pair $pair(i, x)$ define the injury set of $N_(i,x)$ as
$
I_(i,x) = { y st (exists s)[y in setdiff(D_(i,s+1), D_(i,s)) sand y leq r(i, x, s)]}.
$
#lemma[
    Each $I_(i,x)$ is finite, and each $r(i, x) =^"dfn" lim_s r(i, x, s)$ exists.
    Thus each requirement $N_(i,x)$ is satisfied.
    <lemma6.6>
]
#proof[
    We proceed by induction. Fix $i$ and $x$, and suppose that the lemma holds for all $pair(j, y) < pair(i, x)$.
    Let $s$ be so large that for all $pair(j, y) < pair(i, x)$

    - $I_(j,y) subset D_(j,s)$ (so that $N_(j,y)$ will never subsequently be injured), and

    - $(forall s' geq s)[r(j, y, s') = r(j, y)]$.

    Let $r = max {r(j,y) | pair(j,y) < pair(i,x)}$ and let $t geq s$ be so large that $restr(K_t, r) = restr(K, r)$
    and $restr(K_t, x) = restr(K, x)$.
    This means that no pair $pair(j, y) < pair(i, x)$ will ever need protection again.
    Thus, for any $t' > t$, if $y in setdiff(K_(t'+1), K_(t'))$ and $y leq r(i, x, t')$ then $pair(i, x)$
    is the least such pair threatened with injury and $y$ will be enumerated into all of the $A_j$'s _except_ $A_i$.
    So nothing enumerated into $A_i$ after #stg($t$) will ever injure $N_(i,x)$ and thereby enter $I_(i,x)$.
    As numbers of the form $l(i, z, t')$ with $z leq x$ will only be enumerated into $B_i$ when a
    pair $pair(j, y) < pair(i, x)$ needs protection, no such will ever be enumerated again.
    Also, since $restr(K_t, x) = restr(K, x)$, no number of the form $h(i, z, macron(t))$ with $z < x$ will enter $C_i$
    after #stg($t$).

    By construction,
    $
    (forall t' > t)(forall z geq x)[h(i, z, t') > r(i,z,t')]
    $
    // p.79
    and
    $
    (forall t' > t)(forall z > x)[l(i, z, t') > r(i, z, t')]
    $
    so none of these will ever injure $N_(i,x)$.

    We have shown that no element enters $I_(i,x)$ after stage $t$ and hence that this set is finite.

    If there is a stage $t_0 > t$ at which $x in V^(D_i)[t_0]$ then this will never later be injured,
    $x in V^(D_i)$, and $r(i, x) = r(i, x, t_0)$.
    By the same token, if $x in.not V^(D_i)$ then
    $(forall t_0 > t)[x in.not V^(D_i)[t_0]]$, and $r(i, x) = 0$.
]

Now define $h(i, x) = lim_s h(i, x, s)$.

#lemma[
    For $i in omega$, $lambda x [h(i,x)] leqt pseudojump(D_i, V)$.
    <lemma6.7>
]
#proof[
    Fix $i$.
    Write $m_r$ and $m_h$ for moduli of the functions $r(i,x,s)$ and $h(i, x, s)$ respectively.
    // That is, (treating $i$ as a constant because we have fixed it.)
    //
    //    m_r(x) = m_r(i, x) and m_h(x) = m_h(i, x) are such that
    //
    // (forall s > m_r(x))[r(i, x, s) = r(i, x)]
    // (forall s > m_h(x))[h(i, x, s) = h(i, x)].
    //
    // See Soare p.56
    We show how to $(pseudojump(D_i, V))$-recursively compute $h(i,x)$, $m_r$, and $m_h$ by induction.
    (In fact, it turns out that we end up with $m_r = m_h$, but it seems more natural to refer to these functions separately.)

    So, suppose we know $m_r(y)$, $r(i, y)$, $m_h(y)$, and $h(i,y)$ for all $y < x$.

    Let $s$ be so large that for all $y < x$

    - $s > m_r(y)$,

    - $s > m_h(y)$, and

    - $h(i, y) in C_(i,s)$ for all $y < x$ such that $h(i, y) in C_i$.

    By definition, for all $s' > s$, $rho^-(i, x, s') = rho^-(i, x, s)$.

    Now, if $x in V^(D_i)$ find a $t > s$ such that $x in V^(D_i)[t]$ and
    $restr(D_(i,t), r(i, x, t)) = restr(D_i, r(i, x, t))$.
    Then never again will $r(i, x, dot)$ or $h(i, x, dot)$ change and we can define $m_r(x) = m_h(x) = t$,
    so that $r(i, x) = r(i, x, t)$ and $h(i, x) = h(i, x, t)$.

    If $x in.not V^(D_i)$ we must work a little harder.
    Let $s' > s$ be arbitrary.
    First note that there can be no (least) $y < x$ such that $l(i, y, s' + 1) neq l(i, y, s')$.
    Well, suppose otherwise. For this least $y$, $l(i, y, ast.op)$ can change only if $l(i, y, s')$
    enters $B_i$ at #stg($s'+1$) to mark an injury to $N_(i,y)$.
    As this requirement in injured we must have in particular that $y in (V^(D_i))[s']$ and $r(i, y, s') > 0$.
    But then $restr(D_(i,s'+1), r(i, y, s')) neq restr(D_(i,s'), r(i, y, s'))$ and so by the assumption
    we made about the operator~$V$, $y in.not (V^(D_i))[s'+1]$ and $r(i, y, s'+1) = 0 neq r(i,y,s')$,
    contradicting the definition of~$s$.
    As $rho^-(i, x, s') = rho^-(i, x, s)$, it follows that the only way that we can have
    $l(i, x, s'+1) neq l(i, x, s')$ is if $l(i, x, s')$ was enumerated into $B_(i,s'+1)$
    because some pair $pair(j, y) < pair(i, x)$ received protection, thus injuring $N_(i,x)$.
    In this case, $l(i, x, s'+1)$ is chosen to be the next element after $l(i, x, s')$ in the
    column~$column(omega, x)$.
    So, writing $l(i,x,s) = pair(x, lambda_0)$, the only values that will ever subsequently be taken on
    by $l(i, x, s')$ will be (in order) $pair(x, lambda_0)$, $pair(x, lambda_0 + 1)$, $pair(x, lambda_0 + 2)$, ...
    As the value will change only when $N_(i,x)$ is injured, by #lemmaRef(<lemma6.6>) $l(i, x, s')$ will only
    take on finitely many of these values.

    // p.80
    So, let $J_x = { pair(x, k) | k geq lambda_0 sand pair(x, k) in B_i }$.
    Note that this set is finite, may perhaps be empty, and may be computed from $B_i$.
    Let $t$ be the least stage greater than~$s$ such that $J_x subset B_(i,t)$.
    Thus there are no injuries to $N_(i,x)$ after $t$ due to higher priority pairs being protected.
    By the definition of~$s$, there are also no subsequent injuries due to enumerations of
    $h(i,y)$ for $y < x$.
    As these are the only two ways in which injuries can occur, there are no injuries at all after #stg($t$),
    and we may conclude that $m_r(x) = m_h(x) = t$, $r(i, x) = 0$, and $h(i, x) = h(i, x, t)$.

    We are done.
]

Now, by #lemmaRef(<lemma6.6>), all of the requirements of the form $N_(i,x)$ are satisfied,
so for each $i$, $pseudojump(D_i, V) leqt K$.
By construction each $R$-requirement is satisfied, and since by #lemmaRef(<lemma6.7>) we can compute $h(i, x)$
from $pseudojump(D_i, V)$ we may conclude that also $K leq pseudojump(D_i, V)$.

It remains only to show that $D_0, D_1, D_2, dots$ are pairwise incomparable.
Well, suppose $i neq j$ and $D_i leqt D_j$.
By lemma~#thmref(<lemma6.5>) $K equivt A_i join A_j$ so also $K equivt D_i join D_j equivt D_j$.
But we already know that $pseudojump(D_i, V) equivt K$, so this would contradict the non-triviality
assumption we have made on the pseudojump~$V$.

#bibliography("works.yml", style: "ieee")

// LocalWords:  basicModuleRe blankEq equivt CDJF notleqt lim ast yml

