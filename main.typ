#import "@preview/touying:0.5.3": *
#import themes.metropolis: *
#import "@preview/cetz:0.3.1"
#import "@preview/fletcher:0.5.2" as fletcher: node, edge
#import "@preview/ctheorems:1.1.3": *
#import "@preview/curryst:0.3.0": rule, proof-tree
#import "@preview/numbly:0.1.0": numbly
#import "./catt.typ": *
#import "./dtt.typ": *
#import "@preview/codly:1.1.1": *
#import "@preview/codly-languages:0.1.1": *
#show: codly-init.with()
#show: metropolis-theme.with(aspect-ratio: "16-9")

// Pdfpc configuration
// typst query --root . ./example.typ --field value --one "<pdfpc-file>" > ./example.pdfpc
#pdfpc.config(
  duration-minutes: 30,
  start-time: datetime(hour: 14, minute: 10, second: 0),
  end-time: datetime(hour: 14, minute: 40, second: 0),
  last-minutes: 5,
  note-font-size: 12,
  disable-markdown: false,
  default-transition: (
    type: "push",
    duration-seconds: 2,
    angle: ltr,
    alignment: "vertical",
    direction: "inward",
  ),
)

// Custom Table Styling
#let toptable = (..content) => {
  table(
    fill: (x, y) => if y == 0 {
      silver
    },
    stroke: (x, y) => if y == 0 {
      (
        top: (thickness: 1pt, paint: silver),
      )
    } else if y > 0 {
      (
        top: (thickness: 1pt, paint: silver),
        left: (thickness: 1pt, paint: silver),
        right: (thickness: 1pt, paint: silver),
        bottom: (thickness: 1pt, paint: silver),
      )
    },
    inset: 7pt,
    ..content,
  )
}

#let lefttable = (..content) => {
  table(
    fill: (x, y) => if x == 0 {
      silver
    },
    stroke: (x, y) => if x == 0 {
      (
        right: (thickness: 1pt, paint: silver),
      )
    } else if x > 0 {
      (
        top: (thickness: 1pt, paint: silver),
        left: (thickness: 1pt, paint: silver),
        right: (thickness: 1pt, paint: silver),
        bottom: (thickness: 1pt, paint: silver),
      )
    },
    inset: 7pt,
    ..content
  )
}


// Theorems configuration by ctheorems
#show: thmrules.with(qed-symbol: $square$)
#let theorem = thmbox("theorem", "Theorem", fill: rgb("#eeffee"))
#let corollary = thmplain(
  "corollary",
  "Corollary",
  base: "theorem",
  titlefmt: strong,
)
#let definition = thmbox("definition", "Definition", inset: (x: 1.2em, top: 1em))
#let example = thmbox("example", "example", fill: rgb("#eeeeee")).with(numbering: none)
#let proof = thmproof("proof", "Proof")

#let boxify = content => box(fill: silver, inset: 0.5em, [#content])

#show: metropolis-theme.with(
  aspect-ratio: "16-9",
  // config-common(handout: true),
  config-info(
    title: [Equality and Isomorphisms in Type Theory],
    subtitle: [HoTT to Parametric Univalence and Beyond; `Trocq` @trocq],
    author: [Abdul Haliq],
    date: datetime.today(),
    institution: text(
            size: 1.2em,
            font: ("AU Passata"),
          )[#upper[Aarhus Universitet]],
  ),
)

#set heading(numbering: numbly("{1}.", default: "1.1"))

#title-slide()

== Outline <touying:hidden>

#components.adaptive-columns(outline(title: none, indent: 1em))

= Presentation

== Logical Relations Recap

#figure(toptable(
  columns: 3,
  align: (right, center, center),
  [], [Safety in System F], [Equality in `Trocq`],
  [arity], [1; Predicates], [2; Relations],
  [language], [first order logic], [MLTT],
  [abs thm], [safety of expression under safe context], [typing judgement under related terms and related types],
))
$
  forall xi, v s. [| Delta hy Gamma |]_xi (v s) ==> [| Delta hy tau |]^upright(bold(E))_xi (e[v s slash x s])
$
#figure(
  proof-tree(
    rule(
      name: [TrocqAbs-Thm],
      $gamma(Delta) hyp M' : A' #h(2em) gamma(Delta) hyp M_R : "rel"(A_R)(M, M')$,
      $gamma(Delta) hyp$,
      $gamma(Delta) hyp M : A$,
      $Delta hyt M @ A ~ M' ∵ M_R$,
      $Delta hyt A @ UU_i^alpha ~ A' ∵ A_R$,
    ),
  ),
)

== Parametricity Translations
*raw parametricity translation*
$
  [| angle.l angle.r |] &= angle.l angle.r \
  [| Gamma, x:A |] &= [| Gamma |], x : A, x' : A', x_R : [|A|] x x' \
  [| x |] &= x_R \
  [| UU_i |] &= lambda A, A'. A -> A' -> UU_i
$
*univalent parametricity translation*
$
  [|
    UU_i
  |] A B = Sigma(R : A -> B -> UU_i, e : A equiv B, Pi(a : A, b : B, R a b equiv Id(A, a, attach(arrow.b, br: e)(b))))
$
*generalized equality*
$
  sqr^((n,k)) (A, B) &= Sigma(R : A -> B -> UU, M_n(R) times M_k(R^(-1)))
$

#pagebreak()

*justifying univalence*
$
  "isContr"(T) &= Sigma(t : T, Pi(t' : T, Id(T,t,t'))) \
  "isFun"(R) &= Pi(a : A, "isContr"(Sigma(b : B, R(a,b)))) \
  A equiv B &= Sigma(R : A -> B -> UU, "isFun"(R) times "isFun"(R^(-1))) \
  &script("where" R^(-1) (b,a) = R(a,b))
$
$
  "isFun"(R) = "isUmap"(
    R
  ) = Sigma(
    &m : A -> B, && 1 & -> \
    &g_1 : Pi(a : A, b : B, Id(B, m(a), b) -> R(a, b)),  && 2_a & arrow.t \
    &g_2 : Pi(a : A, b : B, R(a, b) -> Id(B, m(a), b)), && 2_b & arrow.b \
    &Pi(a : A, b : B, g_1(a,b) comp g_2(a,b) =^dot_dot id)) && 4 & equiv
$
$
  sqr^top (A,B) = A equiv B = Sigma (R : A -> B -> UU_i, "isUmap"(R) times "isUmap"(R^(-1)))
$

== Equality Levels

#figure(
  grid(columns: 2, gutter: 5em, 
    cetz.canvas({
      import cetz.draw: *
      circle((-2, 0), radius: (0.1, 0.1), fill: black, anchor: "mid", name: "0")
      circle((0, 0), radius: (0.1, 0.1), fill: black, anchor: "mid", name: "1")
      circle((2, 1), radius: (0.1, 0.1), fill: black, anchor: "mid", name: "2_a")
      circle((2, -1), radius: (0.1, 0.1), fill: black, anchor: "mid", name: "2_b")
      circle((4, 0), radius: (0.1, 0.1), fill: black, anchor: "mid", name: "3")
      circle((6, 0), radius: (0.1, 0.1), fill: black, anchor: "mid", name: "4")
      content((-2, 1), $0$, anchor: "north")
      content((-2, -0.5), [#text(size: 0.65em, "no data")], anchor: "south")
      content((0, 1), $1$, anchor: "north")
      content((0, -0.5), [#text(size: 0.65em, $->$)], anchor: "south")
      content((2, 2), $2_a$, anchor: "north")
      content((2, 0.5), [#text(size: 0.65em, $arrow.t$)], anchor: "south")
      content((2, -0), $2_b$, anchor: "north")
      content((2, -1.5), [#text(size: 0.65em, $arrow.b$)], anchor: "south")
      content((4, 1), $3$, anchor: "north")
      content((4, -0.5), [#text(size: 0.65em, $iso$)], anchor: "south")
      content((6, 1), $4$, anchor: "north")
      content((6, -0.5), [#text(size: 0.65em, $equiv$)], anchor: "south")
      line("0.east", "1.west", name: "line0", mark: (end: ">", start: none))
      line("1.east", "2_a.west", name: "line1", mark: (end: ">", start: none))
      line("1.east", "2_b.west", name: "line2", mark: (end: ">", start: none))
      line("2_a.east", "3.west", name: "line3", mark: (end: ">", start: none))
      line("2_b.east", "3.west", name: "line4", mark: (end: ">", start: none))
      line("3.east", "4.west", name: "line5", mark: (end: ">", start: none))
    }),
    $
      sqr^top = sqr^((4,4)) &= A equiv B \
      sqr^((3,3)) &= A iso B \
      sqr^((1,0)) &= A -> B
    $
  )
)
$
  M_0(R) &= tt #h(2em) M_1(R) &= A -> B
$
$
  M_(2_a)(
    R
  ) &= Sigma(m : A -> B, G_(2_a)(m,R)) script("where" G_(2_a)(m,R) = Pi(a : A, b: B, Id(B, m(a), b) -> R(a,b))) \
  M_(2_b)(
    R
  ) &= Sigma(m : A -> B, G_(2_b)(m,R)) script("where" G_(2_b)(m,R) = Pi(a : A, b: B, R(a,b) -> Id(B, m(a), b))) \
  M_3(R) &= Sigma(m : A -> B, (G_(2_a)(m,R) times G_(2_b)(m,R))) \
  M_4(R) &= Sigma(m : A -> B, Sigma(g_1 : G_(2_a)(m,R), g_2 : G_(2_b)(m,R), g_1(a,b) comp g_2(a,b) =^dot_dot id))
$
$
  cal(D)_square = {(alpha,beta) in cal(A)^2 | alpha = top or beta in {0,1,2_a}^2}
$

== `Trocq` Calculus

#figure(toptable(
  columns: 3,
  align: center + horizon,
  [Parametricity Context], [$"CC"_omega^+$, Equality Levels], [`Trocq`],
  [
    $
      Xi ::= epsilon | Xi, x ~ x' ∵ x_R
    $
    $
      hyu p_square^(alpha,beta) : sqr^beta UU UU \
      "rel"(p_square^(alpha,beta)) = sqr^alpha
    $
    #figure(
      proof-tree(
        rule(
          $Xi hyu UU_i ~ UU_i ∵ p_(square_i)^(top,top)$,
        ),
      ),
    )
  ],
  figure(
    proof-tree(
      rule(
        $Gamma hyp UU_i^alpha subt UU_j^beta$,
        $alpha >= beta$,
        $i <= j$,
      ),
    ),
  ),
  [
    $
      Delta ::= epsilon | Delta, x @ A ~ x' ∵ x_R
    $
    $
      attach(arrows.bb, br: (p,q), tr: (m,n)) angle.l R, M^->, M^<- angle.r
    $
    $
      attach(arrow.b.double, tr: UU_i^alpha, br: UU_i^alpha') t_R &= attach(arrows.bb, tr: alpha, br: alpha') t_R
    $
    #figure(
      proof-tree(
        rule(
          $Delta hyt UU_i^alpha @ UU_(i+1)^beta ~ UU_i^alpha ∵ p_(UU_i)^(alpha,beta)$,
          $(alpha, beta) in cal(D)_square$,
        ),
      ),
    ) 
  ]
))

== `Coq` Code

`theories/Param_nat.v`

#codly(languages: codly-languages, )
```Coq
Inductive natR : nat -> nat -> Type :=
  | OR : natR O O
  | SR : forall (n n' : nat), natR n n' -> natR (S n) (S n').
Definition map_nat : nat -> nat := id.
Definition map_in_R_nat : forall {n n' : nat}, map_nat n = n' -> natR n n'
Definition R_in_map_nat : forall {n n' : nat}, natR n n' -> map_nat n = n'
Definition R_in_mapK_nat : forall {n n' : nat} (nR : natR n n'),
  map_in_R_nat (R_in_map_nat nR) = nR.
```

#figure(toptable(
  columns: 5,
  align: (center, center, center, center, center),
  [lattice data], $1$, $2_a$, $2_b$, $4$,
  [coq definition], `map_nat`, `map_in_R_nat`, `R_in_map_nat'`, `R_in_mapK_nat`,
))


#pagebreak()

#codly(languages: codly-languages, )
```Coq
Fixpoint isEven (n : nat) : bool :=
  match n with
  | O => true
  | (S x) => ~~ (isEven x)
  end.
Definition Param_isEven :
  forall (n1 n1' : nat) (n1R : natR n1 n1'), isEven n1 = isEven n1'.
Proof.
  intros n1 n1' n1R.
  induction n1R as [|n1 n1' n1R IHn1R].
  - reflexivity.
  - simpl. rewrite IHn1R. reflexivity.
Defined.
```

= Conclusion

== Problems Encountered

- basic tutorial in plugin repo is incomplete
- `BigN.t` is a complicated type, hard to construct data to construct relation
- cannot do parametricity proof between `nat` and `BigN.t` without proof transfer; `isEven`

== Conclusion

- able to relate theory to `Coq` code and see how $sqr (A,B)$ is constructed
- understand how equality and univalence is internalized in a theory
- able to read text on higher observational type theory now

= Bibliography <touying:hidden>

#bibliography("refs.bib")

= Thank You <touying:hidden>

#focus-slide[
  #smallcaps([Thank You])
]