/-
# Formal Lean/Markdown Specification
## Semantic domain of questionnaires, operational graph G1, and target-guided transdomain induction

This specification formalizes a system composed of four main modules:

1. construction of an operational graph `G1` in the target domain `D1`;

2. internal inference in `G1`, that is, computation of the real operational trace
   of a sample `c1 : D1.Sample`;

3. construction of transdomain induction objects, that is, minimal sets of
   question-answer pairs from the source domain `D2` capable of inducing
   operational QAs of the graph `G1`;

4. target-guided transdomain inference, which takes as input a sample
   `c2 : D2.Sample`, progressively induces a trace inside `G1`, and returns
   the set of samples `c1 : D1.Sample` compatible with the induced trace.

The fundamental distinction is:

`G1`

is the target operational graph, built to differentiate the samples of
domain `D1`.

`D2`

is not transformed into an autonomous differentiation graph.

Domain `D2` is used as the source domain of evidence.

The transdomain rules do not build a second graph `G2`; instead, they build
induction objects toward the operational QAs of `G1`.

General formula:

`c2 : D2.Sample`
`→ QA evidence in D2`
`→ minimal groups of D2 premises`
`→ induction of operational QAs in G1`
`→ induced trace in G1`
`→ compatible samples c1 in D1`

The real operational signature of a sample `c1` in `G1` is:

`OperationalSignature(c1) = { x1 | OperationalQAReached(D1,G1,c1,x1) }`

The signature induced by a sample `c2` inside `G1` is:

`InducedTargetSignature(c2) = { x1 | TargetQAInducedBySource(c2,x1) }`

Complete association is:

`InducedTargetSignature(c2) = OperationalSignature(c1)`

Partial association is:

`InducedTargetSignature(c2) ⊆ OperationalSignature(c1)`

When the induced trace is partial, isolated terminals are not compared.
Instead, complete operational paths of `G1` extending the induced trace are
compared.

Central point of the optimization:

for each target operational QA `x1` of `G1`, minimal sets of source QAs
`P2 ⊆ QA D2` are constructed such that:

`P2 ⟹ x1`

through transdomain rules.

During inference, the real cost of a set of premises is not its absolute
cardinality, but the number of new QAs still to be acquired with respect to
the already acquired ancestor context:

`Cost(P2 | Context) = cost of the QAs in P2 not already assumed in the context`

If a source QA has already been used to induce an ancestor QA in `G1`, then
its answer is assumed as contextual and is not requested again.

If, instead, the same question appears in a non-ancestor branch, it is not
automatically considered reached: structural reuse is allowed, but operational
validity remains tied to the path context.

Technical Lean note:

We do not use `from` as the name of a variable or field.

We use:

`src` = source node.

`dst` = destination node.
-/

namespace SemanticSpec

universe u v w


/-
## 0. Minimal sets

A set of elements of type `α` is represented as a predicate:

`SSet α := α → Prop`

Therefore:

`x ∈ A`

means:

`A x`.

Formula:

`A ⊆ α`

is represented as:

`A : α → Prop`
-/

abbrev SSet (α : Type u) := α → Prop

instance {α : Type u} : Membership α (SSet α) where
  mem A x := A x


/-
`Subset A B` means:

`A ⊆ B`

Formula:

`Subset(A,B) := ∀ x, x ∈ A → x ∈ B`
-/

def Subset {α : Type u} (A B : SSet α) : Prop :=
  ∀ x : α, x ∈ A → x ∈ B


/-
`ProperSubset A B` means:

`A ⊂ B`

Formula:

`ProperSubset(A,B) := A ⊆ B ∧ ∃ x, x ∈ B ∧ x ∉ A`
-/

def ProperSubset {α : Type u} (A B : SSet α) : Prop :=
  Subset A B ∧
  ∃ x : α, x ∈ B ∧ ¬ (x ∈ A)


def MyEmptySet {α : Type u} : SSet α :=
  fun _ => False


def MyUnion {α : Type u} (A B : SSet α) : SSet α :=
  fun x => x ∈ A ∨ x ∈ B


def MyInter {α : Type u} (A B : SSet α) : SSet α :=
  fun x => x ∈ A ∧ x ∈ B


def MySingleton {α : Type u} (a : α) : SSet α :=
  fun x => x = a


/-
## 1. Semantic domain

A semantic domain is a quadruple:

`D = (Sample, Question, Answer, holds)`

where:

`Sample`

is the type of samples.

`Question`

is the type of questions.

`Answer q`

is the type of admissible answers for question `q`.

`holds q c r`

says that sample `c` satisfies answer `r` to question `q`.

Formula:

`holds(q,c,r)`

It is read as:

"for sample `c`, answer `r` to question `q` is true".

Important note:

`Answer` depends on `Question`.

Dependent formula:

`Answer : Question → Type`
-/

structure SemanticDomain where
  Sample   : Type u
  Question : Type v
  Answer   : Question → Type w

  holds : (q : Question) → Sample → Answer q → Prop


/-
## 2. Semantic question-answer pair

A semantic QA is a dependent pair:

`QA(D) = Σ q : Question, Answer(q)`

In Lean:

`x.q : D.Question`

`x.r : D.Answer x.q`

This QA does not yet contain graph information.

It is only:

`(q,r)`
-/

structure QA (D : SemanticDomain) where
  q : D.Question
  r : D.Answer q


/-
Complete proposition:

`CompleteProp(D,c,x) := holds(x.q,c,x.r)`
-/

def CompleteProp
  (D : SemanticDomain)
  (c : D.Sample)
  (x : QA D) : Prop :=
  D.holds x.q c x.r


/-
A complete proposition is defined only if the following are present:

1. a sample;
2. a QA.

Formula:

`CompleteDefined(c?,x?) := ∃ c x, c? = some c ∧ x? = some x`
-/

def CompleteDefined
  (D : SemanticDomain)
  (c? : Option D.Sample)
  (x? : Option (QA D)) : Prop :=
  ∃ c : D.Sample,
  ∃ x : QA D,
    c? = some c ∧
    x? = some x


def Undefined
  (D : SemanticDomain)
  (c? : Option D.Sample)
  (x? : Option (QA D)) : Prop :=
  ¬ CompleteDefined D c? x?


theorem undefined_if_missing_sample
  (D : SemanticDomain)
  (x? : Option (QA D)) :
  Undefined D none x? := by
  intro h
  rcases h with ⟨c, x, hc, hx⟩
  cases hc


theorem undefined_if_missing_qa
  (D : SemanticDomain)
  (c? : Option D.Sample) :
  Undefined D c? none := by
  intro h
  rcases h with ⟨c, x, hc, hx⟩
  cases hx


/-
## 3. Semantic profile of the sample

The semantic profile of a sample is the set of all semantic QAs that are true
for that sample.

Formula:

`Profile(c) = { x : QA D | holds(x.q,c,x.r) }`

Answers are not necessarily exclusive.
-/

def Profile
  (D : SemanticDomain)
  (c : D.Sample) : SSet (QA D) :=
  fun x => D.holds x.q c x.r


/-
## 4. Connectors and internal rules

An internal rule allows deriving a QA from a set of premises.

Supported connectors:

`and` = all premises must be true.

`or` = at least one premise must be true.

General formula:

`premises ⊢ conclusion`
-/

inductive Connector where
  | and
  | or
deriving Repr


def PremisesHold
  (D : SemanticDomain)
  (c : D.Sample)
  (kind : Connector)
  (premises : SSet (QA D)) : Prop :=
  match kind with

  | Connector.and =>
      ∀ x : QA D,
        x ∈ premises →
        D.holds x.q c x.r

  | Connector.or =>
      ∃ x : QA D,
        x ∈ premises ∧
        D.holds x.q c x.r


structure DerivationRule
  (D : SemanticDomain) where

  premises   : SSet (QA D)
  conclusion : QA D
  kind       : Connector


def DerivationRuleSound
  (D : SemanticDomain)
  (rule : DerivationRule D) : Prop :=
  ∀ c : D.Sample,
    PremisesHold D c rule.kind rule.premises →
    D.holds rule.conclusion.q c rule.conclusion.r


structure DerivationSystem
  (D : SemanticDomain) where

  rules : SSet (DerivationRule D)

  sound :
    ∀ rule : DerivationRule D,
      rule ∈ rules →
      DerivationRuleSound D rule


/-
Closure operator:

`X ⊆ close(X)`
-/

structure ClosureOperator
  (D : SemanticDomain) where

  close : SSet (QA D) → SSet (QA D)

  extensive :
    ∀ X : SSet (QA D),
      Subset X (close X)


def ExtendedProfile
  (D : SemanticDomain)
  (Cl : ClosureOperator D)
  (c : D.Sample) : SSet (QA D) :=
  Cl.close (Profile D c)


theorem profile_subset_extended
  (D : SemanticDomain)
  (Cl : ClosureOperator D)
  (c : D.Sample) :
  Subset (Profile D c) (ExtendedProfile D Cl c) := by
  exact Cl.extensive (Profile D c)


/-
## 5. Semantic expressions

Semantic expressions allow building compound formulas.

Grammar:

`Expr ::= ⊤`

`Expr ::= ⊥`

`Expr ::= question(q)`

`Expr ::= answer(q,r)`

`Expr ::= qa(x)`

`Expr ::= ¬ Expr`

`Expr ::= Expr ∧ Expr`

`Expr ::= Expr ∨ Expr`

`Expr ::= Expr → Expr`

`Expr ::= Expr ↔ Expr`
-/

inductive SemanticExpression
  (D : SemanticDomain) where

  | top :
      SemanticExpression D

  | bottom :
      SemanticExpression D

  | question :
      D.Question →
      SemanticExpression D

  | answer :
      (q : D.Question) →
      D.Answer q →
      SemanticExpression D

  | qa :
      QA D →
      SemanticExpression D

  | not :
      SemanticExpression D →
      SemanticExpression D

  | and :
      SemanticExpression D →
      SemanticExpression D →
      SemanticExpression D

  | or :
      SemanticExpression D →
      SemanticExpression D →
      SemanticExpression D

  | implies :
      SemanticExpression D →
      SemanticExpression D →
      SemanticExpression D

  | iff :
      SemanticExpression D →
      SemanticExpression D →
      SemanticExpression D


inductive SemanticObject
  (D : SemanticDomain) where

  | sample :
      D.Sample →
      SemanticObject D

  | question :
      D.Question →
      SemanticObject D

  | answer :
      (q : D.Question) →
      D.Answer q →
      SemanticObject D

  | qa :
      QA D →
      SemanticObject D


def InterpretExpression
  (D : SemanticDomain)
  (e : SemanticExpression D) : D.Sample → Prop :=
  match e with

  | SemanticExpression.top =>
      fun _ => True

  | SemanticExpression.bottom =>
      fun _ => False

  | SemanticExpression.question q =>
      fun c =>
        ∃ r : D.Answer q,
          D.holds q c r

  | SemanticExpression.answer q r =>
      fun c =>
        D.holds q c r

  | SemanticExpression.qa x =>
      fun c =>
        D.holds x.q c x.r

  | SemanticExpression.not e₁ =>
      fun c =>
        ¬ InterpretExpression D e₁ c

  | SemanticExpression.and e₁ e₂ =>
      fun c =>
        InterpretExpression D e₁ c ∧
        InterpretExpression D e₂ c

  | SemanticExpression.or e₁ e₂ =>
      fun c =>
        InterpretExpression D e₁ c ∨
        InterpretExpression D e₂ c

  | SemanticExpression.implies e₁ e₂ =>
      fun c =>
        InterpretExpression D e₁ c →
        InterpretExpression D e₂ c

  | SemanticExpression.iff e₁ e₂ =>
      fun c =>
        InterpretExpression D e₁ c ↔
        InterpretExpression D e₂ c


theorem interpret_top
  (D : SemanticDomain)
  (c : D.Sample) :
  InterpretExpression D SemanticExpression.top c := by
  exact True.intro


theorem interpret_and_iff
  (D : SemanticDomain)
  (e₁ e₂ : SemanticExpression D)
  (c : D.Sample) :
  InterpretExpression D (SemanticExpression.and e₁ e₂) c
  ↔
  InterpretExpression D e₁ c ∧
  InterpretExpression D e₂ c := by
  rfl


theorem interpret_or_iff
  (D : SemanticDomain)
  (e₁ e₂ : SemanticExpression D)
  (c : D.Sample) :
  InterpretExpression D (SemanticExpression.or e₁ e₂) c
  ↔
  InterpretExpression D e₁ c ∨
  InterpretExpression D e₂ c := by
  rfl


theorem interpret_not_iff
  (D : SemanticDomain)
  (e : SemanticExpression D)
  (c : D.Sample) :
  InterpretExpression D (SemanticExpression.not e) c
  ↔
  ¬ InterpretExpression D e c := by
  rfl


theorem interpret_implies_iff
  (D : SemanticDomain)
  (e₁ e₂ : SemanticExpression D)
  (c : D.Sample) :
  InterpretExpression D (SemanticExpression.implies e₁ e₂) c
  ↔
  (InterpretExpression D e₁ c → InterpretExpression D e₂ c) := by
  rfl


theorem interpret_iff_iff
  (D : SemanticDomain)
  (e₁ e₂ : SemanticExpression D)
  (c : D.Sample) :
  InterpretExpression D (SemanticExpression.iff e₁ e₂) c
  ↔
  (InterpretExpression D e₁ c ↔ InterpretExpression D e₂ c) := by
  rfl


/-
## 6. Open propositions, subordinates, and multidomain observations

An open proposition is a predicate:

`Sample → Prop`

A closed proposition is a proposition:

`Prop`

Subordinates are operators that transform predicates into other predicates.

Multidomain observations relate predicates belonging to different domains.
-/

structure OpenDomainProposition
  (D : SemanticDomain) where

  predicate : D.Sample → Prop


structure DomainProposition
  (D : SemanticDomain) where

  proposition : Prop


def openPropFromExpression
  (D : SemanticDomain)
  (e : SemanticExpression D) : OpenDomainProposition D :=
  { predicate := InterpretExpression D e }


def domainPropFromQA
  (D : SemanticDomain)
  (c : D.Sample)
  (x : QA D) : DomainProposition D :=
  { proposition := D.holds x.q c x.r }


def domainPropFromExpressionAtSample
  (D : SemanticDomain)
  (e : SemanticExpression D)
  (c : D.Sample) : DomainProposition D :=
  { proposition := InterpretExpression D e c }


structure SubordinateOperator
  (Sample : Type u) where

  op : (Sample → Prop) → (Sample → Prop)


def ApplySub
  {Sample : Type u}
  (S : SubordinateOperator Sample)
  (P : Sample → Prop) : Sample → Prop :=
  S.op P


def SubordinateAppliedToExpression
  (D : SemanticDomain)
  (S : SubordinateOperator D.Sample)
  (e : SemanticExpression D) : D.Sample → Prop :=
  ApplySub S (InterpretExpression D e)


def SubordinateAppliedToQA
  (D : SemanticDomain)
  (S : SubordinateOperator D.Sample)
  (x : QA D) : D.Sample → Prop :=
  S.op (fun c => D.holds x.q c x.r)


structure CombinedSubordinate
  (Sample : Type u) where

  op : (Sample → Prop) → (Sample → Prop)


def ApplyCombinedSub
  {Sample : Type u}
  (S : CombinedSubordinate Sample)
  (P : Sample → Prop) : Sample → Prop :=
  S.op P


structure MultiDomainObservation
  (D₁ D₂ : SemanticDomain) where

  leftExpr  : SemanticExpression D₁
  rightExpr : SemanticExpression D₂

  leftSub  : CombinedSubordinate D₁.Sample
  rightSub : CombinedSubordinate D₂.Sample

  relation :
    (D₁.Sample → Prop) →
    (D₂.Sample → Prop) →
    Prop

  observed :
    relation
      (leftSub.op  (InterpretExpression D₁ leftExpr))
      (rightSub.op (InterpretExpression D₂ rightExpr))


def MultiDomainObservation.leftInterpreted
  {D₁ D₂ : SemanticDomain}
  (O : MultiDomainObservation D₁ D₂) : D₁.Sample → Prop :=
  ApplyCombinedSub O.leftSub (InterpretExpression D₁ O.leftExpr)


def MultiDomainObservation.rightInterpreted
  {D₁ D₂ : SemanticDomain}
  (O : MultiDomainObservation D₁ D₂) : D₂.Sample → Prop :=
  ApplyCombinedSub O.rightSub (InterpretExpression D₂ O.rightExpr)


def MultiDomainObservationSound
  {D₁ D₂ : SemanticDomain}
  (O : MultiDomainObservation D₁ D₂) : Prop :=
  O.relation O.leftInterpreted O.rightInterpreted


theorem multidomain_observation_is_sound
  {D₁ D₂ : SemanticDomain}
  (O : MultiDomainObservation D₁ D₂) :
  MultiDomainObservationSound O := by
  exact O.observed


structure ObservationBase
  (D₁ D₂ : SemanticDomain) where

  observations : SSet (MultiDomainObservation D₁ D₂)


def ObservationBaseSound
  {D₁ D₂ : SemanticDomain}
  (B : ObservationBase D₁ D₂) : Prop :=
  ∀ O : MultiDomainObservation D₁ D₂,
    O ∈ B.observations →
    MultiDomainObservationSound O


theorem observation_base_sound_from_observed
  {D₁ D₂ : SemanticDomain}
  (B : ObservationBase D₁ D₂) :
  ObservationBaseSound B := by
  intro O hO
  exact multidomain_observation_is_sound O


/-
## 7. Semantic transdomain rules

A transdomain rule allows deriving a QA of `D₁` from a set of QAs of `D₂`.

Formula:

`premises ⊆ QA D₂`

`conclusion : QA D₁`

Schema:

`premises_D₂ ⟹ conclusion_D₁`

Premises are multiple.

Therefore a conclusion of domain `D₁` may depend on a group of QAs from
domain `D₂`, not on a single QA.

This section is semantic.

Later we will use these rules to build induction objects toward the operational
QAs of graph `G1`.
-/

def AllHold
  (D : SemanticDomain)
  (samples : SSet D.Sample)
  (features : SSet (QA D)) : Prop :=
  ∀ c : D.Sample,
    c ∈ samples →
    ∀ x : QA D,
      x ∈ features →
      D.holds x.q c x.r


def AllHoldOne
  (D : SemanticDomain)
  (samples : SSet D.Sample)
  (x : QA D) : Prop :=
  ∀ c : D.Sample,
    c ∈ samples →
    D.holds x.q c x.r


structure TransDomainRule
  (D₂ D₁ : SemanticDomain) where

  premises   : SSet (QA D₂)
  conclusion : QA D₁


def TransDomainRuleSound
  (D₂ D₁ : SemanticDomain)
  (samples₂ : SSet D₂.Sample)
  (samples₁ : SSet D₁.Sample)
  (rule : TransDomainRule D₂ D₁) : Prop :=
  AllHold D₂ samples₂ rule.premises →
  AllHoldOne D₁ samples₁ rule.conclusion


structure TransDomainSystem
  (D₂ D₁ : SemanticDomain) where

  samples₂ : SSet D₂.Sample
  samples₁ : SSet D₁.Sample

  rules : SSet (TransDomainRule D₂ D₁)

  sound :
    ∀ rule : TransDomainRule D₂ D₁,
      rule ∈ rules →
      TransDomainRuleSound D₂ D₁ samples₂ samples₁ rule


/-
## 8. Semantic coverage of questions

A question covers a set of samples if every sample has at least one true answer
to that question.

Formula:

`CoversQuestion(D,samples,q) := ∀ c ∈ samples, ∃ r, holds(q,c,r)`
-/

def CoversQuestion
  (D : SemanticDomain)
  (samples : SSet D.Sample)
  (q : D.Question) : Prop :=
  ∀ c : D.Sample,
    c ∈ samples →
    ∃ r : D.Answer q,
      D.holds q c r


def CoversQuestionSet
  (D : SemanticDomain)
  (samples : SSet D.Sample)
  (questions : SSet D.Question) : Prop :=
  ∀ c : D.Sample,
    c ∈ samples →
    ∃ q : D.Question,
      q ∈ questions ∧
      ∃ r : D.Answer q,
        D.holds q c r


theorem covers_singleton_question_set
  (D : SemanticDomain)
  (samples : SSet D.Sample)
  (q : D.Question) :
  CoversQuestion D samples q →
  CoversQuestionSet D samples (fun q' => q' = q) := by
  intro hCover
  intro c hc
  rcases hCover c hc with ⟨r, hHold⟩
  refine ⟨q, ?_, ?_⟩
  · show q = q
    rfl
  · exact ⟨r, hHold⟩


def SplitByQA
  (D : SemanticDomain)
  (samples : SSet D.Sample)
  (x : QA D) : SSet D.Sample :=
  fun c => c ∈ samples ∧ D.holds x.q c x.r


def SplitByQuestionAnswer
  (D : SemanticDomain)
  (samples : SSet D.Sample)
  (q : D.Question)
  (r : D.Answer q) : SSet D.Sample :=
  fun c => c ∈ samples ∧ D.holds q c r


/-
#######################################################################
## STRUCTURAL CHANGE WITH RESPECT TO THE PREVIOUS SPECIFICATION
#######################################################################

From this point onward, we no longer use:

`QTree`, `QBranch`, `QForest`.

Instead, we use:

`OperationalGraph`.

The graph is oriented.

Nodes are operational occurrences of questions.

Edges are labeled by answers.

Formula:

`src -- r --> dst`

The same sample may traverse multiple edges at the same time.
-/

structure OperationalGraph
  (D : SemanticDomain) where

  Node : Type

  questionOf :
    Node → D.Question

  roots :
    SSet Node

  active :
    (src : Node) →
    D.Answer (questionOf src) →
    Prop

  edge :
    (src : Node) →
    D.Answer (questionOf src) →
    Node →
    Prop


def AnswerActive
  (D : SemanticDomain)
  (G : OperationalGraph D)
  (src : G.Node)
  (r : D.Answer (G.questionOf src)) : Prop :=
  G.active src r


def AnswerContinues
  (D : SemanticDomain)
  (G : OperationalGraph D)
  (src : G.Node)
  (r : D.Answer (G.questionOf src)) : Prop :=
  ∃ dst : G.Node,
    G.edge src r dst


def AnswerEnabledAndTrue
  (D : SemanticDomain)
  (G : OperationalGraph D)
  (c : D.Sample)
  (src : G.Node)
  (r : D.Answer (G.questionOf src)) : Prop :=
  G.active src r ∧
  D.holds (G.questionOf src) c r


/-
## 9. Structural path of the graph

`GraphPath D G a b`

means that there exists a non-empty oriented path from `a` to `b`.

Recursive formula:

`GraphPath(a,b)`

holds if:

1. there exists a direct edge `a --r--> b`;
2. or there exists `m` such that `GraphPath(a,m) ∧ GraphPath(m,b)`.
-/

inductive GraphPath
  (D : SemanticDomain)
  (G : OperationalGraph D) :
  G.Node → G.Node → Prop where

  | edge :
      {src dst : G.Node} →
      (r : D.Answer (G.questionOf src)) →
      G.edge src r dst →
      GraphPath D G src dst

  | trans :
      {a b c : G.Node} →
      GraphPath D G a b →
      GraphPath D G b c →
      GraphPath D G a c


def AcyclicOperationalGraph
  (D : SemanticDomain)
  (G : OperationalGraph D) : Prop :=
  ∀ n : G.Node,
    ¬ GraphPath D G n n


def OperationalAncestor
  (D : SemanticDomain)
  (G : OperationalGraph D)
  (ancestor current : G.Node) : Prop :=
  GraphPath D G ancestor current


def AncestorQuestion
  (D : SemanticDomain)
  (G : OperationalGraph D)
  (current : G.Node)
  (q : D.Question) : Prop :=
  ∃ ancestor : G.Node,
    OperationalAncestor D G ancestor current ∧
    G.questionOf ancestor = q


def QuestionOnCurrentPath
  (D : SemanticDomain)
  (G : OperationalGraph D)
  (current : G.Node)
  (q : D.Question) : Prop :=
  G.questionOf current = q ∨
  AncestorQuestion D G current q


def QuestionNotOnCurrentPath
  (D : SemanticDomain)
  (G : OperationalGraph D)
  (current : G.Node)
  (q : D.Question) : Prop :=
  ¬ QuestionOnCurrentPath D G current q


def NoRepeatedQuestionOnPaths
  (D : SemanticDomain)
  (G : OperationalGraph D) : Prop :=
  ∀ a : G.Node,
    ∀ b : G.Node,
      GraphPath D G a b →
      G.questionOf a = G.questionOf b →
      False


theorem no_repeated_questions_implies_acyclic
  (D : SemanticDomain)
  (G : OperationalGraph D) :
  NoRepeatedQuestionOnPaths D G →
  AcyclicOperationalGraph D G := by
  intro hNoRep
  intro n hCycle
  exact hNoRep n n hCycle rfl


/-
## 10. Parallel operational reachability

`OperationalReaches D G c n`

means that sample `c` reaches node `n`.

Formula of the step:

`Reach(c,src) ∧ active(src,r) ∧ holds(questionOf(src),c,r) ∧ edge(src,r,dst) → Reach(c,dst)`

Since answers are not exclusive, the same sample may reach multiple nodes in
parallel.
-/

inductive OperationalReaches
  (D : SemanticDomain)
  (G : OperationalGraph D)
  (c : D.Sample) :
  G.Node → Prop where

  | root :
      {n : G.Node} →
      n ∈ G.roots →
      OperationalReaches D G c n

  | step :
      {src dst : G.Node} →
      (r : D.Answer (G.questionOf src)) →
      OperationalReaches D G c src →
      G.active src r →
      D.holds (G.questionOf src) c r →
      G.edge src r dst →
      OperationalReaches D G c dst


/-
## 11. Operational coverage of the graph

A graph covers a sample if:

1. there exists at least one root;
2. every reached node has at least one active and true answer.

Formula:

`GraphCoversSample(c) := HasRoot(c) ∧ ∀ n, Reach(c,n) → ∃ r, active(n,r) ∧ holds(questionOf(n),c,r)`
-/

def SampleHasOperationalRoot
  (D : SemanticDomain)
  (G : OperationalGraph D)
  (c : D.Sample) : Prop :=
  ∃ root : G.Node,
    root ∈ G.roots


def ReachedNodeHasTrueAnswer
  (D : SemanticDomain)
  (G : OperationalGraph D)
  (c : D.Sample)
  (n : G.Node) : Prop :=
  OperationalReaches D G c n →
  ∃ r : D.Answer (G.questionOf n),
    G.active n r ∧
    D.holds (G.questionOf n) c r


def GraphCoversSample
  (D : SemanticDomain)
  (G : OperationalGraph D)
  (c : D.Sample) : Prop :=
  SampleHasOperationalRoot D G c ∧
  ∀ n : G.Node,
    OperationalReaches D G c n →
    ∃ r : D.Answer (G.questionOf n),
      G.active n r ∧
      D.holds (G.questionOf n) c r


def GraphCoversSamples
  (D : SemanticDomain)
  (G : OperationalGraph D)
  (samples : SSet D.Sample) : Prop :=
  ∀ c : D.Sample,
    c ∈ samples →
    GraphCoversSample D G c


/-
## 12. Operational QA

A semantic QA is:

`(q,r)`

An operational QA is:

`(src,r)`

where:

`src : G.Node`

`r : D.Answer (G.questionOf src)`

Formula:

`OperationalQA(G) = Σ src : G.Node, Answer(questionOf src)`

Reachability formula:

`OperationalQAReached(c,(src,r)) := Reach(c,src) ∧ active(src,r) ∧ holds(questionOf(src),c,r)`

This is the primary differentiating signature of the graph.
-/

structure OperationalQA
  (D : SemanticDomain)
  (G : OperationalGraph D) where

  src : G.Node
  r   : D.Answer (G.questionOf src)


def OperationalQAAsSemanticQA
  (D : SemanticDomain)
  (G : OperationalGraph D)
  (x : OperationalQA D G) : QA D :=
  {
    q := G.questionOf x.src
    r := x.r
  }


def OperationalQAReached
  (D : SemanticDomain)
  (G : OperationalGraph D)
  (c : D.Sample)
  (x : OperationalQA D G) : Prop :=
  OperationalReaches D G c x.src ∧
  G.active x.src x.r ∧
  D.holds (G.questionOf x.src) c x.r


def OperationalQASignature
  (D : SemanticDomain)
  (G : OperationalGraph D)
  (c : D.Sample) : SSet (OperationalQA D G) :=
  fun x =>
    OperationalQAReached D G c x


def SameOperationalQASignature
  (D : SemanticDomain)
  (G : OperationalGraph D)
  (c₁ c₂ : D.Sample) : Prop :=
  ∀ x : OperationalQA D G,
    OperationalQAReached D G c₁ x ↔
    OperationalQAReached D G c₂ x


def OperationalQASignaturesDifferent
  (D : SemanticDomain)
  (G : OperationalGraph D)
  (c₁ c₂ : D.Sample) : Prop :=
  ¬ SameOperationalQASignature D G c₁ c₂


/-
## 13. Terminal question-answer

A terminal is an operational QA:

`(src,r)`

such that:

`active(src,r) ∧ ¬ ∃ dst, edge(src,r,dst)`

Formula:

`TerminalQAReached(c,t) := OperationalQAReached(c,t) ∧ ¬ AnswerContinues(t.src,t.r)`

Therefore:

`TerminalSignature(c) ⊆ OperationalSignature(c)`
-/

structure TerminalQA
  (D : SemanticDomain)
  (G : OperationalGraph D) where

  src : G.Node
  r   : D.Answer (G.questionOf src)


def TerminalQAAsOperationalQA
  (D : SemanticDomain)
  (G : OperationalGraph D)
  (t : TerminalQA D G) : OperationalQA D G :=
  {
    src := t.src
    r := t.r
  }


def TerminalQAAsSemanticQA
  (D : SemanticDomain)
  (G : OperationalGraph D)
  (t : TerminalQA D G) : QA D :=
  {
    q := G.questionOf t.src
    r := t.r
  }


def TerminalQAIsStructurallyTerminal
  (D : SemanticDomain)
  (G : OperationalGraph D)
  (t : TerminalQA D G) : Prop :=
  G.active t.src t.r ∧
  ¬ AnswerContinues D G t.src t.r


def TerminalQAReached
  (D : SemanticDomain)
  (G : OperationalGraph D)
  (c : D.Sample)
  (t : TerminalQA D G) : Prop :=
  OperationalQAReached D G c (TerminalQAAsOperationalQA D G t) ∧
  ¬ AnswerContinues D G t.src t.r


theorem terminal_reached_implies_operational_reached
  (D : SemanticDomain)
  (G : OperationalGraph D)
  (c : D.Sample)
  (t : TerminalQA D G) :
  TerminalQAReached D G c t →
  OperationalQAReached D G c (TerminalQAAsOperationalQA D G t) := by
  intro h
  exact h.1


theorem terminal_reached_implies_semantic_truth
  (D : SemanticDomain)
  (G : OperationalGraph D)
  (c : D.Sample)
  (t : TerminalQA D G) :
  TerminalQAReached D G c t →
  D.holds
    (TerminalQAAsSemanticQA D G t).q
    c
    (TerminalQAAsSemanticQA D G t).r := by
  intro h
  exact h.1.2.2


/-
## 14. Terminal signature

Formula:

`TerminalSignature(c) = { t | TerminalQAReached(c,t) }`

The terminal signature is a view of path closure.

The primary signature remains the operational one.

Terminals remain important, but they are no longer the isolated criterion of
transdomain association.
-/

def TerminalSignature
  (D : SemanticDomain)
  (G : OperationalGraph D)
  (c : D.Sample) : SSet (TerminalQA D G) :=
  fun t =>
    TerminalQAReached D G c t


def SameTerminalSignature
  (D : SemanticDomain)
  (G : OperationalGraph D)
  (c₁ c₂ : D.Sample) : Prop :=
  ∀ t : TerminalQA D G,
    TerminalQAReached D G c₁ t ↔
    TerminalQAReached D G c₂ t


def TerminalSignaturesDifferent
  (D : SemanticDomain)
  (G : OperationalGraph D)
  (c₁ c₂ : D.Sample) : Prop :=
  ¬ SameTerminalSignature D G c₁ c₂


/-
## 15. Complete differentiation

The main differentiation uses operational signatures:

`CompleteOperationalDifferentiationGraph(G,samples) := ∀ c₁ c₂ ∈ samples, c₁ ≠ c₂ → OperationalSignature(c₁) ≠ OperationalSignature(c₂)`

Expanded formula:

`∀ c₁ c₂, c₁ ∈ samples → c₂ ∈ samples → c₁ ≠ c₂ → ¬ SameOperationalQASignature(c₁,c₂)`
-/

def CompleteOperationalDifferentiationGraph
  (D : SemanticDomain)
  (G : OperationalGraph D)
  (samples : SSet D.Sample) : Prop :=
  ∀ c₁ : D.Sample,
    c₁ ∈ samples →
    ∀ c₂ : D.Sample,
      c₂ ∈ samples →
      c₁ ≠ c₂ →
      OperationalQASignaturesDifferent D G c₁ c₂


def CompleteOperationalDifferentiationGraphWitness
  (D : SemanticDomain)
  (G : OperationalGraph D)
  (samples : SSet D.Sample) : Prop :=
  ∀ c₁ : D.Sample,
    c₁ ∈ samples →
    ∀ c₂ : D.Sample,
      c₂ ∈ samples →
      c₁ ≠ c₂ →
      ∃ x : OperationalQA D G,
        ¬
          (OperationalQAReached D G c₁ x ↔
           OperationalQAReached D G c₂ x)


theorem complete_operational_witness_implies_complete_graph
  (D : SemanticDomain)
  (G : OperationalGraph D)
  (samples : SSet D.Sample) :
  CompleteOperationalDifferentiationGraphWitness D G samples →
  CompleteOperationalDifferentiationGraph D G samples := by
  intro hWitness
  intro c₁ hc₁ c₂ hc₂ hneq
  intro hSame
  rcases hWitness c₁ hc₁ c₂ hc₂ hneq with ⟨x, hdiff⟩
  exact hdiff (hSame x)


axiom complete_operational_graph_implies_witness
  (D : SemanticDomain)
  (G : OperationalGraph D)
  (samples : SSet D.Sample) :
  CompleteOperationalDifferentiationGraph D G samples →
  CompleteOperationalDifferentiationGraphWitness D G samples


def CompleteTerminalDifferentiationGraph
  (D : SemanticDomain)
  (G : OperationalGraph D)
  (samples : SSet D.Sample) : Prop :=
  ∀ c₁ : D.Sample,
    c₁ ∈ samples →
    ∀ c₂ : D.Sample,
      c₂ ∈ samples →
      c₁ ≠ c₂ →
      TerminalSignaturesDifferent D G c₁ c₂


def CompleteDifferentiationGraph
  (D : SemanticDomain)
  (G : OperationalGraph D)
  (samples : SSet D.Sample) : Prop :=
  CompleteOperationalDifferentiationGraph D G samples


/-
## 16. Separating question

Formula:

`QuestionSeparatesPair(q,c₁,c₂) := ∃ r, (holds(q,c₁,r) ∧ ¬ holds(q,c₂,r)) ∨ (holds(q,c₂,r) ∧ ¬ holds(q,c₁,r))`
-/

def QuestionSeparatesPair
  (D : SemanticDomain)
  (q : D.Question)
  (c₁ c₂ : D.Sample) : Prop :=
  ∃ r : D.Answer q,
    (D.holds q c₁ r ∧ ¬ D.holds q c₂ r)
    ∨
    (D.holds q c₂ r ∧ ¬ D.holds q c₁ r)


def QuestionSeparatesSomePairInSet
  (D : SemanticDomain)
  (q : D.Question)
  (samples : SSet D.Sample) : Prop :=
  ∃ c₁ : D.Sample,
  ∃ c₂ : D.Sample,
    c₁ ∈ samples ∧
    c₂ ∈ samples ∧
    c₁ ≠ c₂ ∧
    QuestionSeparatesPair D q c₁ c₂


def SeparatingQuestionBase
  (D : SemanticDomain)
  (samples : SSet D.Sample)
  (questions : SSet D.Question) : Prop :=
  ∀ c₁ : D.Sample,
    c₁ ∈ samples →
    ∀ c₂ : D.Sample,
      c₂ ∈ samples →
      c₁ ≠ c₂ →
      ∃ q : D.Question,
        q ∈ questions ∧
        QuestionSeparatesPair D q c₁ c₂


def SemanticallyDifferentiableSampleSet
  (D : SemanticDomain)
  (samples : SSet D.Sample)
  (questions : SSet D.Question) : Prop :=
  SeparatingQuestionBase D samples questions


/-
## 17. Pair not yet distinguished

Formula:

`NotYetDistinguished(c₁,c₂) := c₁ ∈ samples ∧ c₂ ∈ samples ∧ c₁ ≠ c₂ ∧ SameOperationalQASignature(c₁,c₂)`
-/

def NotYetDistinguished
  (D : SemanticDomain)
  (G : OperationalGraph D)
  (samples : SSet D.Sample)
  (c₁ c₂ : D.Sample) : Prop :=
  c₁ ∈ samples ∧
  c₂ ∈ samples ∧
  c₁ ≠ c₂ ∧
  SameOperationalQASignature D G c₁ c₂


/-
## 18. Questions already present, reusable, and new

Formula:

`QuestionAlreadyInGraph(q) := ∃ n, questionOf(n) = q`

`ExistingReusableQuestion(current,q) := QuestionAlreadyInGraph(q) ∧ QuestionNotOnCurrentPath(current,q)`
-/

def QuestionAlreadyInGraph
  (D : SemanticDomain)
  (G : OperationalGraph D)
  (q : D.Question) : Prop :=
  ∃ n : G.Node,
    G.questionOf n = q


def ExistingReusableQuestion
  (D : SemanticDomain)
  (G : OperationalGraph D)
  (current : G.Node)
  (q : D.Question) : Prop :=
  QuestionAlreadyInGraph D G q ∧
  QuestionNotOnCurrentPath D G current q


def FreshQuestionForCurrentPath
  (D : SemanticDomain)
  (G : OperationalGraph D)
  (current : G.Node)
  (q : D.Question) : Prop :=
  QuestionNotOnCurrentPath D G current q


def CandidateQuestion
  (D : SemanticDomain)
  (G : OperationalGraph D)
  (current : G.Node)
  (domainQuestions : SSet D.Question)
  (q : D.Question) : Prop :=
  q ∈ domainQuestions ∧
  FreshQuestionForCurrentPath D G current q


def CandidateSeparatingQuestion
  (D : SemanticDomain)
  (G : OperationalGraph D)
  (current : G.Node)
  (domainQuestions : SSet D.Question)
  (c₁ c₂ : D.Sample)
  (q : D.Question) : Prop :=
  CandidateQuestion D G current domainQuestions q ∧
  QuestionSeparatesPair D q c₁ c₂


def ExistingReusableSeparatingQuestion
  (D : SemanticDomain)
  (G : OperationalGraph D)
  (current : G.Node)
  (domainQuestions : SSet D.Question)
  (c₁ c₂ : D.Sample)
  (q : D.Question) : Prop :=
  ExistingReusableQuestion D G current q ∧
  CandidateSeparatingQuestion D G current domainQuestions c₁ c₂ q


def FreshSeparatingQuestion
  (D : SemanticDomain)
  (G : OperationalGraph D)
  (current : G.Node)
  (domainQuestions : SSet D.Question)
  (c₁ c₂ : D.Sample)
  (q : D.Question) : Prop :=
  CandidateSeparatingQuestion D G current domainQuestions c₁ c₂ q ∧
  ¬ ExistingReusableQuestion D G current q


/-
## 19. Priority policy in question selection

Formula:

`Chosen(chosen) := CandidateSeparating(chosen) ∧ (Reusable(chosen) ∨ ¬ ∃ q, ReusableSeparating(q))`
-/

def ChosenQuestionRespectsReusePriority
  (D : SemanticDomain)
  (G : OperationalGraph D)
  (current : G.Node)
  (domainQuestions : SSet D.Question)
  (c₁ c₂ : D.Sample)
  (chosen : D.Question) : Prop :=
  CandidateSeparatingQuestion D G current domainQuestions c₁ c₂ chosen ∧
  (
    ExistingReusableQuestion D G current chosen
    ∨
    ¬ ∃ q : D.Question,
      ExistingReusableSeparatingQuestion
        D
        G
        current
        domainQuestions
        c₁
        c₂
        q
  )


/-
## 20. Operational insertability of the separating question
-/

structure GraphExpansion
  (D : SemanticDomain)
  (domainQuestions : SSet D.Question)
  (beforeGraph : OperationalGraph D)
  (afterGraph : OperationalGraph D) where

  current :
    beforeGraph.Node

  chosen :
    D.Question

  acyclic_before :
    AcyclicOperationalGraph D beforeGraph

  acyclic_after :
    AcyclicOperationalGraph D afterGraph

  no_repeated_before :
    NoRepeatedQuestionOnPaths D beforeGraph

  no_repeated_after :
    NoRepeatedQuestionOnPaths D afterGraph


def ExpansionSeparatesPair
  (D : SemanticDomain)
  (domainQuestions : SSet D.Question)
  (beforeGraph : OperationalGraph D)
  (afterGraph : OperationalGraph D)
  (E : GraphExpansion D domainQuestions beforeGraph afterGraph)
  (c₁ c₂ : D.Sample) : Prop :=
  ChosenQuestionRespectsReusePriority
    D
    beforeGraph
    E.current
    domainQuestions
    c₁
    c₂
    E.chosen


/-
## 21. Global progressive expandability
-/

def PairReachesCurrent
  (D : SemanticDomain)
  (G : OperationalGraph D)
  (c₁ c₂ : D.Sample)
  (current : G.Node) : Prop :=
  OperationalReaches D G c₁ current ∧
  OperationalReaches D G c₂ current


def GloballyInsertableSeparatingQuestion
  (D : SemanticDomain)
  (G : OperationalGraph D)
  (samples : SSet D.Sample)
  (domainQuestions : SSet D.Question) : Prop :=
  ∀ c₁ : D.Sample,
    ∀ c₂ : D.Sample,
      NotYetDistinguished D G samples c₁ c₂ →
      ∃ current : G.Node,
        PairReachesCurrent D G c₁ c₂ current ∧
        ∃ q : D.Question,
          ChosenQuestionRespectsReusePriority
            D
            G
            current
            domainQuestions
            c₁
            c₂
            q


def GraphIsProgressivelyExpandable
  (D : SemanticDomain)
  (G : OperationalGraph D)
  (samples : SSet D.Sample)
  (domainQuestions : SSet D.Question) : Prop :=
  AcyclicOperationalGraph D G ∧
  NoRepeatedQuestionOnPaths D G ∧
  GloballyInsertableSeparatingQuestion D G samples domainQuestions


/-
## 22. Existence of a complete differentiating graph
-/

def FiniteSampleSet
  (D : SemanticDomain)
  (samples : SSet D.Sample) : Prop :=
  ∃ xs : List D.Sample,
    ∀ c : D.Sample,
      c ∈ samples ↔ c ∈ xs


def CompleteDifferentiatingOperationalGraphExists
  (D : SemanticDomain)
  (samples : SSet D.Sample) : Prop :=
  ∃ G : OperationalGraph D,
    GraphCoversSamples D G samples ∧
    AcyclicOperationalGraph D G ∧
    NoRepeatedQuestionOnPaths D G ∧
    CompleteDifferentiationGraph D G samples


axiom progressive_complete_graph_exists
  (D : SemanticDomain)
  (samples : SSet D.Sample)
  (domainQuestions : SSet D.Question)
  (initialGraph : OperationalGraph D) :
  FiniteSampleSet D samples →
  GraphCoversSamples D initialGraph samples →
  AcyclicOperationalGraph D initialGraph →
  NoRepeatedQuestionOnPaths D initialGraph →
  SeparatingQuestionBase D samples domainQuestions →
  GraphIsProgressivelyExpandable D initialGraph samples domainQuestions →
  CompleteDifferentiatingOperationalGraphExists D samples


theorem separating_base_with_expandability_implies_complete_graph_exists
  (D : SemanticDomain)
  (samples : SSet D.Sample)
  (domainQuestions : SSet D.Question)
  (initialGraph : OperationalGraph D) :
  FiniteSampleSet D samples →
  GraphCoversSamples D initialGraph samples →
  AcyclicOperationalGraph D initialGraph →
  NoRepeatedQuestionOnPaths D initialGraph →
  SeparatingQuestionBase D samples domainQuestions →
  GraphIsProgressivelyExpandable D initialGraph samples domainQuestions →
  CompleteDifferentiatingOperationalGraphExists D samples := by
  intro hFinite
  intro hCover
  intro hAcyclic
  intro hNoRepeat
  intro hSep
  intro hExpandable

  exact progressive_complete_graph_exists
    D
    samples
    domainQuestions
    initialGraph
    hFinite
    hCover
    hAcyclic
    hNoRepeat
    hSep
    hExpandable


/-
## 23. Graph construction state
-/

structure GraphConstructionState
  (D : SemanticDomain) where

  graph : OperationalGraph D


def GraphStateWellFormed
  (D : SemanticDomain)
  (samples : SSet D.Sample)
  (s : GraphConstructionState D) : Prop :=
  GraphCoversSamples D s.graph samples ∧
  AcyclicOperationalGraph D s.graph ∧
  NoRepeatedQuestionOnPaths D s.graph


def GraphStateComplete
  (D : SemanticDomain)
  (samples : SSet D.Sample)
  (s : GraphConstructionState D) : Prop :=
  GraphStateWellFormed D samples s ∧
  CompleteDifferentiationGraph D s.graph samples


/-
## 24. Progressive builder without fuel

The builder does not use external fuel.

Termination derives from the internal measure:

`badPairCount`.

Formula:

`step?(s) = some t → badPairCount(t) < badPairCount(s)`

Correct stopping formula:

`step?(s) = none → badPairCount(s) = 0`

Completeness formula:

`badPairCount(s) = 0 → GraphStateComplete(s)`
-/

structure GraphProgressBuilder
  (D : SemanticDomain)
  (samples : SSet D.Sample)
  (domainQuestions : SSet D.Question) where

  badPairCount :
    GraphConstructionState D → Nat

  step? :
    GraphConstructionState D → Option (GraphConstructionState D)

  step_decreases :
    ∀ s t : GraphConstructionState D,
      step? s = some t →
      badPairCount t < badPairCount s

  step_preserves_wellformed :
    ∀ s t : GraphConstructionState D,
      GraphStateWellFormed D samples s →
      step? s = some t →
      GraphStateWellFormed D samples t

  complete_if_zero :
    ∀ s : GraphConstructionState D,
      GraphStateWellFormed D samples s →
      badPairCount s = 0 →
      GraphStateComplete D samples s

  stops_implies_zero :
    ∀ s : GraphConstructionState D,
      GraphStateWellFormed D samples s →
      step? s = none →
      badPairCount s = 0


/-
## 25. Execution of the builder without fuel

Formula:

`run(s) = s`

if:

`step?(s) = none`

otherwise:

`run(s) = run(t)`

if:

`step?(s) = some t`.
-/

def runGraphBuilder
  (D : SemanticDomain)
  (samples : SSet D.Sample)
  (domainQuestions : SSet D.Question)
  (B : GraphProgressBuilder D samples domainQuestions)
  (s : GraphConstructionState D) :
  GraphConstructionState D :=

  match hstep : B.step? s with
  | none =>
      s

  | some t =>
      runGraphBuilder D samples domainQuestions B t

termination_by B.badPairCount s

decreasing_by
  exact B.step_decreases s t hstep


/-
## 26. Abstract correctness of the builder without fuel
-/

theorem runGraphBuilder_complete
  (D : SemanticDomain)
  (samples : SSet D.Sample)
  (domainQuestions : SSet D.Question)
  (B : GraphProgressBuilder D samples domainQuestions)
  (s : GraphConstructionState D) :
  GraphStateWellFormed D samples s →
  GraphStateComplete
    D
    samples
    (runGraphBuilder D samples domainQuestions B s) := by

  intro hWell

  cases hstep : B.step? s with

  | none =>
      rw [runGraphBuilder]
      rw [hstep]

      have hzero : B.badPairCount s = 0 :=
        B.stops_implies_zero s hWell hstep

      exact B.complete_if_zero s hWell hzero

  | some t =>
      have hWellT : GraphStateWellFormed D samples t :=
        B.step_preserves_wellformed s t hWell hstep

      have hRec :
        GraphStateComplete
          D
          samples
          (runGraphBuilder D samples domainQuestions B t) :=
        runGraphBuilder_complete D samples domainQuestions B t hWellT

      rw [runGraphBuilder]
      rw [hstep]

      exact hRec

termination_by B.badPairCount s

decreasing_by
  exact B.step_decreases s t hstep


def ProgressBuilderExists
  (D : SemanticDomain)
  (samples : SSet D.Sample)
  (domainQuestions : SSet D.Question) : Prop :=
  ∃ B : GraphProgressBuilder D samples domainQuestions,
    True


theorem progress_builder_exists_implies_finite_success
  (D : SemanticDomain)
  (samples : SSet D.Sample)
  (domainQuestions : SSet D.Question) :
  ProgressBuilderExists D samples domainQuestions →
  ∀ initialState : GraphConstructionState D,
    GraphStateWellFormed D samples initialState →
    ∃ B : GraphProgressBuilder D samples domainQuestions,
      GraphStateComplete
        D
        samples
        (runGraphBuilder
          D
          samples
          domainQuestions
          B
          initialState) := by

  intro hExists
  intro initialState
  intro hWell

  rcases hExists with ⟨B, hTrivial⟩

  exact
    ⟨B,
      runGraphBuilder_complete
        D
        samples
        domainQuestions
        B
        initialState
        hWell⟩


/-
## 27. Target-guided induction objects from D2 toward G1

From this point onward, we no longer build an autonomous graph `G2`.

Domain `D2` is used as a source of evidence.

Graph `G1` remains the target graph.

For each target operational QA:

`x1 : OperationalQA D1 G1`

we build induction objects containing minimal groups of source QAs:

`P2 ⊆ QA D2`

capable of inducing `x1`.

Formula:

`PremiseSetSupportsTarget(P2,x1)`

means:

there exists a transdomain rule `rule` such that:

1. `rule.conclusion = OperationalQAAsSemanticQA(x1)`;
2. all premises of the rule are contained in `P2`.

Formula:

`∃ rule, rule ∈ rules ∧ rule.conclusion = Sem(x1) ∧ rule.premises ⊆ P2`

A group `P2` is minimal if there does not exist a proper subset `P2' ⊂ P2`
that still supports the same target.
-/

def PremiseSetSupportsTarget
  (D₂ D₁ : SemanticDomain)
  (G₁ : OperationalGraph D₁)
  (rules : SSet (TransDomainRule D₂ D₁))
  (premises₂ : SSet (QA D₂))
  (target : OperationalQA D₁ G₁) : Prop :=
  ∃ rule : TransDomainRule D₂ D₁,
    rule ∈ rules ∧
    rule.conclusion = OperationalQAAsSemanticQA D₁ G₁ target ∧
    Subset rule.premises premises₂


def MinimalPremiseSetForTarget
  (D₂ D₁ : SemanticDomain)
  (G₁ : OperationalGraph D₁)
  (rules : SSet (TransDomainRule D₂ D₁))
  (premises₂ : SSet (QA D₂))
  (target : OperationalQA D₁ G₁) : Prop :=
  PremiseSetSupportsTarget D₂ D₁ G₁ rules premises₂ target ∧
  ¬ ∃ smaller : SSet (QA D₂),
      ProperSubset smaller premises₂ ∧
      PremiseSetSupportsTarget D₂ D₁ G₁ rules smaller target


/-
An induction object associates a target operational QA `target` with a minimal
set of source QAs `premises₂`.

Formula:

`TargetInductionObject(target,premises₂)`

with:

`MinimalPremiseSetForTarget(premises₂,target)`

These objects are constructed before inference on a specific sample.

They are independent of the sample `c2`.

During inference, the system will choose among these objects those compatible
with the current context and the source sample.
-/

structure TargetInductionObject
  (D₂ D₁ : SemanticDomain)
  (G₁ : OperationalGraph D₁)
  (rules : SSet (TransDomainRule D₂ D₁)) where

  target :
    OperationalQA D₁ G₁

  premises₂ :
    SSet (QA D₂)

  minimal :
    MinimalPremiseSetForTarget D₂ D₁ G₁ rules premises₂ target


/-
The induction object system is the set of available objects.

Formula:

`objects ⊆ TargetInductionObject(D2,D1,G1,rules)`

This structure represents the result of the method:

`BuildInductionObjects(G1, rules)`

that is:

given the target graph `G1` and the transdomain rules, build all minimal
induction objects toward the operational QAs of `G1`.
-/

structure TargetInductionObjectSystem
  (D₂ D₁ : SemanticDomain)
  (G₁ : OperationalGraph D₁) where

  rules :
    SSet (TransDomainRule D₂ D₁)

  objects :
    SSet (TargetInductionObject D₂ D₁ G₁ rules)


def ObjectTargets
  (D₂ D₁ : SemanticDomain)
  (G₁ : OperationalGraph D₁)
  (S : TargetInductionObjectSystem D₂ D₁ G₁)
  (obj : TargetInductionObject D₂ D₁ G₁ S.rules)
  (target : OperationalQA D₁ G₁) : Prop :=
  obj ∈ S.objects ∧
  obj.target = target


/-
## 28. Induction context and contextual cost

During transdomain inference, source QAs already used to induce ancestor
operational QAs in `G1` must not be requested again.

For this reason we introduce a context.

The context contains:

`assumedSource`

the set of source QAs of `D2` already acquired and assumed true in the current
induced path.

`inducedTarget`

the set of operational QAs of `G1` already induced.

Formula:

`Context = (assumedSource, inducedTarget)`

A source QA already in the context has zero cost.

Ideal cost formula:

`Cost(P2 | Context) = cost(P2 \ Context.assumedSource)`

Here we do not formalize the concrete cardinality of a predicative set.

Therefore we introduce an abstract cost model.
-/

structure TargetInductionContext
  (D₂ D₁ : SemanticDomain)
  (G₁ : OperationalGraph D₁) where

  assumedSource :
    SSet (QA D₂)

  inducedTarget :
    SSet (OperationalQA D₁ G₁)


structure SourceQuestionCostModel
  (D₂ : SemanticDomain) where

  cost :
    SSet (QA D₂) →
    SSet (QA D₂) →
    Nat


def ContextualCost
  (D₂ : SemanticDomain)
  (M : SourceQuestionCostModel D₂)
  (known : SSet (QA D₂))
  (premises₂ : SSet (QA D₂)) : Nat :=
  M.cost known premises₂


/-
A source question has already been used in the context if there exists an
already assumed QA with the same question.

Formula:

`SourceQuestionAlreadyUsed(known,q) := ∃ x, x ∈ known ∧ x.q = q`

If a question has already been used in the ancestor context, then we do not want
to request a new different answer to the same question.

Therefore a set of premises is allowed in the context if every QA in it whose
question has already been used is already itself in the context.

Formula:

`ContextAllowsPremiseSet(Context,P2) := ∀ x ∈ P2, SourceQuestionAlreadyUsed(Context,x.q) → x ∈ Context`
-/

def SourceQuestionAlreadyUsed
  (D₂ : SemanticDomain)
  (known : SSet (QA D₂))
  (q : D₂.Question) : Prop :=
  ∃ x : QA D₂,
    x ∈ known ∧
    x.q = q


def ContextAllowsPremiseSet
  (D₂ D₁ : SemanticDomain)
  (G₁ : OperationalGraph D₁)
  (ctx : TargetInductionContext D₂ D₁ G₁)
  (premises₂ : SSet (QA D₂)) : Prop :=
  ∀ x : QA D₂,
    x ∈ premises₂ →
    SourceQuestionAlreadyUsed D₂ ctx.assumedSource x.q →
    x ∈ ctx.assumedSource


/-
A set of premises is optimal in the context if:

1. it supports the target;
2. it is allowed in the context;
3. there is no other allowed set that supports the same target and has lower
   contextual cost.

Formula:

`ContextuallyOptimalPremiseSet(P2,target,ctx)`

means:

`PremiseSetSupportsTarget(P2,target)`
`∧ ContextAllowsPremiseSet(ctx,P2)`
`∧ ¬ ∃ P2', Supports(P2',target) ∧ Allowed(ctx,P2') ∧ Cost(P2'|ctx) < Cost(P2|ctx)`

This formalizes the idea:

choose the group of premises requiring the smallest number of new questions,
reusing as much as possible the QAs already acquired along the ancestors of the
induced trace.
-/

def ContextuallyOptimalPremiseSetForTarget
  (D₂ D₁ : SemanticDomain)
  (G₁ : OperationalGraph D₁)
  (rules : SSet (TransDomainRule D₂ D₁))
  (M : SourceQuestionCostModel D₂)
  (ctx : TargetInductionContext D₂ D₁ G₁)
  (premises₂ : SSet (QA D₂))
  (target : OperationalQA D₁ G₁) : Prop :=
  PremiseSetSupportsTarget D₂ D₁ G₁ rules premises₂ target ∧
  ContextAllowsPremiseSet D₂ D₁ G₁ ctx premises₂ ∧
  ¬ ∃ other : SSet (QA D₂),
      PremiseSetSupportsTarget D₂ D₁ G₁ rules other target ∧
      ContextAllowsPremiseSet D₂ D₁ G₁ ctx other ∧
      ContextualCost D₂ M ctx.assumedSource other
        <
      ContextualCost D₂ M ctx.assumedSource premises₂


/-
## 29. Induced reachability in the target graph G1

A target operational QA `x1` must not be considered inducible only because
there exists a group of source premises that supports it.

It must also be reachable in the graph `G1` through a chain of already induced
operational QAs.

Therefore transdomain inference must respect the operational structure of the
target graph.

We first define induced reachability of the nodes of `G1`.

A node is inductively reachable if:

1. it is a root;
2. or there exists an already induced operational QA that leads to that node
   through an edge of `G1`.

Formula:

`InducedNodeReachable(root)`

if:

`root ∈ G1.roots`

Formula of the step:

`InducedNodeReachable(src) ∧ inducedTarget(src,r) ∧ edge(src,r,dst) → InducedNodeReachable(dst)`
-/

inductive TargetInducedNodeReachable
  (D₂ D₁ : SemanticDomain)
  (G₁ : OperationalGraph D₁)
  (ctx : TargetInductionContext D₂ D₁ G₁) :
  G₁.Node → Prop where

  | root :
      {n : G₁.Node} →
      n ∈ G₁.roots →
      TargetInducedNodeReachable D₂ D₁ G₁ ctx n

  | step :
      {src dst : G₁.Node} →
      (r : D₁.Answer (G₁.questionOf src)) →
      TargetInducedNodeReachable D₂ D₁ G₁ ctx src →
      ({ src := src, r := r } : OperationalQA D₁ G₁) ∈ ctx.inducedTarget →
      G₁.edge src r dst →
      TargetInducedNodeReachable D₂ D₁ G₁ ctx dst


/-
A target operational QA is inducible in the context only if:

1. its source node is inductively reachable;
2. its answer is active in the graph `G1`.

Formula:

`TargetOperationalQAInducibleInContext(ctx,x1) := ReachInduced(ctx,x1.src) ∧ active(x1.src,x1.r)`
-/

def TargetOperationalQAInducibleInContext
  (D₂ D₁ : SemanticDomain)
  (G₁ : OperationalGraph D₁)
  (ctx : TargetInductionContext D₂ D₁ G₁)
  (target : OperationalQA D₁ G₁) : Prop :=
  TargetInducedNodeReachable D₂ D₁ G₁ ctx target.src ∧
  G₁.active target.src target.r


/-
## 30. Satisfaction of premises by a source sample

A group of premises `P2` is satisfied by a sample `c2` if all source QAs
contained in `P2` are true for `c2`.

Formula:

`PremiseSetSatisfiedBySample(c2,P2) := ∀ x2 ∈ P2, holds(x2.q,c2,x2.r)`

Since in this new architecture we no longer build an autonomous graph `G2`,
verification takes place directly in the source domain `D2`.
-/

def PremiseSetSatisfiedBySample
  (D₂ : SemanticDomain)
  (c₂ : D₂.Sample)
  (premises₂ : SSet (QA D₂)) : Prop :=
  ∀ x₂ : QA D₂,
    x₂ ∈ premises₂ →
    D₂.holds x₂.q c₂ x₂.r


/-
A target operational QA is induced by a source sample in the context if:

1. the target QA is reachable in graph `G1` with respect to the already induced
   trace;
2. there exists a contextually optimal set of premises;
3. the source sample satisfies that set of premises.

Formula:

`TargetQAInducedBySource(c2,ctx,x1) :=`
`ReachableInG1(ctx,x1)`
`∧ ∃ P2, ContextuallyOptimal(P2,x1,ctx) ∧ Satisfied(c2,P2)`
-/

def TargetQAInducedBySource
  (D₂ D₁ : SemanticDomain)
  (G₁ : OperationalGraph D₁)
  (rules : SSet (TransDomainRule D₂ D₁))
  (M : SourceQuestionCostModel D₂)
  (ctx : TargetInductionContext D₂ D₁ G₁)
  (c₂ : D₂.Sample)
  (target : OperationalQA D₁ G₁) : Prop :=
  TargetOperationalQAInducibleInContext D₂ D₁ G₁ ctx target ∧
  ∃ premises₂ : SSet (QA D₂),
    ContextuallyOptimalPremiseSetForTarget
      D₂
      D₁
      G₁
      rules
      M
      ctx
      premises₂
      target
    ∧
    PremiseSetSatisfiedBySample D₂ c₂ premises₂


/-
## 31. Context update after an induction

When a target operational QA `target` is induced through a set of premises
`premises₂`, the context is updated as follows:

1. the source premises are added to the assumed source QAs;
2. the target QA is added to the induced operational QAs in `G1`.

Formula:

`assumedSource' = assumedSource ∪ premises₂`

`inducedTarget' = inducedTarget ∪ { target }`

This is the mechanism that makes source QAs used to induce ancestors of the
trace in `G1` contextual.
-/

def AddPremiseSetToKnown
  (D₂ : SemanticDomain)
  (known : SSet (QA D₂))
  (premises₂ : SSet (QA D₂)) : SSet (QA D₂) :=
  fun x =>
    x ∈ known ∨ x ∈ premises₂


def AddTargetToInduced
  (D₂ D₁ : SemanticDomain)
  (G₁ : OperationalGraph D₁)
  (induced : SSet (OperationalQA D₁ G₁))
  (target : OperationalQA D₁ G₁) : SSet (OperationalQA D₁ G₁) :=
  fun x =>
    x ∈ induced ∨ x = target


def UpdateTargetInductionContext
  (D₂ D₁ : SemanticDomain)
  (G₁ : OperationalGraph D₁)
  (ctx : TargetInductionContext D₂ D₁ G₁)
  (premises₂ : SSet (QA D₂))
  (target : OperationalQA D₁ G₁) :
  TargetInductionContext D₂ D₁ G₁ :=
  {
    assumedSource :=
      AddPremiseSetToKnown D₂ ctx.assumedSource premises₂

    inducedTarget :=
      AddTargetToInduced D₂ D₁ G₁ ctx.inducedTarget target
  }


/-
## 32. Target-guided transdomain inference step

A valid transdomain inference step chooses:

1. a target operational QA `target` reachable in the context;
2. a contextually optimal set of source premises `premises₂`;
3. a source sample `c2` satisfying those premises.

Then it updates the context by adding `premises₂` and `target`.

Formula:

`ValidStep(ctx,c2,premises₂,target) :=`
`TargetOperationalQAInducibleInContext(ctx,target)`
`∧ ContextuallyOptimalPremiseSetForTarget(premises₂,target,ctx)`
`∧ PremiseSetSatisfiedBySample(c2,premises₂)`
-/

def ValidTargetGuidedInductionStep
  (D₂ D₁ : SemanticDomain)
  (G₁ : OperationalGraph D₁)
  (rules : SSet (TransDomainRule D₂ D₁))
  (M : SourceQuestionCostModel D₂)
  (ctx : TargetInductionContext D₂ D₁ G₁)
  (c₂ : D₂.Sample)
  (premises₂ : SSet (QA D₂))
  (target : OperationalQA D₁ G₁) : Prop :=
  TargetOperationalQAInducibleInContext D₂ D₁ G₁ ctx target ∧
  ContextuallyOptimalPremiseSetForTarget
    D₂
    D₁
    G₁
    rules
    M
    ctx
    premises₂
    target
  ∧
  PremiseSetSatisfiedBySample D₂ c₂ premises₂


/-
## 33. State and method of transdomain inference

The state of transdomain inference contains the current context.

Formula:

`TargetGuidedInferenceState = { ctx }`

The inference method is abstract.

It contains:

`badTargetCount`

number of target operational QAs still potentially inducible and unresolved.

`step?`

optional step.

`step_decreases`

each step decreases `badTargetCount`.

`step_preserves_validity`

each step preserves the validity of the context.

`stops_when_closed`

if the method stops, the induced trace is closed with respect to the reachable
and inducible QAs in the current context.

This structure allows specifying the method without yet fixing a concrete
computational algorithm.
-/

structure TargetGuidedInferenceState
  (D₂ D₁ : SemanticDomain)
  (G₁ : OperationalGraph D₁) where

  ctx :
    TargetInductionContext D₂ D₁ G₁


def TargetInferenceContextValid
  (D₂ D₁ : SemanticDomain)
  (G₁ : OperationalGraph D₁)
  (state : TargetGuidedInferenceState D₂ D₁ G₁) : Prop :=
  True


def TargetTraceClosed
  (D₂ D₁ : SemanticDomain)
  (G₁ : OperationalGraph D₁)
  (rules : SSet (TransDomainRule D₂ D₁))
  (M : SourceQuestionCostModel D₂)
  (c₂ : D₂.Sample)
  (state : TargetGuidedInferenceState D₂ D₁ G₁) : Prop :=
  ∀ target : OperationalQA D₁ G₁,
    TargetQAInducedBySource D₂ D₁ G₁ rules M state.ctx c₂ target →
    target ∈ state.ctx.inducedTarget


structure TargetGuidedInferenceMethod
  (D₂ D₁ : SemanticDomain)
  (G₁ : OperationalGraph D₁)
  (rules : SSet (TransDomainRule D₂ D₁))
  (M : SourceQuestionCostModel D₂)
  (c₂ : D₂.Sample) where

  badTargetCount :
    TargetGuidedInferenceState D₂ D₁ G₁ → Nat

  step? :
    TargetGuidedInferenceState D₂ D₁ G₁ →
    Option (TargetGuidedInferenceState D₂ D₁ G₁)

  step_decreases :
    ∀ s t : TargetGuidedInferenceState D₂ D₁ G₁,
      step? s = some t →
      badTargetCount t < badTargetCount s

  step_preserves_validity :
    ∀ s t : TargetGuidedInferenceState D₂ D₁ G₁,
      TargetInferenceContextValid D₂ D₁ G₁ s →
      step? s = some t →
      TargetInferenceContextValid D₂ D₁ G₁ t

  stops_when_closed :
    ∀ s : TargetGuidedInferenceState D₂ D₁ G₁,
      TargetInferenceContextValid D₂ D₁ G₁ s →
      step? s = none →
      TargetTraceClosed D₂ D₁ G₁ rules M c₂ s


/-
## 34. Execution of the transdomain method without fuel

As with the builder of `G1`, we do not use fuel.

Termination derives from the measure:

`badTargetCount`.

Formula:

`step?(s) = some t → badTargetCount(t) < badTargetCount(s)`
-/

def runTargetGuidedInference
  (D₂ D₁ : SemanticDomain)
  (G₁ : OperationalGraph D₁)
  (rules : SSet (TransDomainRule D₂ D₁))
  (M : SourceQuestionCostModel D₂)
  (c₂ : D₂.Sample)
  (Method : TargetGuidedInferenceMethod D₂ D₁ G₁ rules M c₂)
  (s : TargetGuidedInferenceState D₂ D₁ G₁) :
  TargetGuidedInferenceState D₂ D₁ G₁ :=

  match hstep : Method.step? s with
  | none =>
      s

  | some t =>
      runTargetGuidedInference D₂ D₁ G₁ rules M c₂ Method t

termination_by Method.badTargetCount s

decreasing_by
  exact Method.step_decreases s t hstep


theorem runTargetGuidedInference_closed
  (D₂ D₁ : SemanticDomain)
  (G₁ : OperationalGraph D₁)
  (rules : SSet (TransDomainRule D₂ D₁))
  (M : SourceQuestionCostModel D₂)
  (c₂ : D₂.Sample)
  (Method : TargetGuidedInferenceMethod D₂ D₁ G₁ rules M c₂)
  (s : TargetGuidedInferenceState D₂ D₁ G₁) :
  TargetInferenceContextValid D₂ D₁ G₁ s →
  TargetTraceClosed
    D₂
    D₁
    G₁
    rules
    M
    c₂
    (runTargetGuidedInference D₂ D₁ G₁ rules M c₂ Method s) := by

  intro hValid

  cases hstep : Method.step? s with

  | none =>
      rw [runTargetGuidedInference]
      rw [hstep]
      exact Method.stops_when_closed s hValid hstep

  | some t =>
      have hValidT :
        TargetInferenceContextValid D₂ D₁ G₁ t :=
        Method.step_preserves_validity s t hValid hstep

      have hRec :
        TargetTraceClosed
          D₂
          D₁
          G₁
          rules
          M
          c₂
          (runTargetGuidedInference D₂ D₁ G₁ rules M c₂ Method t) :=
        runTargetGuidedInference_closed D₂ D₁ G₁ rules M c₂ Method t hValidT

      rw [runTargetGuidedInference]
      rw [hstep]

      exact hRec

termination_by Method.badTargetCount s

decreasing_by
  exact Method.step_decreases s t hstep


/-
## 35. Correlated samples in domain D1

After inducing a trace inside `G1`, we want to return a set of samples of
domain `D1` compatible with that trace.

A sample `c1` is compatible with an induced context if every induced operational
QA is actually reached by `c1` in `G1`.

Formula:

`CompatibleWithInducedTrace(c1,ctx) := ∀ x1 ∈ ctx.inducedTarget, OperationalQAReached(D1,G1,c1,x1)`

The result of transdomain inference is:

`AssociatedSamples(c2) = { c1 ∈ samples1 | CompatibleWithInducedTrace(c1, finalContext) }`

This form returns a set, not necessarily a single sample.

If the induced trace is complete and `G1` completely differentiates the samples,
the set may reduce to a single sample.
-/

def CompatibleWithInducedTargetTrace
  (D₂ D₁ : SemanticDomain)
  (G₁ : OperationalGraph D₁)
  (ctx : TargetInductionContext D₂ D₁ G₁)
  (c₁ : D₁.Sample) : Prop :=
  ∀ x₁ : OperationalQA D₁ G₁,
    x₁ ∈ ctx.inducedTarget →
    OperationalQAReached D₁ G₁ c₁ x₁


def AssociatedSamplesFromContext
  (D₂ D₁ : SemanticDomain)
  (G₁ : OperationalGraph D₁)
  (samples₁ : SSet D₁.Sample)
  (ctx : TargetInductionContext D₂ D₁ G₁) : SSet D₁.Sample :=
  fun c₁ =>
    c₁ ∈ samples₁ ∧
    CompatibleWithInducedTargetTrace D₂ D₁ G₁ ctx c₁


def AssociatedSamplesFromInference
  (D₂ D₁ : SemanticDomain)
  (G₁ : OperationalGraph D₁)
  (rules : SSet (TransDomainRule D₂ D₁))
  (M : SourceQuestionCostModel D₂)
  (samples₁ : SSet D₁.Sample)
  (c₂ : D₂.Sample)
  (Method : TargetGuidedInferenceMethod D₂ D₁ G₁ rules M c₂)
  (initialState : TargetGuidedInferenceState D₂ D₁ G₁) :
  SSet D₁.Sample :=
  let finalState :=
    runTargetGuidedInference D₂ D₁ G₁ rules M c₂ Method initialState

  AssociatedSamplesFromContext
    D₂
    D₁
    G₁
    samples₁
    finalState.ctx


/-
## 36. Operational paths and partial completion

In the case where the trace induced by `c2` is partial, we do not use reachable
terminals as a shortcut.

We use all complete operational paths that extend the induced trace.

An operational path is represented abstractly as a set of operational QAs plus
structural properties:

1. it starts from a root;
2. it is locally coherent with the edges;
3. it reaches a terminal closure.

Formula:

`CompleteOperationalPath(p) := starts_at_root ∧ locally_connected ∧ complete_to_terminal`

Extension formula:

`PathExtendsInducedTrace(ctx,p) := ∀ x1 ∈ ctx.inducedTarget, x1 ∈ p`

Compatibility formula:

`SampleCompatibleWithOperationalPath(c1,p) := ∀ x1 ∈ p, OperationalQAReached(c1,x1)`
-/

structure OperationalPath
  (D : SemanticDomain)
  (G : OperationalGraph D) where

  occurs :
    SSet (OperationalQA D G)

  starts_at_root :
    Prop

  locally_connected :
    Prop

  complete_to_terminal :
    Prop


def CompleteOperationalPath
  (D : SemanticDomain)
  (G : OperationalGraph D)
  (p : OperationalPath D G) : Prop :=
  p.starts_at_root ∧
  p.locally_connected ∧
  p.complete_to_terminal


def OperationalPathContains
  (D : SemanticDomain)
  (G : OperationalGraph D)
  (p : OperationalPath D G)
  (x : OperationalQA D G) : Prop :=
  x ∈ p.occurs


def PathExtendsInducedTrace
  (D₂ D₁ : SemanticDomain)
  (G₁ : OperationalGraph D₁)
  (ctx : TargetInductionContext D₂ D₁ G₁)
  (p : OperationalPath D₁ G₁) : Prop :=
  ∀ x₁ : OperationalQA D₁ G₁,
    x₁ ∈ ctx.inducedTarget →
    x₁ ∈ p.occurs


def SampleCompatibleWithOperationalPath
  (D : SemanticDomain)
  (G : OperationalGraph D)
  (c : D.Sample)
  (p : OperationalPath D G) : Prop :=
  ∀ x : OperationalQA D G,
    x ∈ p.occurs →
    OperationalQAReached D G c x


def PossibleAssociatedByPathCompletion
  (D₂ D₁ : SemanticDomain)
  (G₁ : OperationalGraph D₁)
  (ctx : TargetInductionContext D₂ D₁ G₁)
  (c₁ : D₁.Sample) : Prop :=
  CompatibleWithInducedTargetTrace D₂ D₁ G₁ ctx c₁ ∧
  ∃ p : OperationalPath D₁ G₁,
    CompleteOperationalPath D₁ G₁ p ∧
    PathExtendsInducedTrace D₂ D₁ G₁ ctx p ∧
    SampleCompatibleWithOperationalPath D₁ G₁ c₁ p


def PossibleAssociatedSamplesByPathCompletion
  (D₂ D₁ : SemanticDomain)
  (G₁ : OperationalGraph D₁)
  (samples₁ : SSet D₁.Sample)
  (ctx : TargetInductionContext D₂ D₁ G₁) : SSet D₁.Sample :=
  fun c₁ =>
    c₁ ∈ samples₁ ∧
    PossibleAssociatedByPathCompletion D₂ D₁ G₁ ctx c₁


/-
## 37. External ordering of operational QAs

The operational signature is a set:

`OperationalSignature(c) = { x | OperationalQAReached(c,x) }`

For some operational uses, such as vector comparison, ranking, or dissimilarity
matrices, it is useful to transform the signature into an ordered vector.

Formula:

`OrderedOperationalIdentifier(c,i) := OperationalQAReached(c, operationalAt(i))`
-/

structure OperationalQAOrdering
  (D : SemanticDomain)
  (G : OperationalGraph D) where

  indexType : Type

  operationalAt :
    indexType → OperationalQA D G

  covers_operational :
    ∀ x : OperationalQA D G,
      ∃ i : indexType,
        operationalAt i = x


def OrderedOperationalIdentifier
  (D : SemanticDomain)
  (G : OperationalGraph D)
  (Ord : OperationalQAOrdering D G)
  (c : D.Sample)
  (i : Ord.indexType) : Prop :=
  OperationalQAReached D G c (Ord.operationalAt i)


axiom ordered_operational_identifier_equiv_signature
  (D : SemanticDomain)
  (G : OperationalGraph D)
  (Ord : OperationalQAOrdering D G)
  (c₁ c₂ : D.Sample) :
  (∀ i : Ord.indexType,
    OrderedOperationalIdentifier D G Ord c₁ i ↔
    OrderedOperationalIdentifier D G Ord c₂ i)
  ↔
  SameOperationalQASignature D G c₁ c₂


/-
## 38. External ordering of terminals

Terminals remain available as closure of operational paths.

The terminal signature can be ordered, but it does not replace the operational
signature in transdomain associations.
-/

structure TerminalOrdering
  (D : SemanticDomain)
  (G : OperationalGraph D) where

  indexType : Type

  terminalAt :
    indexType → TerminalQA D G

  terminal_is_structural :
    ∀ i : indexType,
      TerminalQAIsStructurallyTerminal D G (terminalAt i)

  covers_terminal :
    ∀ t : TerminalQA D G,
      TerminalQAIsStructurallyTerminal D G t →
      ∃ i : indexType,
        terminalAt i = t


def OrderedTerminalIdentifier
  (D : SemanticDomain)
  (G : OperationalGraph D)
  (Ord : TerminalOrdering D G)
  (c : D.Sample)
  (i : Ord.indexType) : Prop :=
  TerminalQAReached D G c (Ord.terminalAt i)


axiom ordered_identifier_equiv_terminal_signature
  (D : SemanticDomain)
  (G : OperationalGraph D)
  (Ord : TerminalOrdering D G)
  (c₁ c₂ : D.Sample) :
  (∀ i : Ord.indexType,
    OrderedTerminalIdentifier D G Ord c₁ i ↔
    OrderedTerminalIdentifier D G Ord c₂ i)
  ↔
  SameTerminalSignature D G c₁ c₂


/-
## 39. Final synthesis

The specification produces four conceptual methods.

### 1. Method for constructing G1

Input:

`samples1 : SSet D1.Sample`

`domainQuestions1 : SSet D1.Question`

Output:

`G1 : OperationalGraph D1`

Goal:

`CompleteDifferentiationGraph D1 G1 samples1`

that is:

`∀ c1 c1' ∈ samples1, c1 ≠ c1' → OperationalSignature(c1) ≠ OperationalSignature(c1')`

### 2. Method for inference in G1

Input:

`c1 : D1.Sample`

Output:

`OperationalSignature(c1)`

Formula:

`OperationalSignature(c1) = { x1 | OperationalQAReached D1 G1 c1 x1 }`

### 3. Method for constructing D2 → G1 induction objects

Input:

`G1`

`rules : SSet (TransDomainRule D2 D1)`

Output:

`TargetInductionObjectSystem D2 D1 G1`

For each target operational QA `x1`, it constructs minimal groups of source QAs
`P2` such that:

`P2 ⟹ x1`

Formula:

`MinimalPremiseSetForTarget(P2,x1)`

that is:

`PremiseSetSupportsTarget(P2,x1)`
`∧ ¬ ∃ P2' ⊂ P2, PremiseSetSupportsTarget(P2',x1)`

### 4. Method for target-guided transdomain inference

Input:

`c2 : D2.Sample`

Procedure:

1. it starts from the initial context;
2. it considers only operational QAs reachable in `G1`;
3. for each reachable target QA, it selects contextually optimal source premise sets;
4. it reuses source QAs already acquired along ancestors;
5. it does not accumulate useless questions coming from inactive branches;
6. it progressively induces a trace in `G1`;
7. it returns the samples of `D1` compatible with the induced trace.

Output:

`AssociatedSamplesFromInference(c2) ⊆ D1.Sample`

Formula:

`AssociatedSamples(c2) = { c1 ∈ samples1 | ∀ x1 ∈ inducedTarget(c2), OperationalQAReached(D1,G1,c1,x1) }`

### Essential point

We do not build an autonomous graph `G2` to associate samples.

A graph built to differentiate the samples of `D2` could use questions that are
excellent for distinguishing `D2`, but useless for inducing graph `G1`.

Therefore domain `D2` is queried in a target-guided way:

`G1` guides the choice of source questions to ask in `D2`.

The criterion is not:

"differentiate D2"

but:

"induce, in the most economical and contextually coherent way, the next
operational QAs reachable in G1".

Formula of contextual cost:

`Cost(P2 | Context) = cost of the QAs of P2 not already assumed in the ancestor context`

Formula of target-guided induction:

`TargetQAInducedBySource(c2,ctx,x1) :=`
`TargetOperationalQAInducibleInContext(ctx,x1)`
`∧ ∃ P2, ContextuallyOptimalPremiseSetForTarget(P2,x1,ctx)`
`∧ PremiseSetSatisfiedBySample(c2,P2)`

Terminals remain important, but only as closure of operational paths, not as
an isolated association criterion.
-/

end SemanticSpec
