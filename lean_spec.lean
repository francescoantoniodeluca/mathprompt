namespace SemanticSpec

universe u v w

abbrev SSet (α : Type u) := α → Prop

instance {α : Type u} : Membership α (SSet α) where
  mem A x := A x

def Subset {α : Type u} (A B : SSet α) : Prop :=
  ∀ x : α, x ∈ A → x ∈ B

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

def FiniteSet {α : Type u} (A : SSet α) : Prop :=
  ∃ xs : List α,
    ∀ x : α,
      x ∈ A ↔ x ∈ xs


structure SemanticDomain where
  Sample   : Type u
  Question : Type v
  Answer   : Question → Type w
  holds    : (q : Question) → Sample → Answer q → Prop


structure QA (D : SemanticDomain) where
  q : D.Question
  r : D.Answer q

def CompleteProp
  (D : SemanticDomain)
  (c : D.Sample)
  (x : QA D) : Prop :=
  D.holds x.q c x.r

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

def Profile
  (D : SemanticDomain)
  (c : D.Sample) : SSet (QA D) :=
  fun x => D.holds x.q c x.r


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

structure SubordinateOperator
  (Sample : Type u) where
  op : (Sample → Prop) → (Sample → Prop)

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
  · rfl
  · exact ⟨r, hHold⟩


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

def AnswerContinues
  (D : SemanticDomain)
  (G : OperationalGraph D)
  (src : G.Node)
  (r : D.Answer (G.questionOf src)) : Prop :=
  ∃ dst : G.Node,
    G.edge src r dst


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

def GraphCoversSample
  (D : SemanticDomain)
  (G : OperationalGraph D)
  (c : D.Sample) : Prop :=
  (∃ root : G.Node, root ∈ G.roots) ∧
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

def TerminalSignature
  (D : SemanticDomain)
  (G : OperationalGraph D)
  (c : D.Sample) : SSet (TerminalQA D G) :=
  fun t =>
    TerminalQAReached D G c t


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

def CompleteDifferentiationGraph
  (D : SemanticDomain)
  (G : OperationalGraph D)
  (samples : SSet D.Sample) : Prop :=
  CompleteOperationalDifferentiationGraph D G samples


def QuestionSeparatesPair
  (D : SemanticDomain)
  (q : D.Question)
  (c₁ c₂ : D.Sample) : Prop :=
  ∃ r : D.Answer q,
    (D.holds q c₁ r ∧ ¬ D.holds q c₂ r)
    ∨
    (D.holds q c₂ r ∧ ¬ D.holds q c₁ r)

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

def NotYetDistinguished
  (D : SemanticDomain)
  (G : OperationalGraph D)
  (samples : SSet D.Sample)
  (c₁ c₂ : D.Sample) : Prop :=
  c₁ ∈ samples ∧
  c₂ ∈ samples ∧
  c₁ ≠ c₂ ∧
  SameOperationalQASignature D G c₁ c₂


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

def CandidateQuestion
  (D : SemanticDomain)
  (G : OperationalGraph D)
  (current : G.Node)
  (domainQuestions : SSet D.Question)
  (q : D.Question) : Prop :=
  q ∈ domainQuestions ∧
  QuestionNotOnCurrentPath D G current q

def CandidateSeparatingQuestion
  (D : SemanticDomain)
  (G : OperationalGraph D)
  (current : G.Node)
  (domainQuestions : SSet D.Question)
  (c₁ c₂ : D.Sample)
  (q : D.Question) : Prop :=
  CandidateQuestion D G current domainQuestions q ∧
  QuestionSeparatesPair D q c₁ c₂

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
      ExistingReusableQuestion D G current q ∧
      CandidateSeparatingQuestion D G current domainQuestions c₁ c₂ q
  )


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

axiom runGraphBuilder_complete
  (D : SemanticDomain)
  (samples : SSet D.Sample)
  (domainQuestions : SSet D.Question)
  (B : GraphProgressBuilder D samples domainQuestions)
  (s : GraphConstructionState D) :
  GraphStateWellFormed D samples s →
  GraphStateComplete
    D
    samples
    (runGraphBuilder D samples domainQuestions B s)


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
  (targetQA : OperationalQA D₁ G₁) : Prop :=
  obj ∈ S.objects ∧
  obj.target = targetQA


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

def TargetOperationalQAInducibleInContext
  (D₂ D₁ : SemanticDomain)
  (G₁ : OperationalGraph D₁)
  (ctx : TargetInductionContext D₂ D₁ G₁)
  (target : OperationalQA D₁ G₁) : Prop :=
  TargetInducedNodeReachable D₂ D₁ G₁ ctx target.src ∧
  G₁.active target.src target.r

def PremiseSetSatisfiedBySample
  (D₂ : SemanticDomain)
  (c₂ : D₂.Sample)
  (premises₂ : SSet (QA D₂)) : Prop :=
  ∀ x₂ : QA D₂,
    x₂ ∈ premises₂ →
    D₂.holds x₂.q c₂ x₂.r

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
      D₂ D₁ G₁ rules M ctx premises₂ target
    ∧
    PremiseSetSatisfiedBySample D₂ c₂ premises₂


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

def BadTarget
  (D₂ D₁ : SemanticDomain)
  (G₁ : OperationalGraph D₁)
  (rules : SSet (TransDomainRule D₂ D₁))
  (M : SourceQuestionCostModel D₂)
  (relevantTargets : SSet (OperationalQA D₁ G₁))
  (c₂ : D₂.Sample)
  (state : TargetGuidedInferenceState D₂ D₁ G₁)
  (target : OperationalQA D₁ G₁) : Prop :=
  target ∈ relevantTargets ∧
  TargetQAInducedBySource D₂ D₁ G₁ rules M state.ctx c₂ target ∧
  ¬ target ∈ state.ctx.inducedTarget

def TargetTraceClosed
  (D₂ D₁ : SemanticDomain)
  (G₁ : OperationalGraph D₁)
  (rules : SSet (TransDomainRule D₂ D₁))
  (M : SourceQuestionCostModel D₂)
  (relevantTargets : SSet (OperationalQA D₁ G₁))
  (c₂ : D₂.Sample)
  (state : TargetGuidedInferenceState D₂ D₁ G₁) : Prop :=
  ∀ target : OperationalQA D₁ G₁,
    ¬ BadTarget D₂ D₁ G₁ rules M relevantTargets c₂ state target

def TargetTraceClosedExpanded
  (D₂ D₁ : SemanticDomain)
  (G₁ : OperationalGraph D₁)
  (rules : SSet (TransDomainRule D₂ D₁))
  (M : SourceQuestionCostModel D₂)
  (relevantTargets : SSet (OperationalQA D₁ G₁))
  (c₂ : D₂.Sample)
  (state : TargetGuidedInferenceState D₂ D₁ G₁) : Prop :=
  ∀ target : OperationalQA D₁ G₁,
    target ∈ relevantTargets →
    TargetQAInducedBySource D₂ D₁ G₁ rules M state.ctx c₂ target →
    target ∈ state.ctx.inducedTarget

theorem closed_expanded_implies_closed
  (D₂ D₁ : SemanticDomain)
  (G₁ : OperationalGraph D₁)
  (rules : SSet (TransDomainRule D₂ D₁))
  (M : SourceQuestionCostModel D₂)
  (relevantTargets : SSet (OperationalQA D₁ G₁))
  (c₂ : D₂.Sample)
  (state : TargetGuidedInferenceState D₂ D₁ G₁) :
  TargetTraceClosedExpanded
    D₂ D₁ G₁ rules M relevantTargets c₂ state →
  TargetTraceClosed
    D₂ D₁ G₁ rules M relevantTargets c₂ state := by
  intro hExpanded
  intro target
  intro hBad
  rcases hBad with ⟨hRel, hInd, hNot⟩
  exact hNot (hExpanded target hRel hInd)


def InducedTargetMonotone
  (D₂ D₁ : SemanticDomain)
  (G₁ : OperationalGraph D₁)
  (s t : TargetGuidedInferenceState D₂ D₁ G₁) : Prop :=
  Subset s.ctx.inducedTarget t.ctx.inducedTarget

def StepAddsNewRelevantTarget
  (D₂ D₁ : SemanticDomain)
  (G₁ : OperationalGraph D₁)
  (relevantTargets : SSet (OperationalQA D₁ G₁))
  (s t : TargetGuidedInferenceState D₂ D₁ G₁) : Prop :=
  ∃ target : OperationalQA D₁ G₁,
    target ∈ relevantTargets ∧
    ¬ target ∈ s.ctx.inducedTarget ∧
    target ∈ t.ctx.inducedTarget

structure TargetGuidedInferenceMethod
  (D₂ D₁ : SemanticDomain)
  (G₁ : OperationalGraph D₁)
  (rules : SSet (TransDomainRule D₂ D₁))
  (M : SourceQuestionCostModel D₂)
  (c₂ : D₂.Sample) where
  relevantTargets :
    SSet (OperationalQA D₁ G₁)
  relevantTargets_finite :
    FiniteSet relevantTargets
  step? :
    TargetGuidedInferenceState D₂ D₁ G₁ →
    Option (TargetGuidedInferenceState D₂ D₁ G₁)
  step_preserves_validity :
    ∀ s t : TargetGuidedInferenceState D₂ D₁ G₁,
      TargetInferenceContextValid D₂ D₁ G₁ s →
      step? s = some t →
      TargetInferenceContextValid D₂ D₁ G₁ t
  step_monotone :
    ∀ s t : TargetGuidedInferenceState D₂ D₁ G₁,
      step? s = some t →
      InducedTargetMonotone D₂ D₁ G₁ s t
  step_adds_new_target :
    ∀ s t : TargetGuidedInferenceState D₂ D₁ G₁,
      step? s = some t →
      StepAddsNewRelevantTarget D₂ D₁ G₁ relevantTargets s t
  step_adds_only_relevant :
    ∀ s t : TargetGuidedInferenceState D₂ D₁ G₁,
      step? s = some t →
      ∀ target : OperationalQA D₁ G₁,
        target ∈ t.ctx.inducedTarget →
        ¬ target ∈ s.ctx.inducedTarget →
        target ∈ relevantTargets
  stops_when_closed :
    ∀ s : TargetGuidedInferenceState D₂ D₁ G₁,
      TargetInferenceContextValid D₂ D₁ G₁ s →
      step? s = none →
      TargetTraceClosed D₂ D₁ G₁ rules M relevantTargets c₂ s


def TargetGuidedInferenceTerminates
  (D₂ D₁ : SemanticDomain)
  (G₁ : OperationalGraph D₁)
  (rules : SSet (TransDomainRule D₂ D₁))
  (M : SourceQuestionCostModel D₂)
  (c₂ : D₂.Sample)
  (Method : TargetGuidedInferenceMethod D₂ D₁ G₁ rules M c₂)
  (initialState : TargetGuidedInferenceState D₂ D₁ G₁) : Prop :=
  ∃ finalState : TargetGuidedInferenceState D₂ D₁ G₁,
    TargetInferenceContextValid D₂ D₁ G₁ finalState ∧
    TargetTraceClosed
      D₂
      D₁
      G₁
      rules
      M
      Method.relevantTargets
      c₂
      finalState

axiom target_guided_inference_terminates_by_finite_growth
  (D₂ D₁ : SemanticDomain)
  (G₁ : OperationalGraph D₁)
  (rules : SSet (TransDomainRule D₂ D₁))
  (M : SourceQuestionCostModel D₂)
  (c₂ : D₂.Sample)
  (Method : TargetGuidedInferenceMethod D₂ D₁ G₁ rules M c₂)
  (initialState : TargetGuidedInferenceState D₂ D₁ G₁) :
  TargetInferenceContextValid D₂ D₁ G₁ initialState →
  TargetGuidedInferenceTerminates
    D₂ D₁ G₁ rules M c₂ Method initialState


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

def AssociatedSamplesExistAfterTermination
  (D₂ D₁ : SemanticDomain)
  (G₁ : OperationalGraph D₁)
  (rules : SSet (TransDomainRule D₂ D₁))
  (M : SourceQuestionCostModel D₂)
  (samples₁ : SSet D₁.Sample)
  (c₂ : D₂.Sample)
  (Method : TargetGuidedInferenceMethod D₂ D₁ G₁ rules M c₂)
  (initialState : TargetGuidedInferenceState D₂ D₁ G₁) : Prop :=
  ∃ finalState : TargetGuidedInferenceState D₂ D₁ G₁,
    TargetTraceClosed
      D₂
      D₁
      G₁
      rules
      M
      Method.relevantTargets
      c₂
      finalState
    ∧
    AssociatedSamplesFromContext
      D₂
      D₁
      G₁
      samples₁
      finalState.ctx
      =
    AssociatedSamplesFromContext
      D₂
      D₁
      G₁
      samples₁
      finalState.ctx


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

end SemanticSpec
