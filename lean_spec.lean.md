/-
# Specifica formale Lean/Markdown
## Dominio semantico dei questionari, grafo operativo G1 e induzione transdominio guidata dal bersaglio
Questa specifica formalizza un sistema composto da quattro moduli principali:
1. costruzione di un grafo operativo `G1` nel dominio bersaglio `D1`;
2. inferenza interna in `G1`, cioè calcolo della traccia operativa reale di un
   campione `c1 : D1.Sample`;
3. costruzione di oggetti di induzione transdominio, cioè insiemi minimi di
   domande-risposte del dominio sorgente `D2` capaci di indurre QA operative
   del grafo `G1`;
4. inferenza transdominio guidata da `G1`, che prende in input un campione
   `c2 : D2.Sample`, induce progressivamente una traccia dentro `G1` e restituisce
   l'insieme dei campioni `c1 : D1.Sample` compatibili con la traccia indotta.
La distinzione fondamentale è:
`G1`
è il grafo operativo bersaglio, costruito per differenziare i campioni del
dominio `D1`.
`D2`
non viene trasformato in un grafo autonomo di differenziazione.
Il dominio `D2` viene usato come dominio sorgente di evidenze.
Le regole transdominio non costruiscono un secondo grafo `G2`, ma costruiscono
oggetti di induzione verso le QA operative di `G1`.
Formula generale:
`c2 : D2.Sample`
`→ evidenze QA in D2`
`→ gruppi minimi di premesse D2`
`→ induzione di QA operative in G1`
`→ traccia indotta in G1`
`→ campioni c1 compatibili in D1`
La firma operativa reale di un campione `c1` in `G1` è:
`OperationalSignature(c1) = { x1 | OperationalQAReached(D1,G1,c1,x1) }`
La firma indotta da un campione `c2` dentro `G1` è:
`InducedTargetSignature(c2) = { x1 | TargetQAInducedBySource(c2,x1) }`
L'associazione completa è:
`InducedTargetSignature(c2) = OperationalSignature(c1)`
L'associazione parziale è:
`InducedTargetSignature(c2) ⊆ OperationalSignature(c1)`
Quando la traccia indotta è parziale, non si confrontano terminali isolati.
Si confrontano invece path operative complete di `G1` che estendono la traccia
indotta.
Punto centrale dell'ottimizzazione:
per ogni QA operativa bersaglio `x1` di `G1`, si costruiscono insiemi minimi
di QA sorgenti `P2 ⊆ QA D2` tali che:
`P2 ⟹ x1`
tramite regole transdominio.
Durante l'inferenza, il costo reale di un insieme di premesse non è la sua
cardinalità assoluta, ma il numero di nuove QA ancora da acquisire rispetto al
contesto antenato già acquisito:
`Cost(P2 | Context) = costo delle QA in P2 non già assunte nel contesto`
Se una QA sorgente è già stata usata per indurre una QA antenata in `G1`, allora
la sua risposta viene assunta come contestuale e non viene richiesta di nuovo.
Se invece la stessa domanda compare in un ramo non antenato, non viene
automaticamente considerata raggiunta: il riuso strutturale è ammesso, ma la
validità operativa resta legata al contesto del percorso.
Nota tecnica Lean:
Non usiamo `from` come nome di variabile o campo.
Usiamo:
`src` = nodo sorgente.
`dst` = nodo destinazione.
-/
namespace SemanticSpec
universe u v w
/-
## 0. Insiemi minimali
Un insieme di elementi di tipo `α` viene rappresentato come predicato:
`SSet α := α → Prop`
Quindi:
`x ∈ A`
significa:
`A x`.
Formula:
`A ⊆ α`
viene rappresentato come:
`A : α → Prop`
-/
abbrev SSet (α : Type u) := α → Prop
instance {α : Type u} : Membership α (SSet α) where
  mem A x := A x
/-
`Subset A B` significa:
`A ⊆ B`
Formula:
`Subset(A,B) := ∀ x, x ∈ A → x ∈ B`
-/
def Subset {α : Type u} (A B : SSet α) : Prop :=
  ∀ x : α, x ∈ A → x ∈ B
/-
`ProperSubset A B` significa:
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
## 1. Dominio semantico
Un dominio semantico è una quadrupla:
`D = (Sample, Question, Answer, holds)`
dove:
`Sample`
è il tipo dei campioni.
`Question`
è il tipo delle domande.
`Answer q`
è il tipo delle risposte ammissibili per la domanda `q`.
`holds q c r`
dice che il campione `c` soddisfa la risposta `r` alla domanda `q`.
Formula:
`holds(q,c,r)`
Si legge:
"per il campione `c`, la risposta `r` alla domanda `q` è vera".
Nota importante:
`Answer` dipende da `Question`.
Formula dipendente:
`Answer : Question → Type`
-/
structure SemanticDomain where
  Sample   : Type u
  Question : Type v
  Answer   : Question → Type w
  holds : (q : Question) → Sample → Answer q → Prop
/-
## 2. Coppia domanda-risposta semantica
Una QA semantica è una coppia dipendente:
`QA(D) = Σ q : Question, Answer(q)`
In Lean:
`x.q : D.Question`
`x.r : D.Answer x.q`
Questa QA non contiene ancora informazione grafica.
È solo:
`(q,r)`
-/
structure QA (D : SemanticDomain) where
  q : D.Question
  r : D.Answer q
/-
Proposizione completa:
`CompleteProp(D,c,x) := holds(x.q,c,x.r)`
-/
def CompleteProp
  (D : SemanticDomain)
  (c : D.Sample)
  (x : QA D) : Prop :=
  D.holds x.q c x.r
/-
Una proposizione completa è definita solo se sono presenti:
1. un campione;
2. una QA.
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
## 3. Profilo semantico del campione
Il profilo semantico del campione è l'insieme di tutte le QA semantiche vere
per quel campione.
Formula:
`Profile(c) = { x : QA D | holds(x.q,c,x.r) }`
Le risposte non sono necessariamente esclusive.
-/
def Profile
  (D : SemanticDomain)
  (c : D.Sample) : SSet (QA D) :=
  fun x => D.holds x.q c x.r
/-
## 4. Connettori e regole interne
Una regola interna permette di derivare una QA da un insieme di premesse.
Connettori supportati:
`and` = tutte le premesse devono essere vere.
`or` = almeno una premessa deve essere vera.
Formula generale:
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
Operatore di chiusura:
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
## 5. Espressioni semantiche
Le espressioni semantiche permettono di costruire formule composte.
Grammatica:
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
## 6. Proposizioni aperte, subordinate e osservazioni multidominio
Una proposizione aperta è un predicato:
`Sample → Prop`
Una proposizione chiusa è una proposizione:
`Prop`
Le subordinate sono operatori che trasformano predicati in altri predicati.
Le osservazioni multidominio mettono in relazione predicati appartenenti a
domini diversi.
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
## 7. Regole transdominio semantiche
Una regola transdominio permette di derivare una QA di `D₁` da un insieme di QA
di `D₂`.
Formula:
`premises ⊆ QA D₂`
`conclusion : QA D₁`
Schema:
`premises_D₂ ⟹ conclusion_D₁`
Le premesse sono multiple.
Quindi una conclusione del dominio `D₁` può dipendere da un gruppo di QA del
dominio `D₂`, non da una singola QA.
Questa sezione è semantica.
Più avanti useremo queste regole per costruire oggetti di induzione verso le QA
operative del grafo `G1`.
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
## 8. Copertura semantica delle domande
Una domanda copre un insieme di campioni se ogni campione ha almeno una risposta
vera a quella domanda.
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
## CAMBIO STRUTTURALE RISPETTO ALLA SPECIFICA PRECEDENTE
#######################################################################
Da qui in poi non si usano più:
`QTree`, `QBranch`, `QForest`.
Usiamo invece:
`OperationalGraph`.
Il grafo è orientato.
I nodi sono occorrenze operative di domande.
Gli archi sono etichettati da risposte.
Formula:
`src -- r --> dst`
Uno stesso campione può percorrere più archi contemporaneamente.
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
## 9. Percorso strutturale del grafo
`GraphPath D G a b`
significa che esiste un percorso orientato non vuoto da `a` a `b`.
Formula ricorsiva:
`GraphPath(a,b)`
vale se:
1. esiste un arco diretto `a --r--> b`;
2. oppure esiste `m` tale che `GraphPath(a,m) ∧ GraphPath(m,b)`.
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
## 10. Raggiungibilità operativa parallela
`OperationalReaches D G c n`
significa che il campione `c` raggiunge il nodo `n`.
Formula del passo:
`Reach(c,src) ∧ active(src,r) ∧ holds(questionOf(src),c,r) ∧ edge(src,r,dst) → Reach(c,dst)`
Poiché le risposte non sono esclusive, uno stesso campione può raggiungere più
nodi in parallelo.
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
## 11. Copertura operativa del grafo
Un grafo copre un campione se:
1. esiste almeno una radice;
2. ogni nodo raggiunto ha almeno una risposta attiva e vera.
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
## 12. QA operativa
Una QA semantica è:
`(q,r)`
Una QA operativa è:
`(src,r)`
dove:
`src : G.Node`
`r : D.Answer (G.questionOf src)`
Formula:
`OperationalQA(G) = Σ src : G.Node, Answer(questionOf src)`
Formula di raggiungibilità:
`OperationalQAReached(c,(src,r)) := Reach(c,src) ∧ active(src,r) ∧ holds(questionOf(src),c,r)`
Questa è la firma differenziante primaria del grafo.
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
## 13. Domanda-risposta terminale
Un terminale è una QA operativa:
`(src,r)`
tale che:
`active(src,r) ∧ ¬ ∃ dst, edge(src,r,dst)`
Formula:
`TerminalQAReached(c,t) := OperationalQAReached(c,t) ∧ ¬ AnswerContinues(t.src,t.r)`
Quindi:
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
## 14. Firma terminale
Formula:
`TerminalSignature(c) = { t | TerminalQAReached(c,t) }`
La firma terminale è una vista della chiusura dei percorsi.
La firma primaria resta quella operativa.
I terminali restano importanti, ma non sono più il criterio isolato di
associazione transdominio.
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
## 15. Differenziazione completa
La differenziazione principale usa firme operative:
`CompleteOperationalDifferentiationGraph(G,samples) := ∀ c₁ c₂ ∈ samples, c₁ ≠ c₂ → OperationalSignature(c₁) ≠ OperationalSignature(c₂)`
Formula estesa:
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
## 16. Domanda separante
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
## 17. Coppia non ancora distinta
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
## 18. Domande già presenti, riusabili e nuove
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
## 19. Politica di priorità nella scelta della domanda
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
## 20. Inseribilità operativa della domanda separante
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
## 21. Espandibilità progressiva globale
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
## 22. Esistenza di un grafo differenziante completo
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
## 23. Stato di costruzione del grafo
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
## 24. Builder progressivo senza fuel
Il builder non usa un fuel esterno.
La terminazione deriva dalla misura interna:
`badPairCount`.
Formula:
`step?(s) = some t → badPairCount(t) < badPairCount(s)`
Formula di arresto corretto:
`step?(s) = none → badPairCount(s) = 0`
Formula di completezza:
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
## 25. Esecuzione del builder senza fuel
Formula:
`run(s) = s`
se:
`step?(s) = none`
altrimenti:
`run(s) = run(t)`
se:
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
## 26. Correttezza astratta del builder senza fuel
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
## 27. Oggetti di induzione target-guided da D2 verso G1
Da qui in poi non costruiamo più un grafo `G2` autonomo.
Il dominio `D2` viene usato come sorgente di evidenze.
Il grafo `G1` resta il grafo bersaglio.
Per ogni QA operativa bersaglio:
`x1 : OperationalQA D1 G1`
costruiamo oggetti di induzione contenenti gruppi minimi di QA sorgenti:
`P2 ⊆ QA D2`
capaci di indurre `x1`.
Formula:
`PremiseSetSupportsTarget(P2,x1)`
significa:
esiste una regola transdominio `rule` tale che:
1. `rule.conclusion = OperationalQAAsSemanticQA(x1)`;
2. tutte le premesse della regola sono contenute in `P2`.
Formula:
`∃ rule, rule ∈ rules ∧ rule.conclusion = Sem(x1) ∧ rule.premises ⊆ P2`
Un gruppo `P2` è minimo se non esiste un sottoinsieme proprio `P2' ⊂ P2`
che supporta ancora lo stesso target.
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
Un oggetto di induzione associa una QA operativa bersaglio `target` a un insieme
minimo di QA sorgenti `premises₂`.
Formula:
`TargetInductionObject(target,premises₂)`
con:
`MinimalPremiseSetForTarget(premises₂,target)`
Questi oggetti vengono costruiti prima dell'inferenza su un campione specifico.
Sono indipendenti dal campione `c2`.
Durante l'inferenza, il sistema sceglierà tra questi oggetti quelli compatibili
con il contesto corrente e con il campione sorgente.
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
Il sistema di oggetti di induzione è l'insieme degli oggetti disponibili.
Formula:
`objects ⊆ TargetInductionObject(D2,D1,G1,rules)`
Questa struttura rappresenta il risultato del metodo:
`BuildInductionObjects(G1, rules)`
cioè:
dato il grafo bersaglio `G1` e le regole transdominio, costruisci tutti gli
oggetti di induzione minimali verso le QA operative di `G1`.
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
## 28. Contesto di induzione e costo contestuale
Durante l'inferenza transdominio, non bisogna richiedere di nuovo le QA sorgenti
già usate per indurre QA operative antenate in `G1`.
Per questo introduciamo un contesto.
Il contesto contiene:
`assumedSource`
insieme delle QA sorgenti di `D2` già acquisite e assunte come vere nel percorso
indotto corrente.
`inducedTarget`
insieme delle QA operative di `G1` già indotte.
Formula:
`Context = (assumedSource, inducedTarget)`
Una QA sorgente già nel contesto ha costo zero.
Formula del costo ideale:
`Cost(P2 | Context) = costo(P2 \ Context.assumedSource)`
Non formalizziamo qui la cardinalità concreta di un insieme predicativo.
Introduciamo quindi un modello astratto di costo.
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
Una domanda sorgente è già stata usata nel contesto se esiste una QA già assunta
con la stessa domanda.
Formula:
`SourceQuestionAlreadyUsed(known,q) := ∃ x, x ∈ known ∧ x.q = q`
Se una domanda è già stata usata nel contesto antenato, allora non vogliamo
richiedere una nuova risposta diversa alla stessa domanda.
Perciò un set di premesse è ammesso nel contesto se ogni sua QA che ha una
domanda già usata è già essa stessa nel contesto.
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
Un set di premesse è ottimale nel contesto se:
1. supporta il target;
2. è ammesso nel contesto;
3. non esiste un altro set ammesso che supporta lo stesso target e ha costo
   contestuale minore.
Formula:
`ContextuallyOptimalPremiseSet(P2,target,ctx)`
significa:
`PremiseSetSupportsTarget(P2,target)`
`∧ ContextAllowsPremiseSet(ctx,P2)`
`∧ ¬ ∃ P2', Supports(P2',target) ∧ Allowed(ctx,P2') ∧ Cost(P2'|ctx) < Cost(P2|ctx)`
Questo formalizza l'idea:
scegliere il gruppo di premesse che richiede il minor numero di nuove domande,
riusando il più possibile le QA già acquisite lungo gli antenati della traccia
indotta.
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
## 29. Raggiungibilità indotta nel grafo bersaglio G1
Una QA operativa bersaglio `x1` non deve essere considerata inducibile solo
perché esiste un gruppo di premesse sorgenti che la supporta.
Deve anche essere raggiungibile nel grafo `G1` tramite una catena di QA operative
già indotte.
Quindi l'inferenza transdominio deve rispettare la struttura operativa del
grafo bersaglio.
Definiamo prima la raggiungibilità indotta dei nodi di `G1`.
Un nodo è raggiungibile induttivamente se:
1. è una radice;
2. oppure esiste una QA operativa già indotta che porta a quel nodo tramite un
   arco di `G1`.
Formula:
`InducedNodeReachable(root)`
se:
`root ∈ G1.roots`
Formula del passo:
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
Una QA operativa bersaglio è inducibile nel contesto solo se:
1. il suo nodo sorgente è raggiungibile induttivamente;
2. la sua risposta è attiva nel grafo `G1`.
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
## 30. Soddisfazione delle premesse da parte di un campione sorgente
Un gruppo di premesse `P2` è soddisfatto da un campione `c2` se tutte le QA
sorgenti contenute in `P2` sono vere per `c2`.
Formula:
`PremiseSetSatisfiedBySample(c2,P2) := ∀ x2 ∈ P2, holds(x2.q,c2,x2.r)`
Poiché in questa nuova architettura non costruiamo più un grafo autonomo `G2`,
la verifica avviene direttamente nel dominio sorgente `D2`.
-/
def PremiseSetSatisfiedBySample
  (D₂ : SemanticDomain)
  (c₂ : D₂.Sample)
  (premises₂ : SSet (QA D₂)) : Prop :=
  ∀ x₂ : QA D₂,
    x₂ ∈ premises₂ →
    D₂.holds x₂.q c₂ x₂.r
/-
Una QA operativa bersaglio viene indotta da un campione sorgente nel contesto se:
1. la QA bersaglio è raggiungibile nel grafo `G1` rispetto alla traccia già
   indotta;
2. esiste un set di premesse contestualmente ottimale;
3. il campione sorgente soddisfa quel set di premesse.
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
## 31. Aggiornamento del contesto dopo un'induzione
Quando una QA operativa bersaglio `target` viene indotta tramite un set di
premesse `premises₂`, il contesto viene aggiornato così:
1. le premesse sorgenti vengono aggiunte alle QA sorgenti assunte;
2. la QA bersaglio viene aggiunta alle QA operative indotte in `G1`.
Formula:
`assumedSource' = assumedSource ∪ premises₂`
`inducedTarget' = inducedTarget ∪ { target }`
Questo è il meccanismo che rende contestuali le QA sorgenti usate per indurre
antenati della traccia in `G1`.
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
## 32. Passo di inferenza transdominio guidato da G1
Un passo valido di inferenza transdominio sceglie:
1. una QA operativa bersaglio `target` raggiungibile nel contesto;
2. un set di premesse sorgenti `premises₂` contestualmente ottimale;
3. un campione sorgente `c2` che soddisfa quelle premesse.
Poi aggiorna il contesto aggiungendo `premises₂` e `target`.
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
## 33. Stato e metodo di inferenza transdominio
Lo stato dell'inferenza transdominio contiene il contesto corrente.
Formula:
`TargetGuidedInferenceState = { ctx }`
Il metodo di inferenza è astratto.
Contiene:
`badTargetCount`
numero di QA operative bersaglio ancora potenzialmente inducibili e non risolte.
`step?`
passo opzionale.
`step_decreases`
ogni passo diminuisce `badTargetCount`.
`step_preserves_validity`
ogni passo conserva la validità del contesto.
`stops_when_closed`
se il metodo si ferma, la traccia indotta è chiusa rispetto alle QA raggiungibili
e inducibili nel contesto corrente.
Questa struttura permette di specificare il metodo senza fissare ancora un
algoritmo computazionale concreto.
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
## 34. Esecuzione del metodo transdominio senza fuel
Come per il builder di `G1`, non usiamo fuel.
La terminazione deriva dalla misura:
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
## 35. Campioni correlati nel dominio D1
Dopo aver indotto una traccia dentro `G1`, vogliamo restituire un insieme di
campioni del dominio `D1` compatibili con quella traccia.
Un campione `c1` è compatibile con un contesto indotto se ogni QA operativa
indotta è realmente raggiunta da `c1` in `G1`.
Formula:
`CompatibleWithInducedTrace(c1,ctx) := ∀ x1 ∈ ctx.inducedTarget, OperationalQAReached(D1,G1,c1,x1)`
Il risultato dell'inferenza transdominio è:
`AssociatedSamples(c2) = { c1 ∈ samples1 | CompatibleWithInducedTrace(c1, finalContext) }`
Questa forma restituisce un set, non necessariamente un singolo campione.
Se la traccia indotta è completa e `G1` differenzia completamente i campioni,
il set può ridursi a un solo campione.
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
## 36. Path operative e completamento parziale
Nel caso in cui la traccia indotta da `c2` sia parziale, non usiamo i terminali
raggiungibili come scorciatoia.
Usiamo tutte le path operative complete che estendono la traccia indotta.
Una path operativa è rappresentata astrattamente come un insieme di QA operative
più proprietà strutturali:
1. parte da una radice;
2. è localmente coerente con gli archi;
3. arriva a una chiusura terminale.
Formula:
`CompleteOperationalPath(p) := starts_at_root ∧ locally_connected ∧ complete_to_terminal`
Formula di estensione:
`PathExtendsInducedTrace(ctx,p) := ∀ x1 ∈ ctx.inducedTarget, x1 ∈ p`
Formula di compatibilità:
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
## 37. Ordine esterno delle QA operative
La firma operativa è un insieme:
`OperationalSignature(c) = { x | OperationalQAReached(c,x) }`
Per alcuni usi operativi, ad esempio confronto vettoriale, ranking o matrici di
dissimilarità, è utile trasformare la firma in un vettore ordinato.
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
## 38. Ordine esterno dei terminali
I terminali restano disponibili come chiusura delle path operative.
La firma terminale può essere ordinata, ma non sostituisce la firma operativa
nelle associazioni transdominio.
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
## 39. Sintesi finale
La specifica produce quattro metodi concettuali.
### 1. Metodo di costruzione di G1
Input:
`samples1 : SSet D1.Sample`
`domainQuestions1 : SSet D1.Question`
Output:
`G1 : OperationalGraph D1`
Obiettivo:
`CompleteDifferentiationGraph D1 G1 samples1`
cioè:
`∀ c1 c1' ∈ samples1, c1 ≠ c1' → OperationalSignature(c1) ≠ OperationalSignature(c1')`
### 2. Metodo di inferenza in G1
Input:
`c1 : D1.Sample`
Output:
`OperationalSignature(c1)`
Formula:
`OperationalSignature(c1) = { x1 | OperationalQAReached D1 G1 c1 x1 }`
### 3. Metodo di costruzione degli oggetti di induzione D2 → G1
Input:
`G1`
`rules : SSet (TransDomainRule D2 D1)`
Output:
`TargetInductionObjectSystem D2 D1 G1`
Per ogni QA operativa bersaglio `x1`, costruisce gruppi minimi di QA sorgenti
`P2` tali che:
`P2 ⟹ x1`
Formula:
`MinimalPremiseSetForTarget(P2,x1)`
cioè:
`PremiseSetSupportsTarget(P2,x1)`
`∧ ¬ ∃ P2' ⊂ P2, PremiseSetSupportsTarget(P2',x1)`
### 4. Metodo di inferenza transdominio guidato da G1
Input:
`c2 : D2.Sample`
Procedura:
1. parte dal contesto iniziale;
2. considera solo QA operative raggiungibili in `G1`;
3. per ogni QA bersaglio raggiungibile, seleziona i set di premesse sorgenti
   contestualmente ottimali;
4. riusa le QA sorgenti già acquisite lungo gli antenati;
5. non cumula domande inutili provenienti da rami non attivi;
6. induce progressivamente una traccia in `G1`;
7. restituisce i campioni di `D1` compatibili con la traccia indotta.
Output:
`AssociatedSamplesFromInference(c2) ⊆ D1.Sample`
Formula:
`AssociatedSamples(c2) = { c1 ∈ samples1 | ∀ x1 ∈ inducedTarget(c2), OperationalQAReached(D1,G1,c1,x1) }`
### Punto essenziale
Non costruiamo un grafo `G2` autonomo per associare i campioni.
Un grafo costruito per differenziare i campioni di `D2` potrebbe usare domande
ottime per distinguere `D2`, ma inutili per indurre il grafo `G1`.
Perciò il dominio `D2` viene interrogato in modo target-guided:
`G1` guida la scelta delle domande sorgenti da porre in `D2`.
Il criterio non è:
"differenziare D2"
ma:
"indurre nel modo più economico e contestualmente coerente le prossime QA
operative raggiungibili in G1".
Formula del costo contestuale:
`Cost(P2 | Context) = costo delle QA di P2 non già assunte nel contesto antenato`
Formula dell'induzione target-guided:
`TargetQAInducedBySource(c2,ctx,x1) :=`
`TargetOperationalQAInducibleInContext(ctx,x1)`
`∧ ∃ P2, ContextuallyOptimalPremiseSetForTarget(P2,x1,ctx)`
`∧ PremiseSetSatisfiedBySample(c2,P2)`
I terminali restano importanti, ma solo come chiusura delle path operative, non
come criterio isolato di associazione.
-/
end SemanticSpec
