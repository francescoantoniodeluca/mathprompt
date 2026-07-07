#MathPrompt

Using Lean to Create Effective Program Specifications for Prompting

I would like to share some considerations about AI prompting, starting from my own experience and challenges.

Having a clear idea of what a software application should do, and then writing that idea in a prompt, is often not enough. When the idea is complex, it can be very difficult to express it properly. Sometimes, you only realize that the idea was not actually clear after many prompt iterations.

Another risk is writing more than necessary and adding unnecessary constraints. Today, AI is practically one of the best programming assistants available, and we do not want to limit its potential. For this reason, it is important to provide only the information that is truly necessary.

Considering the problems described above, I would like to share, as an example, a new way to write a specification. In the file ./lean_spec.lean, I describe an abstract algorithm that:

* starts from samples in a semantic domain D1 and creates a differentiation graph;
* uses trans-domain relations to create inductive sets of question-answer pairs from domain D2 for each question-answer pair in the constructed graph in domain D1;
* optimizes selected performance indices.

The purpose of this algorithm is to correlate data from one domain to another through a questionnaire. For example, it could help students identify the most suitable course of study, or help users find the psychologist who best fits their needs.

An LLM API could be used either to choose the questions or to generate them directly, as well as to select the inductive set. Depending on the specific requirements of the application, these elements can be added either in Lean or in verbal form, according to the complexity of the system and its scalability needs.

Some examples of applications will soon be available on my GitHub account.

I will also add another file, ./lean_spec.lean.md, which contains the Lean specification enriched with Markdown comments to make it easier to understand.

You do not need to be a Lean-specialized mathematician. Understanding the language is sufficient. I created the specification using ChatGPT, and the possibility of proving theorems in Lean can also help validate ideas and check whether the specification is coherent.

I also leave some axioms to be proved. Proving them, or proving them false, could either strengthen the theory or fundamentally change it.
