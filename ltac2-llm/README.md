Ltac2 bindings for OpenAI
================================

NOTE: this library is largely a proof-of-concept.

To use the library, require via the following command:

```coq
Require Import skylabs.ltac2.llm.llm.
```

You can now query the LLM using the following vernacular command.

```coq
Ltac2 Eval LLM.query_gpt "implement addition on natural numbers in Rocq (previously called Coq)".
```

Setup
-------
This plugin relies on an API key stored in `/builds/openaikey`.


Contributions
-----------------

Contributions are welcome.
