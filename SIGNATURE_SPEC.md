# Signatures of V lemmas

The signature of a V lemma should be very consistent with the corresponding proof-taking counterpart or the `!` counterpart. However, there are some complications in the translation.

* Instead of `head`/`head!`, use `headV` (for example) in the statement.
* The `V` operations require a `Nonempty` instance for their return type (so that we can return a garbage value if something's wrong). Other than the proof-taking variants, they don't explicitly take any other kind of proof.
  * `head` takes a proof of `xs \ne []`, `headV` requires a `Nonempty` instance.
* The `V` lemma signatures should not have unnecessary requirements. If only a `Nonempty` instance is needed but the proof-taking counterpart requires a proof of, say, `i < xs.length`, then drop the proof. However, sometimes the proof is necessary to make the statement true. Flag cases in which you are unsure.
* You can test whether a statement even type-checks by using the lean-lsp-mcp to run Lean code.
* When the LHS is, say, `xs.headV`, and there's a `[Nonempty \a]` instance parameter, use `{_ : Nonempty \a}` instead: These lemmas are used by `rw` and `simp`, which will infer the instance by unification with `headV` in this case.
* `omega` does not work in all files, especially not in the more basif files.
