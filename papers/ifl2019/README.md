
☑ tick

☒ cross

[lala] <- comentarios nuestros



# observaciones, rev1

☒ The example uses fromJust. Not really great error handling. 

  [talvez sobre esto simplemente comentar que los errores se podrían manejar con
  más atributos]

☒ While attribute grammars aren't widely spread in practice, they are a
  well-studied concept, as the authors show in their related work section. Still,
  the authors assume that the reader is not very familiar (or familiar at all)
  with attribute grammars, and give a basic introduction to AG concepts in the
  first two sections of the paper (which is nice). A concrete example is given in
  the form of a simple expression language. Unfortunately, the example only
  briefly re-appears in Section 4.2, but it's largely ignored otherwise. I would
  encourage the authors to see if they can use the example more to help clarify
  the concepts from Section 3 and Section 4 and show how they would work in
  practice. That may make it easier to digest the vast number of types that are
  introduced in the paper.

☒ Part of the example is the introduction of the Expr data type. It has record
  selectors with the same names as the Labels that were introduced in the previous
  paragraph. This is a bit confusing. That would cause name clashes, no? How would
  you solve these clashes? Do I need both code snippets in my code? On those
  labels: the types of Label and @ aren't really introduced. What are all the
  extra snippets of information like "'Chi" and "'Left NtExpr"? I thought e.g.
  PAdd was already marked as non-terminal in its definition?

☒ The example uses functions like inhdefM, which later turn out to be monadic
  variants of their non-monadic counterparts. Exactly which roles monads play in
  the working of the AspectAG library is never really made clear, and the monadic
  nature of those parts of the library is also not really obvious from the types
  presented later in the paper. I would like to see an explanation of this.
  Similarly, the traceAspect function is mentioned in Section 2, but not explained
  until Section 4. The text in Section 2 would almost suggest traceAspect is
  explained just in the next paragraph, but the reader is left hanging instead,
  leaving to wonder what that function does in the examples in Section 2. I would
  like to either see traceAspect introduced later (so not included in the
  examples), or get a more detailed explanation sooner.

☒ Section 2.3 shows many examples of error messages. The quality of the error
  messages is impressive, and if I would indeed get such messages while using the
  library, I would be quite happy. Still, Section 2.3 feels like it's dragging on
  a bit too long, showing error message after error message, taking up a lot of
  space in the paper. It almost makes me wonder whether the other aspects of the
  work were not novel/interesting enough to demand space in the paper. It is also
  not entirely clear why these specific examples were chosen either and whether
  there's anything particularly challenging about producing those specific error
  messages.

☒ One big omission is a discussion on the performance (both run-time and
  compile-time) of the library. What is the performance like compared to the
  previous version of the library that didn't use all these new language features?
  How about compared to preprocessor approaches like UUAGC? What about compared to
  hand-writing similar programs? I would really like to see this being discussed.
  As impressive as the use of types is, if the library is too slow in practice,
  there's still a big problem to be solved (in which case I'd like to see this
  mentioned in the future work section).

☒ At the end of the paper, I am left wondering a bit what exactly has been
  achieved. Yes, the AspectAG library has successfully been implemented with new
  GHC language extensions, allegedly bringing more type safety than previous
  versions. It is a very nice example of advanced Haskell programming. Trade-offs
  between the previous version and the current version of AspectAG are discussed
  as well, but did you gain any big/fundamental (new?) insights from this work? An
  epiphany you would like to share with the rest of the world?

☒ In principle, I am enthusiastic about the work that the authors have done. (..)
  That said, while I think this paper has potential, I find that it still has many
  rough edges. My conclusion is a weak accept under the condition that the authors
  spend some time refining the paper.


☒ Section 4.3: I don't really see the added value of Table 2. What's wrong with
  just providing the type signatures? Even if you want to list the unicode
  characters, that can be done with regular type signatures as well. On unicode
  usage: the example in Figure 1 is inconsistent with regards to unicode usage.
  Some operators are unicode, other are ASCII operators. To introduce fewer new
  symbols to the reader and to make the correspondence between the paper and a
  real implementation easier to see, I think I would prefer not to introduce a
  unicode presentation for some of those operators.
☑ [la tabla voló, hay que ver si vale la  pena mantener extAspect y comAspect
  o definir derecho los operadores (en este momento teníamos tres formas de 
  hacer lo mismo)]

# Observaciones - rev2 (score 0)


☒ It is assumed that the reader is aware of the
  constructs of AspectAG and their limitations. This seriously limits the
  audience. 

☒ The paper starts with a simple but convincing example that shows how
  the system can be used for a very simple grammar that is extended in the next
  step. Although the reader gets a good impression of how the system is used, it
  does not serve as a firm starting point for the use of the system. There are too
  many operators, types and functions that remain undefined. The example shows
  some error messages of the new system, but it is unclear how they are better
  than the messages of the original system. The paper continues by sketching the
  implementation techniques used. The reader is supposed to be familiar with
  type-level programming in Haskell. Some clarification of the concepts used or
  references will improve the readability of the paper. According to the subtitle
  of the paper "Dealing with DSL errors in type-level programming", this is an
  important aspect of the paper. Again the reader gets an impression of the
  techniques used, but too much is omitted to fully understand the details. Next,
  it is sketched how these techniques are used in the new implementation of
  AspectAG. This section mainly introduces new tailor-made tools used in the
  implementation. I missed an example of what must be exactly done to achieve
  better error messages. The related work and conclusions are rather sketchy. It
  is claimed but not demonstrated that this system is safer than the previous
  implementation. Neither is it clear what we have to do for this and what nice
  things of the previous implementation we miss.

☒ In my view, the main problem of this paper is that it tries to do too much:
  describe all cleaver things done in the new implementation of AspectAG. As a
  result, all of these things are done sketchy. A clearer focus on (for instance)
  the improved type error messages in the DSL will improve the paper.



☒ Many things are sketchy. Form the introduction "that tackles some of its most
  important weaknesses.", "summary of some techniques we used", "some
  implementation details", "discuss some related work"

☒ especially the comparison with the original AspectAG system needs to be
  improved.


# Observaciones - rev3

☒ This paper was well written and the aims were clearly motivated. The examples
  were pretty understandable, notwithstanding the inclusion of a lot of Haskell
  code (more on that later). The use of the newer Haskell features does seem to
  result in a better AspectAG implementation.

☒ This sort of paper suffers from the large amount of Haskell code, much of which
  is not accessible to a non-expert. On the one hand, I understand the desire to
  show exactly how things are implemented. On the other hand, after 4-5 pages
  largely occupied by code listings, my eyes started to glaze over, so I don't
  think they were helping my understanding. This issue is exaggerated since much
  of the code uses advanced Haskell features for type-level programming. I suggest
  you include at least a short summary section which explains the syntax and
  meaning of these features to help readers who might be quite comfortable with
  functional programming in general, but not advanced Haskell in particular.

☒ The related work comparison is quite lacking. E.g., the first paragraph of the
  related work section lists some relevant AG implementations, but it's not clear
  why. Either they are relevant and a more detailed comparison with the new
  AspectAG should be given, or they're not really related. This is particularly
  the case for papers like [10] (and follow-ups to that work, which are not cited)
  which also embeds AGs in Haskell. The rest of the section is somewhat better but
  very brief.


☒ The introduction says that you tackle "some of its most important weaknesses".
  It would be better to be precise about exactly which ones are addressed and
  which ones aren't.
  
☒ While the examples in Section 2.3 of better error messages were good, it would
  have been useful to refer back to one or some of these when explaining the
  implementation later. It wasn't clear to me exactly how those messages were
  produced.

# Typos-rev1

☑ Just before paragraph 2.1, the text says "The final result of the evalutator
  is then obtained by performing..". Please point to a line number, because I
  was a bit lost there.


☑ Section 3.2 starts with "... are implemented over this general
  implementetation.". What general implementation is that? (Remember, you're in
  a new paragraph in a new section)

☒ Table 1: please tell me how to read this table
  [no está claro si a esta tabla está bueno pelarla o dejarla]

☑ Section 3.3: "When it is "called" a type error...". Be more specific. If it's
  not called, then what is it?

☑ Section 3.3: why is it signficant that TypeError can be used as a constraint?

☑ Section 3.3.1: please refer to each component by name. It's quite hard to
  follow otherwise.

☒ Section 3.3.1: would it make more sense to start the Require instance with the
  base case of an empty list?
  [efectivamente hacemos esto o motivamos en una linea por qué lo dejamos para 
  después?]


☒ Please don't use language like "clearly" (maybe it's not obvious), "complain"
  (be exact), "folklore" (what folklore?), "seems" (are you not sure?),
  "interesting" (I may disagree that it's interesting), "some sort of" (again,
  be more specific), "well-known trick" (I might not know it, and even if I did,
  I'm interested in proper solutions, not tricks), "some requirement" (be more
  specific), "nice" (that's very subjective)

☒ Template Haskell is mentioned on a few occasions in the paper, but no examples
  are shown at all. It is therefore not entirely clear what the user of the
  library would gain by using (or would lose by not using) the TH functionality.



# typos - rev 3

☑ p1, 1st col:
  "proven not being only useful" is awkward, perhaps "not only proven useful"?

☑ p1, 2nd col:
  "syntactic- and semantically", perhaps "syntactically and semantically"
  
☑ p2, 1st col: "the use we do of", perhaps "the use we make of"?

☑ p2, 2nd col "opertion"

☑ p9, 1st col: "que use"

