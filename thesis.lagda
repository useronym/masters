\documentclass[
  digital, %% This option enables the default options for the
           %% digital version of a document. Replace with `printed`
           %% to enable the default options for the printed version
           %% of a document.
  twoside, %% This option enables double-sided typesetting. Use at
           %% least 120 g/m² paper to prevent show-through. Replace
           %% with `oneside` to use one-sided typesetting; use only
           %% if you don’t have access to a double-sided printer,
           %% or if one-sided typesetting is a formal requirement
           %% at your faculty.
  notable,   %% This option causes the coloring of tables. Replace
           %% with `notable` to restore plain LaTeX tables.
  nolof, nolot    %% This option prints the List of Figures. Replace with
           %% `nolof` to hide the List of Figures.
  %% More options are listed in the user guide at
  %% <http://mirrors.ctan.org/macros/latex/contrib/fithesis/guide/mu/fi.pdf>.
]{fithesis3}

%%\usepackage{fontspec}
%%\usepackage{yfonts}
%%\usepackage{unicode-math}
%%\usepackage{xunicode}
\usepackage[main=english]{babel}
\usepackage{csquotes}

\thesissetup{
    date          = \the\year/\the\month/\the\day,
    university    = mu,
    faculty       = fi,
    type          = mgr,
    author        = {Bc. Adam Krupička},
    gender        = m,
    advisor       = {RNDr. Martin Jonáš},
    title         = {Coinductive Formalization of SECD Machine in Agda},
    TeXtitle      = {Coinductive Formalization of SECD Machine in Agda},
    keywords      = {SECD Agda formalization coinduction},
    TeXkeywords   = {SECD Agda formalization coinduction},
    abstract      = {This is the abstract of my thesis, which can

                     span multiple paragraphs.},
    thanks        = {I would like to thank my friends and family for supporting
      me throughout this work.

      I would also like to thank many users of the Freenode IRC network for
      helpful discussions regarding various topics connected to matters contained in
      this thesis. This list includes, but is not limited to, Ahmad Salim Al-Sibahi,
      Guillaume Allais, Miëtek Bak, Paolo G. Giarrusso, and Andrea Vezzosi.},
    bib = bibliography.bib
}

%% \usepackage{makeidx}      %% The `makeidx` package contains
%%\makeindex                %% helper commands for index typesetting.
%% These additional packages are used within the document:
%%\usepackage{amsmath}  %% Mathematics
%%\usepackage{mathtools}  %% Mathematics
%%\usepackage{amsthm}
%%\usepackage{amsfonts}
\usepackage[backend=biber]{biblatex}
\usepackage{amssymb}
\usepackage{booktabs}
\usepackage{url}      %% Hyperlinks

%%\theoremstyle{definition}
%%\newtheorem{theorem}{Theorem}
%%\newtheorem{definition}{Definition}
%%\newtheorem{notation}{Notation}


\usepackage{agda}
\usepackage{newunicodechar}
\newunicodechar{λ}{\ensuremath{\mathnormal\lambda}}
\newunicodechar{ƛ}{\ensuremath{\mathnormal\lambda}}
\newunicodechar{ι}{\ensuremath{\mathnormal\iota}}
\newunicodechar{τ}{\ensuremath{\mathnormal\tau}}
\newunicodechar{ℕ}{\ensuremath{\mathnormal\mathbb{N}}}
\newunicodechar{ℤ}{\ensuremath{\mathnormal\mathbb{Z}}}
\newunicodechar{↝}{\ensuremath{\mathnormal\leadsto}}
\newunicodechar{ᵈ}{\ensuremath{^d}}
\newunicodechar{ᶜ}{\ensuremath{^c}}
\newunicodechar{★}{\ensuremath{\mathnormal\star}}
\newunicodechar{＋}{\ensuremath{\mathnormal+}}
\newcommand{\A}{\AgdaArgument}
\newcommand{\D}{\AgdaDatatype}
\newcommand{\I}{\AgdaInductiveConstructor}
\newcommand{\F}{\AgdaFunction}

\makeatletter
\renewcommand{\@chapapp}{}% Not necessary...
\newenvironment{chapquote}[2][2em]
  {\setlength{\@tempdima}{#1}%
   \def\chapquote@author{#2}%
   \parshape 1 \@tempdima \dimexpr\textwidth-2\@tempdima\relax%
   \itshape}
  {\par\medskip\normalfont\hfill---\ \chapquote@author\hspace*{\@tempdima}\par\bigskip}
\makeatother

\begin{document}
\chapter{Introduction}
\begin{chapquote}{George Orwell, \textit{Homage to Catalonia}}
  There are occasions when it pays better to fight and be beaten than not to
  fight at all.
\end{chapquote}
Ever since the dawn of functional programming languages, there was a need for an
efficient and practical execution model which would serve as the compilation
target for the high-level functional languages. The first of these was the
SECD machine, introduced by Landin in 1964.

Statically typed languages have many advantages over those lacking in this area.
They give higher assurances to the correctness of the programs therein written,
and they allow for stronger optimizations by the compiler. Perhaps most of all,
they give the programmer a solid framework in which to reason about the code
being written.

Even in the community of statically typed languages, however, typed low-level
assembly languages have not received much consideration. All the current
mainstream assembly languages do not depend on a type system, instead trusting
the compiler from a high-level language to generate valid programs. This is
something we wish to address in this work, by introducing a type system for SECD
instructions.

Still another 

\chapter{Logic, Constructivism, Type Theory}
\begin{chapquote}{Richard Feynman}
  What I cannot create, I do not understand.
\end{chapquote}
This chapter presents a quick overview of several rather complex areas. However,
the information here presented should be sufficient for understanding the rest
of this thesis.

Previous knowledge of mathematical logic and computability theory would be
helpful in order for the reader to be able to appreciate all of the below
content, however it is not assumed.

\section{Intuitionistic logic}
Intuitionistic logic~\parencite{brouwer1907foundations, brouwer1908unreliability}
is a logic that, unlike most of current mathematics, only allows for
constructive arguments. In practice, the main difference is that proof by
contradiction is not allowed: in order to show that something is the case, it is
not enough to show that the opposite is not the case. In theory, this is
achieved by disallowing the law of the excluded middle (LEM), which states that
for any proposition $P$, $P$ either does or does not hold:
\[
  ∀P\quad.P ∨ ¬P
\]
Certain other well-known classical tautologies, such as double negation
elimination,
\[
  ∀P\quad.¬¬P → P
\]
are equivalent to this principle. It is also the case that the axiom of
choice, as formulated in set theory, implies the law of the excluded middle, a
result by Diaconescu~\parencite{diaconescu1975axiom}.

Intuitionistic logic began as an attempt by Brouwer to develop a base for all
mathematics that would more closely follow the intuitions of the human mind.
Futhermore, the Stanford Encyclopedia of Philosophy's entry on
Intuitionism~\parencite{sep-logic-intuitionistic} states,

\begin{displayquote}
  (…) to Brouwer the general LEM was equivalent to the a priori assumption that
  every mathematical problem has a solution — an assumption he rejected,
  anticipating Gödel’s incompleteness theorem by a quarter of a century.
\end{displayquote}

In practice, there are considerations with regards to constructive approaches
other than a purely philosophical one. Under the standard
Brouwer-Heyting-Kolmogorov interpretation of the intuitionistic
logic~\parencite{troelstra2011history}, working in this setting means that every
proposition proven amounts to a recipe, an algorithm, on how to transform the
assumptions, or inputs, into the result, or output. For this reason,
intuitionistic logic should be of high interest especially to computer scientists.

As an instructive example, consider the normalization of proofs in some theory.
It has been discovered that if one can establish soundness and completeness of
this theory with regard to some suitable semantics, this naturally gives rise to
a normalizer for this theory~\parencite{coquand2002formalised}. In a
constructive setting, the proof of an implication consists of a function, and so
proofs of soundness and completeness give us a way to convert between the
syntactic and semantic world. Reflecting a proof into the semantical structure
(soundness), and reifying from the semantical structure back into syntax
(completeness), we obtain a normalized version of the original proof. This
approach to normalization is commonly referred to as normalization by evaluation
and has been used as early as 1975 by Martin-Löf in order to establish
decidability of type\-checking for his intuitionistic theory of (dependent)
types theory~\parencite{martin1975intuitionistic}, albeit not under the moniker
of normalization by evaluation~\parencite{abel2013normalization}.

\section{Type Theory}
Type theory was first introduced by Russell and Whitehead in 1910 in their
transformational work Principia Mathematica~\parencite{whitehead1912principia} as
a response to Russell's discovery of inconsistency of the naïve set
theory~\parencite{frege1982philosophical} in 1901. In type theory, every
expression has an associated type, and there are rules for the formation of
values and types dependent on these. Compare this with set theory, where
propositions such as $2 ∈ 3$ can be formulated\footnote{The above being, in
  fact, true, as per the standard construction of natural numbers in set theory
  due to von Neumann~\parencite{von1923introduction}.}.

The next breakthrough in type theory was the discovery of the Simply Typed λ
Calculus~\parencite{church1940formulation} by Church in 1940. This, too, came as a way to
avoid paradoxes present in the Untyped λ Calculus~\parencite{church1932set},
which was found to be inconsistent by Kleene and
Rosser~\parencite{kleene1935inconsistency}. The Untyped λ calculus was introduced
as a universal model of computation, a point at which it succeeded, as it is
equivalent in strength to Turing machines~\parencite{turing1937computability}.
\subsection{Curry-Howard Correspondence}
It was later observed by Howard that the Simply Typed λ Calculus (STLC) could be
viewed as a language for construction of proofs in Natural
Deduction~\parencite{howard1980formulae} (ND), an intuitionistic proof calculus
introduced originally by Gentzen in 1934~\parencite{gentzen1935untersuchungen} as
an attempt at a more natural language for expressing proofs. This correspondence simply
states that \textit{propositions} of ND are isomorphic with \textit{types} in
STLC, \textit{proofs} of ND with \textit{terms} (or programs) of STLC, and
\textit{normalization} of proofs in ND with \textit{conversion into normal form}
of terms of STLC.

This leads to the realization that we can prove theorems by writing computer
programs, and that subsequently we can have these proofs verified by a
type checker. However, in order to be able to express more interesting
properties, we need a type system stronger than STLC.
\subsection{Dependent Types}
In order to extend the expressivity to non-trivial propositions, dependent types
were proposed first by de Bruijn~\parencite{de1967description} in 1967 in his
project Automath, aiming at creating a language for encoding computer-verified
mathematics. Later, in 1972, Martin-Löf formulated his intuitionistic type
theory~\parencite{martin1975intuitionistic}, in which dependent types play a
central role. More recently, starting in the mid 2000's, Voevodsky introduced
Univalent Foundations~\parencite{voevodsky2011univalent}, which aim to give
practical foundations for modern mathematics in a way that allows for
computer-verified proofs.

Dependent types are types which can depend on values. They correspond with
quantifiers from predicate logic, thus allowing one to naturally express more
involved propositions.

The type that corresponds to universal quantification $∀$ is the type of
dependent functions $Π(a : A).B(a)$, where the type of $B$ can depend on the
value $a$. A proof of such a proposition consists of a function which for any
value $a$ produces the proof of $B(a)$. For example, consider the statement
\[
  Π(n : \mathbb{N}).even(n) ∨ odd(n).
\]
A proof of this proposition would consist of a decision procedure which for
any natural number $n$ determines whether $n$ is even or odd and returns a proof
of this fact.

Corresponding with existential quantification $∃$ is the type of dependent
products $Σ(a:A).B(a)$. A proof would consist of a pair of some value $a$ of
type $A$ and a proof of $B(a)$. As an example, consider the statement that there
exists a prime number,
\[
  Σ(n:\mathbb{N}).prime(n).
\]
One possibility of a proof would be the number $2$ and a proof that $2$ is
prime, which would hopefully be self-evident.

\subsection{Inhabitance}
An important concept is that of inhabitance of some type. An inhabited type is a
type that is non-empty, i.e., there are some values of this type. This is
analogous to the proposition that this type corresponds to a provable
proposition. Thus the values of some type are sometimes called witnesses to
(the provability of) the corresponding proposition.

\chapter{Agda}
\begin{chapquote}{From the topic of the official Agda IRC channel}
  Agda: is it a dependently-typed programming language? Is it a proof-assistant
  based on intuitionistic type theory?

  \verb| ¯\(°_0)/¯| Dunno, lol.
\end{chapquote}
Agda~\parencite{norell2007towards} is a functional programming language with
first-class support for dependent types. As per the Curry-Howard correspondence,
well-typed programs in Agda can also be understood as proofs of inhabitance of
their corresponding types; types being understood as propositions.

This section is meant as a crash-course in Agda syntax, not semantics. In other
words, those not familiar with dependently typed programming languages and/or
proof assistants would do better to follow one of the books published on this
topic. See~\parencite{friedman2018little} for an introduction to dependent types
as a whole, or~\parencite{stump2016verified} for an in-depth introduction to
dependendly typed programming and theorem proving in Agda.
\section{Overview}
Due to the presence of dependent types, functions defined in Agda must be by
default\footnote{This restriction can be lifted, however it is at the user's own
risk.} provably terminating. Failure to do so would result in type-checking
becoming undecidable. However, this does not cause the loss of
Turing-completeness; indeed in section~\ref{coinduction} we present how
possibly non-terminating computations can still be expressed, with some help
from the type system.

Agda has strong support for mixfix operators\footnote{Operators that can have
  multiple name parts and are infix, prefix, postfix, or
  closed~\parencite{mixfix}.} and Unicode identifiers. This often allows for
developing a notation close to what one has come to expect in mathematics. For
example, the following is valid Agda syntax:

\begin{code}[hide]
kek : Set₁
kek = Set

module HiddenSyntax where
  infix 10 _,_
  infix 10 _⇒_
  postulate
    α β Γ : Set
    _⊢_ _⇒_ _,_ : Set → Set → Set
\end{code}
\noindent\begin{minipage}[]{\textwidth}\begin{code}
    MP : ∀ {Γ α β} → α , Γ ⊢ β
                    ---------
                   → Γ ⊢ α ⇒ β
\end{code}\end{minipage}

As an aside, there is also some support for proof automation in
Agda~\parencite{auto}, however from the author's experience, the usability of this
tool is limited to simple cases. In contrast with tools such as
Coq~\parencite{barras1997coq}, Isabelle~\parencite{nipkow2002isabelle}, or
ACL2~\parencite{kaufmann1996acl2}, Agda suffers from a lower degree of
automation: there are no built-in tactics, though their implementation is
possible through reflection~\parencite{agda-manual}.
\subsection{Trivial Types}
A type that is trivially inhabited by a single value is often refered to as
\textit{Top} or \textit{Unit}. In Agda,

\noindent\begin{minipage}[]{\textwidth}\begin{code}
data ⊤ : Set where
  ⋅ : ⊤
\end{code}\end{minipage}
declares the new data type \AgdaDatatype{⊤} which is itself of type
\AgdaPrimitiveType{Set}\footnote{For the reader familiar with the Haskell type
  system, the Agda type $Set$ is akin to the Haskell kind \textit{Star}. Agda has
  a stratified hierarchy of universes, where $Set$ itself is of the type $Set_1$, and
  so on.}. The second line declares a value constructor for this type, here
called simply \AgdaInductiveConstructor{⋅}, which constructs a value of type
\AgdaDatatype{⊤}\footnote{Again for the Haskell-able, note how the syntax here
  resembles that of Haskell with the extension \texttt{GADTs}.}.

The dual of \AgdaDatatype{⊤} is the trivially uninhabited type, often called
\textit{Bottom} or \textit{Empty}. Complete definition in Agda follows.

\noindent\begin{minipage}[]{\textwidth}\begin{code}
data ⊥ : Set where
\end{code}\end{minipage}
Note that there are no constructors declared for this type. Due to the inner
workings of Agda, this guarantees us an inhabited type.

The empty type also allows us to define the negation of a proposition,

\noindent\begin{minipage}[]{\textwidth}\begin{code}
¬_ : Set → Set
¬ P = P → ⊥
\end{code}\end{minipage}
Here we also see for the first time the notation for mixfix operators. Note the
underscore \texttt{\_} in the name declaration of this function: it symbolizes
where the argument is to be expected.
\subsection{Booleans}
A step-up from the trivially inhabited type \AgdaDatatype{⊤}, the type of
booleans is made up of two distinct values.

\noindent\begin{minipage}[]{\textwidth}\begin{code}
data Bool : Set where
  tt ff : Bool
\end{code}\end{minipage}
Since both constructors have the same type signature, we take advantage of a
feature in Agda that allows us to declare such constructors on one line,
together with the shared type.

Now we can declare a function that will perform negation of Boolean values,

\noindent\begin{minipage}[]{\textwidth}\begin{code}
not : Bool → Bool
not tt = ff
not ff = tt
\end{code}\end{minipage}
Here we utilize pattern matching to split on the argument and transform each
boolean value into the opposite.

Another function we can define is the conjunction of two boolean values, using a
similar approach,

\noindent\begin{minipage}[]{\textwidth}\begin{code}
_∧_ : Bool → Bool → Bool
tt ∧ b = b
ff ∧ _ = ff
\end{code}\end{minipage}

\subsection{Products}
To define the product type, it is customary to use a record. This will give us
implicit projection functions from the type.

\noindent\begin{minipage}[]{\textwidth}\begin{code}
record _×_ (A : Set) (B : Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B
\end{code}\end{minipage}
\begin{code}[hide]
open _×_
infixr 4 _,_

module HiddenProducts where
\end{code}
Here we declare a new record type, parametrized by two other types,
\AgdaArgument{A} and \AgdaArgument{B}. These are the types of the values stored
in the pair, which we construct with the operator
\AgdaInductiveConstructor{\_,\_}.

As an example, we can create a pair of two boolean values,

\noindent\begin{minipage}[]{\textwidth}\begin{code}
  _ : Bool × Bool
  _ = tt , ff
\end{code}\end{minipage}
Here we see another use of the underscore: we can use it as a placeholder in the
stead of an identifier. This is useful in situations where we wish to give some
example we won't be using in the future.

To showcase the use of projections, we can define an uncurried version of
\F{\_∧\_} as a function from products of two boolean values,

\noindent\begin{minipage}[]{\textwidth}\begin{code}
  conj : Bool × Bool → Bool
  conj r = proj₁ r ∧ proj₂ r
\end{code}\end{minipage}
In practice, however, it is often less cumbersome to instead employ pattern
matching together with the constructor syntax in order to de-structure a record,

\noindent\begin{minipage}[]{\textwidth}\begin{code}
  conj' : Bool × Bool → Bool
  conj' (a , b) = a ∧ b
\end{code}\end{minipage}
\subsection{Natural numbers}
To see a more interesting example of a type, let us consider the type of natural numbers. These can be implemented using Peano encoding, as shown below.

\noindent\begin{minipage}[]{\textwidth}\begin{code}[hide]
module Hidden where
\end{code}\end{minipage}

\noindent\begin{minipage}[]{\textwidth}\begin{code}
  data ℕ : Set where
    zero  : ℕ
    suc   : ℕ → ℕ
\end{code}\end{minipage}
Here we have a nullary constructor for the value zero, and then a unary value
constructor, which corresponds to the successor function. As an example,
consider the number 3, which would be encoded
as~\AgdaInductiveConstructor{suc(suc(suc\ zero))}.

As an example of a function on the naturals, let us define the addition function.

\noindent\begin{minipage}[]{\textwidth}\begin{code}
  _+_ : ℕ → ℕ → ℕ
  zero + b   = b
  suc a + b  = suc (a + b)
\end{code}\end{minipage}
We proceed by induction on the left argument: if that number is zero, the result
is simply the right argument. If the left argument is a successor of some number
\AgdaArgument{a}, we inductively perform addition of \AgdaArgument{a} to
\AgdaArgument{b}, and then apply the successor function to the result.
\section{Propositional Equality}
In this section, we take a short look at one of the main features of
intuitionistic type theory, namely, the identity type. This type allows us to
state the proposition that two values of some data type are \textit{equal}. The
meaning of \textit{equal} here is that both of the values are convertible to the
same value through reductions. This is the concept of propositional equality.
Compare this with definitional equality, which only allows us to express when
two values have the same syntactic representation. For example, definitionally it
holds that $2=2$, however $1+1=2$ only holds propositionally, because a
reduction is required on the left-hand side.

We can define propositional equality in Agda as follows.

\noindent\begin{minipage}[]{\textwidth}\begin{code}
  data _≡_ {A : Set} : A → A → Set where
    refl : {x : A} → x ≡ x
\end{code}\end{minipage}

\noindent\begin{minipage}[]{\textwidth}\begin{code}[hide]
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
\end{code}\end{minipage}
The curly braces denote an implicit argument, i.e., an argument that is to be
inferred by the type-checker. The equality type is polymorphic in this
underlying type, \AgdaArgument{A}.

The only way we have to construct values of this type is by the constructor
\AgdaInductiveConstructor{refl}, which says that each value is propositionally
equal to itself. Propositional equality is thus an internalization of
definitional equality as a proposition: we say that two values are
propositionally equal if there is a chain of reductions which lead to
establishing definitional equality between the two values.

Unlike in axiomatic treatments of equivalence, symmetry and transitivity of
\AgdaDatatype{\_≡\_} are theorems in Agda:

\noindent\begin{minipage}[]{\textwidth}\begin{code}
sym : {A : Set} {a b : A} → a ≡ b → b ≡ a
sym refl = refl

trans : {A : Set} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
trans refl refl = refl
\end{code}\end{minipage}
By pattern-matching on the proofs of equality we force Agda to unify the
variables \A{a}, \A{b}, and \A{c}. This is possible because there are no other
conditions on the variables here. In more complex situations, Agda may fail to perform
unification: in such a case we are required to explicitly de-structure the
involved terms until unification can succeed. After all the variables are
unified, we are \textit{de facto} constructing a proof of \A{a} \D{≡} \A{a}, which
we do with the \I{refl} constructor.

Finally, let us see the promised proof of $1+1=2$,

\noindent\begin{minipage}[]{\textwidth}\begin{code}[hide]
module Hidden2 where
  open import Data.Nat using (zero; suc; _+_)
\end{code}\end{minipage}

\noindent\begin{minipage}[]{\textwidth}\begin{code}
  1+1≡2 : 1 + 1 ≡ 2
  1+1≡2 = refl
\end{code}\end{minipage}
The proof is trivial, as $1+1$ reduces directly to two. A more interesting proof
would be that of associativity of addition,

\noindent\begin{minipage}[]{\textwidth}\begin{code}
  +-assoc : ∀ {a b c} → a + (b + c) ≡ (a + b) + c
  +-assoc {zero}   = refl
  +-assoc {suc a}  = let a+[b+c]≡[a+b]+c = +-assoc {a}
                      in ≡-cong suc a+[b+c]≡[a+b]+c
    where ≡-cong : {A B : Set} {a b : A}
                   → (f : A → B) → a ≡ b → f a ≡ f b
          ≡-cong f refl = refl
\end{code}\end{minipage}
Here we proceed by induction on the variable \A{a}, which is given as an
implicit argument: hence in the definition we surround the argument by curly
braces in order to be able to access it. We have no need for the arguments \A{b}
and \A{c}, and as they are implicit as well, we simply do not write them in the
left-hand side of the definition.

In the base case when $a = 0$ we are asked to prove that
\[
  0+(b+c)≡(0+b)+c.
\]
By the definition of addition, the left side simplifies to $b+c$. The right side
simplifies to $b+c$ as well, therefore we are permitted to close the case by
\I{refl}.

In the general case we are to prove
\[
  suc\ a+(b+c)≡(suc\ a+b)+c.
\]
First we observe how this simplifies according to the definition of addition:
the left side simplifies to $suc\ (a+(b+c))$, whereas the right side first to
$suc\ (a+b)+c$ and then to $suc\ ((a+b)+c)$. Therefore we are to prove that
\[
  suc\ (a+(b+c))≡suc\ ((a+b)+c).
\]
To this end we obtain the inductive assumption,
\[
  a+(b+c)≡(a+b)+c.
\]
Now all we need is to insert the \I{suc} into this assumption, which we do by a
call to the lemma \F{≡-cong}, which proves that propositional equality is a
congruence with respect to unary functions, such as \I{suc}.

The reader may also notice the use of the quantifier $∀$ in the type of
\F{+-assoc}. This is an instruction to Agda to infer the types of the variables
in the type signature, in this case inferring \A{a}, \A{b}, and \A{c} to be of
the type \D{ℕ}. It does \textit{not} have the meaning of universal
quantification, instead all function types are universally quantified
by default, similarly to e.g. Haskell.
\section{Decidable Equality}
A strengthening of the concept of propositional equality is that of
\textit{decidable equality}. This is a form of equality that, unlike
Propositional equality, can be decided programatically. We define this equality
as a restriction of propositional equality to those comparisons that are
decidable. Firstly, we need the definition of a decidable relation.

\noindent\begin{minipage}[]{\textwidth}\begin{code}
data Dec (R : Set) : Set where
  yes  : R → Dec R
  no   : ¬ R → Dec R
\end{code}\end{minipage}
This data type allows us to embed either a \I{yes} or a \I{no} answer as to
whether \A{R} is inhabited. For example, we can state that the type \D{⊤} is
inhabited by producing the witness \I{⋅},

\noindent\begin{minipage}[]{\textwidth}\begin{code}[hide]
module HiddenDec where
\end{code}\end{minipage}

\noindent\begin{minipage}[]{\textwidth}\begin{code}
  _ : Dec ⊤
  _ = yes ⋅
\end{code}\end{minipage}
and that the type \D{⊥} is not,

\noindent\begin{minipage}[]{\textwidth}\begin{code}
  _ : Dec ⊥
  _ = no λ()
\end{code}\end{minipage}
by discharging the absurd pattern by $λ()$. The constructor \I{no} takes a value
of type \F{¬}\D{⊥}, which stands for \D{⊥} → \D{⊥}. Since the left-hand side is
absurd, Agda allows us to conclude anything, even \D{⊥}, by this syntax.

Now we can define what it means for a type to possess decidable equality,

\noindent\begin{minipage}[]{\textwidth}\begin{code}
Decidable : (A : Set) → Set
Decidable A = ∀ (a b : A) → Dec (a ≡ b)
\end{code}\end{minipage}
Here we specify that for any two values of that type we must be able to produce
an answer whether they are equal or not.

As an example, let us define decidable equality for the type of Naturals. We
also use this as an excuse to introduce the keyword \AgdaKeyword{with} which can
be used to make a case-split on some expression,

\noindent\begin{minipage}[]{\textwidth}\begin{code}[hide]
open import Data.Nat using (ℕ; zero; suc)
\end{code}\end{minipage}

\noindent\begin{minipage}[]{\textwidth}\begin{code}
_≟ℕ_ : Decidable ℕ
zero ≟ℕ zero     = yes refl
(suc _) ≟ℕ zero  = no λ()
zero ≟ℕ (suc _)  = no λ()
(suc m) ≟ℕ (suc n) with m ≟ℕ n
… | yes refl  = yes refl
… | no ¬m≡n   = no λ m≡n → ¬m≡n (suc-injective m≡n)
  where suc-injective : ∀ {m n} → suc m ≡ suc n → m ≡ n
        suc-injective refl = refl
\end{code}\end{minipage}
Given a proof of equality of two values of a decidable type, we can forget all
about the proof and simply ask whether the two values are equal or not,

\noindent\begin{minipage}[]{\textwidth}\begin{code}
⌊_⌋ : {A : Set} {a b : A} → Dec (a ≡ b) → Bool
⌊ yes p ⌋  = tt
⌊ no ¬p ⌋  = ff
\end{code}\end{minipage}

\noindent\begin{minipage}[]{\textwidth}\begin{code}[hide]
open import Data.Integer using (ℤ)
open import Data.Integer.Properties renaming (_≟_ to _≟ℤ'_)
open import Data.List using (List; []; [_]; _∷_; null; all; length)
import Relation.Nullary as N
import Data.Empty as E

_≟B_ : Decidable Bool
tt  ≟B tt  = yes refl
ff ≟B ff   = yes refl
tt  ≟B ff  = no λ()
ff ≟B tt   = no λ()

_≟ℤ_ : Decidable ℤ
a ≟ℤ b with a ≟ℤ' b
… | N.yes refl  = yes refl
… | N.no ¬p     = no λ x → ⊥⊥ (¬p x)
  where ⊥⊥ : E.⊥ → ⊥
        ⊥⊥ ()
\end{code}\end{minipage}

\section{Coinduction}
\label{coinduction}
Total languages, such as Agda, are sometimes wrongfully accused of lacking
Turing-completeness. In reality, there are ways to model possibly
non-terminating programs -- given some time limit for their execution. One such
way is to introduce a monad which captures the concept of a recursive
call~\parencite{mcbride2015turing}.

In this section we introduce the concept of coinduction on the example of
streams and then proceed to define a monad which will be used later on in
chapter 5 to give semantics to the execution of SECD machine code.

For a more in-depth overview of coinduction in Agda and especially the
aforementioned monad, please refer to~\parencite{coinduction}.

The concepts presented can be made specific in category theory, where given a
functor $F$ we can speak of $F-$coalgebras. Coinduction, then, is a way of
proving properties of such systems. Morally, the distinction between induction
and coinduction is that induction proceeds by breaking down a problem into some
base case, whereas coinduction starts with a base case and iteratively extends
to subsequent steps.

Well-known examples of $F-$coalgebras include streams and transition systems.
The moral distinction here is that while elements of algebraic structures, or
data, are constructed, elements of coalgebraic structures, or codata, are
observed.

For a more in-depth introduction to coalgebra, please see
~\parencite{jacobs_2016}.

\subsection{Streams}
Streams are infinite lists. For example, consider the succession of all natural
numbers: it is clearly infinite. In some functional languages, such as Haskell,
this can be expressed as a lazily constructed list. Agda, however, being total,
does not allow for such a construction directly: an infinite data structure is
clearly not inductively constructible. It is, however, observable: as with a
regular list, we can peek at its head \AgdaField{hd}, and we can drop the head
and look at the tail \AgdaField{tl} of the stream.

To capture this in Agda, we define a record with these projections and mark it
as \AgdaKeyword{coinductive},

\noindent\begin{minipage}[]{\textwidth}\begin{code}[hide]
open import Size
open import Data.Maybe using (Maybe; just; nothing)
\end{code}\end{minipage}

\noindent\begin{minipage}[]{\textwidth}\begin{code}
record Stream (A : Set) : Set where
  coinductive
  field
    hd  : A
    tl  : Stream A
\end{code}\end{minipage}

\noindent\begin{minipage}[]{\textwidth}\begin{code}[hide]
open Stream
module HiddenX where
  open import Data.Nat using (⌊_/2⌋; _+_; _*_)
  open import Data.Sum using (inj₁; inj₂) renaming (_⊎_ to _∨_)
  open import Data.Product using (Σ) renaming (_,_ to _⹁_)
  even? : ℕ → Bool
  even? zero           = tt
  even? (suc zero)     = ff
  even? (suc (suc n))  = even? n

  mapˢ : ∀ {A B} → (A → B) → Stream A → Stream B
  hd (mapˢ f as) = f (hd as)
  tl (mapˢ f as) = mapˢ f (tl as)

  atˢ : ∀ {A} → ℕ → Stream A → A
  atˢ zero xs = hd xs
  atˢ (suc n) xs = atˢ n (tl xs)
\end{code}\end{minipage}
As an example, consider the aforementioned stream of natural numbers, starting
from some \A{n},

\noindent\begin{minipage}[]{\textwidth}\begin{code}
  nats : ℕ → Stream ℕ
  hd (nats n)  = n
  tl (nats n)  = nats (n + 1)
\end{code}\end{minipage}
Here we employ a feature of Agda called copatterns. Recall that we are
constructing a record: the above syntax says how the individual fields are
to be realized. Note also that the argument to \F{nats} is allowed to be
structurally enlarged before the recursive call, something that would be
forbidden in an inductive definition.

Given such a stream, we may wish to observe it by peeking forward a finite
number of times, thus producing a \D{List},

\noindent\begin{minipage}[]{\textwidth}\begin{code}
  takeˢ : ∀ {A} → ℕ → Stream A → List A
  takeˢ zero xs     = []
  takeˢ (suc n) xs  = hd xs ∷ takeˢ n (tl xs)
\end{code}\end{minipage}
Now we can convince ourselves that the above implementation of \F{nats} is,
indeed, correct,

\noindent\begin{minipage}[]{\textwidth}\begin{code}
  _ : takeˢ 7 (nats 0) ≡ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ []
  _ = refl
\end{code}\end{minipage}
For a more interesting example of a stream, consider the Hailstone sequence,
with a slight modification to the single step function, given below:

\noindent\begin{minipage}[]{\textwidth}\begin{code}
  step : ℕ → ℕ
  step 1 = 0
  step n with even? n
  … | tt  = ⌊ n /2⌋
  … | ff  = 3 * n + 1
\end{code}\end{minipage}
The sequence itself, then, can be given by the following definition,

\noindent\begin{minipage}[]{\textwidth}\begin{code}
  collatz : ℕ → Stream ℕ
  hd (collatz n)  = n
  tl (collatz n)  = collatz (step n)
\end{code}\end{minipage}
For example, observe the sequence starting from the number $12$,

\noindent\begin{minipage}[]{\textwidth}\begin{code}
  _ : takeˢ 11 (collatz 12)
      ≡ 12 ∷ 6 ∷ 3 ∷ 10 ∷ 5 ∷ 16 ∷ 8 ∷ 4 ∷ 2 ∷ 1 ∷ 0 ∷ []
  _ = refl
\end{code}\end{minipage}
As an aside, using a dependent product, we can express the predicate that a
stream will eventually reach some given value,

\noindent\begin{minipage}[]{\textwidth}\begin{code}
  Reaches : ∀ {A} → Stream A → A → Set
  Reaches xs a = Σ ℕ (λ n → atˢ n xs ≡ a)
\end{code}\end{minipage}
Here the binary function \F{atˢ} is used, which returns the $n$-th element of
the stream \A{xs}.

Hence, the Collatz conjecture can be stated as follows:

\noindent\begin{minipage}[]{\textwidth}\begin{code}[hide]
  postulate
\end{code}\end{minipage}

\noindent\begin{minipage}[]{\textwidth}\begin{code}
    conjecture : ∀ n → Reaches (collatz n) 0
\end{code}\end{minipage}
\subsection{The Delay Monad}
The Delay monad captures the concept of unbounded recursive calls. There are two
ways to construct a value of this type: \I{now}, which says that execution has
terminated and the result is available, and \I{later}, which means the result is
delayed by some indirection and \textit{might} be available later. In Agda, we
define this as a mutual definition of an inductive and coinductive data-type as
follows,
\label{delay_monad}

\noindent\begin{minipage}[]{\textwidth}\begin{code}
mutual
  data Delay (A : Set) (i : Size) : Set where
    now    : A → Delay A i
    later  : ∞Delay A i → Delay A i

  record ∞Delay (A : Set) (i : Size) : Set where
    coinductive
    field
      force : {j : Size< i} → Delay A j
\end{code}\end{minipage}
Here we use the built-in type \D{Size} which serves as a measure on the size
of the delay. Note that the field \AgdaField{force} requires this to strictly
decrease. This measure aids the Agda type-checker in verifying that a definition
is \textit{productive}, that is, some progress is made in each iteration
of \AgdaField{force}. The type \D{Size<} \A{i} is the type of all sizes 
strictly smaller than \A{i}. 

For any data-type we may define an infinitely delayed value,

\noindent\begin{minipage}[]{\textwidth}\begin{code}[hide]
open ∞Delay public
\end{code}\end{minipage}

\noindent\begin{minipage}[]{\textwidth}\begin{code}
never : ∀ {i A} → Delay A i
never {i} = later λ where .force {j} → never {j}
\end{code}\end{minipage}
This can be used to signal an error in execution has occurred. The implicit size
argument has been written explicitly for the reader's sake.

Here we also see for the first time the anonymous syntax for constructing
records by copatterns. The above is synonymous with

\noindent\begin{minipage}[]{\textwidth}\begin{code}
mutual
  never' : ∀ {i A} → Delay A i
  never' = later ∞never'

  ∞never' : ∀ {i A} → ∞Delay A i
  force ∞never' = never'
\end{code}\end{minipage}
In other words, anonymous records allow us to succinctly construct codata by use
of copatterns, without the need of writing unwieldy mutual blocks.

Given a delayed value, we can attempt to retrieve it in a given finite number of
steps,

\noindent\begin{minipage}[]{\textwidth}\begin{code}
runFor : ∀ {A} → ℕ → Delay A ∞ → Maybe A
runFor zero (now x)       = just x
runFor zero (later _)     = nothing
runFor (suc _) (now x)    = just x
runFor (suc n) (later x)  = runFor n (force x)
\end{code}\end{minipage}
This idiom is useful for executing a computation that periodically offers
its environment a chance to interrupt the computation, or proceed further on.

\D{Delay} is also a monad, with the unit operator\footnote{In Haskell
  terminology, \textit{return}.} being \I{now} and the bind
operator given below,

\noindent\begin{minipage}[]{\textwidth}\begin{code}
_>>=_ : ∀ {A B i} → Delay A i → (A → Delay B i) → Delay B i
now x >>= f    = f x
later x >>= f  = later λ where .force → (force x) >>= f
\end{code}\end{minipage}
This allows us to chain delayed computations where one depends on the result of
another.

\noindent\begin{minipage}[]{\textwidth}\begin{code}[hide]
open import Data.Integer using (+_; _+_; _-_; _*_)
\end{code}\end{minipage}

\chapter{Formalizing Type Systems}
\begin{chapquote}{Philip Wadler}
  λ calculus isn't invented, it's discovered.
\end{chapquote}
In what follows, we take a look at how we can use Agda to formalize
deductive systems and/or typed calculi. We concern ourselves with the
simplest example there is, the Simply Typed λ Calculus.

Deductive systems are formal languages which allow the statement and proof of
propositions in a manner that makes the conclusions indisputable, as long as one
can agree on assumptions used in the proof and laws of reason encompassed by the
system.

For a more in-depth treatment of the topic of formalizing programming languages
and programming language theory in Agda, please refer
to~\parencite{wadler2018programming}.

λ calculi are arguably the simplest model of computation. They almost invariably
contain the basic concepts, which are variables, function formation, and
function application. They come in many forms and can be adapted to model any
specific requirements we may have, e.g. resource-conscious linear
calculi~\parencite{girard1987linear}, concurrency-oriented process
calculi~\parencite{boudol1989towards}, or calculi modeling quantum
computing~\parencite{van2004lambda}.

For a brief history of λ calculi, please refer to chapter 2.

\section{De Bruijn Indices}
Firstly, we shall need some machinery to make our lives easier. We could use
string literals as variable names in our system, however this would lead to
certain difficulties further on, such as increased complexity of the
formalization due to the need to handle string comparisons and such. Instead, we
shall use the concept commonly referred to as De Bruijn
indices~\parencite{de1972lambda}. In this formalism variable identifiers consist
of natural numbers, where each number $n$ refers to the variable bound by the
binder $n$ positions above the current scope in the syntax tree. Some
examples of this naming scheme are shown in Figure~\ref{debruijn}.
\begin{figure}[h]
  \centering
  \begin{tabular}{l|l}
    \multicolumn{1}{c}{String syntax} & \multicolumn{1}{c}{De Bruijn syntax} \\
    \midrule
    \verb|λx.x| & \verb|λ 0| \\
    \verb|λx.λy.x| & \verb|λλ 1| \\
    \verb|λx.λy.λz.x z (y z)| & \verb|λλλ 2 0 (1 0)| \\
  \end{tabular}
  \caption{Examples of λ terms using the standard naming scheme on the left and
    using De Bruijn indices on the right.}
  \label{debruijn}
\end{figure}
The immediately apparent advantage of using De Bruijn indices is that
α-equivalence\footnote{The problem of whether two λ terms represent the same
  function.} of λ terms becomes trivially decidable by way of purely syntactic
equality. Other advantages include easier formalization.
\subsection{Implementation}
To implement De Bruijn indices in Agda, we express what it means for a variable
to be present in a context. Context is a collection of assumptions we are
equipped with in a given situation. We shall assume that a context is a list of
assumptions, as this is how contexts will be defined in the next subsection. We
will express list membership as a new data type,

\noindent\begin{minipage}[]{\textwidth}\begin{code}
data _∈_ {A : Set} : A → List A → Set where
  here   : ∀ {x xs} → x ∈ (x ∷ xs)
  there  : ∀ {x a xs} → x ∈ xs → x ∈ (a ∷ xs)
\end{code}\end{minipage}

\noindent\begin{minipage}[]{\textwidth}\begin{code}[hide]
infix 10 _∈_
\end{code}\end{minipage}
The first constructor says that an element is present in a list if that element
is the head of the list. The second constructor says that if we already know
that our element \A{x} is in a list, we can extend the list with some other
element \A{a} and \A{x} will still be present in the new list.

As a few examples of elements of \D{\_∈\_} consider the following shorthands
that we use in examples further on.

\noindent\begin{minipage}[]{\textwidth}\begin{code}
𝟎 : ∀ {A} {x : A} {xs : List A} → x ∈ (x ∷ xs)
𝟎 = here

𝟏 : ∀ {A} {x y : A} {xs : List A} → x ∈ (y ∷ x ∷ xs)
𝟏 = there here

𝟐 : ∀ {A} {x y z : A} {xs : List A} → x ∈ (z ∷ y ∷ x ∷ xs)
𝟐 = there (there here)
\end{code}\end{minipage}
Now we can also define a function which, given a proof that an element is in a
list, returns the aforementioned element,

\noindent\begin{minipage}[]{\textwidth}\begin{code}
lookup : ∀ {A x xs} → x ∈ xs → A
lookup {x = x} here  = x
lookup (there w)     = lookup w
\end{code}\end{minipage}
Now if during the construction of some λ term we find ourselves in a situation
in which we wish to introduce a variable pointing to some assumption from the
context, we can give a value such as \F{𝟏} to mean the second assumption in the
context, encoded as a list. Additionally, this \F{𝟏} will also serve as a
witness to the fact that this or that specific assumption is, indeed, in the
context.
\section{Example: Simply Typed λ Calculus}
In this subsection, in preparation of the main matter of this thesis,
we introduce the way typed deductive systems can be formalized in Agda. As
promised, we approach the formalization the Simply Typed λ Calculus.
\subsection{Syntax}
\label{lambda_syntax}
First, we define the types for expressions in our system.

\noindent\begin{minipage}[]{\textwidth}\begin{code}[hide]
module Hidden3 where
\end{code}\end{minipage}

\noindent\begin{minipage}[]{\textwidth}\begin{code}
  data ★ : Set where
    τ    : ★
    _⇒_  : ★ → ★ → ★
\end{code}\end{minipage}

\noindent\begin{minipage}[]{\textwidth}\begin{code}[hide]
  infixr 20 _⇒_
\end{code}\end{minipage}
Here we defined an atomic type \I{τ} and a binary type constructor for
function types. The meaning of \I{τ} is currently completely arbitrary: it will
become concrete when giving semantics.

We proceed by defining context as a list of assumptions, where every assumption
is encoded directly by its type.

\noindent\begin{minipage}[]{\textwidth}\begin{code}
  Context : Set
  Context = List ★
\end{code}\end{minipage}
Now we are finally able to define the deductive rules that make up the calculus,
using De Bruijn indices as explained above.

\noindent\begin{minipage}[]{\textwidth}\begin{code}
  data _⊢_ : Context → ★ → Set where
    var  : ∀ {Γ α}   → α ∈ Γ → Γ ⊢ α
    ƛ_   : ∀ {Γ α β} → α ∷ Γ ⊢ β → Γ ⊢ α ⇒ β
    _$_  : ∀ {Γ α β} → Γ ⊢ α ⇒ β → Γ ⊢ α → Γ ⊢ β
\end{code}\end{minipage}

\noindent\begin{minipage}[]{\textwidth}\begin{code}[hide]
  infix 4 _⊢_
  infixr 5 ƛ_
  infixl 10 _$_
\end{code}\end{minipage}
The constructors above correspond exactly to the typing rules of the calculus.
In the first rule we employed the data type \D{\_∈\_} implenting De Bruijn
indices: if we can give a witness to the membership of assumption \A{α} in the
context, we can derive it. In the second rule, which captures the concept of
λ-abstraction, we say that if from a context extended with \A{α} we can derive
\A{β}, then we can form the function \A{α}~\I{⇒}~\A{β}. The last rule is that of
function application: if from some context we can derive a function
\A{α}~\I{⇒}~\A{β}, and we can derive also \A{α}, we may use the function to
obtain a \A{β}.

We can see some examples now, below we hive λ terms corresponding the S and K
combinators. In standard notation, S is defined as \texttt{λx.λy.x} and K as
\texttt{λx.λy.λz.x z (y z)}.

\noindent\begin{minipage}[]{\textwidth}\begin{code}
  K : ∀ {Γ α β} → Γ ⊢ α ⇒ β ⇒ α
  K = ƛ ƛ (var 𝟏)

  S : ∀ {Γ α β γ} → Γ ⊢ (α ⇒ β ⇒ γ) ⇒ (α ⇒ β) ⇒ α ⇒ γ
  S = ƛ ƛ ƛ var 𝟐 $ var 𝟎 $ (var 𝟏 $ var 𝟎)
\end{code}\end{minipage}
Note how we use Agda polymorphism to construct a polymorphic term of our
calculus — there is no polymorphism in the calculus itself.

The advantage of this presentation is that only well-typed syntax is
representable. Thus, whenever we work with a term of our calculus, it is
guaranteed to be well-typed, which often simplifies things. We see an
example of this in the next subsection.
\subsection{Semantics by Embedding into Agda}
\label{lambda_semantics}
Now that we have defined the syntax, the next step is to give it semantics. We
do this in a straightforward manned by way of embedding our calculus into Agda.

First, we define the semantics of types, by assigning Agda types to types in our calculus.

\noindent\begin{minipage}[]{\textwidth}\begin{code}
  ⟦_⟧★ : ★ → Set
  ⟦ τ ⟧★      = ℕ
  ⟦ α ⇒ β ⟧★  = ⟦ α ⟧★ → ⟦ β ⟧★
\end{code}\end{minipage}
Here we choose to realize our atomic type as the type of Natural numbers. These
are chosen for being a nontrivial type. The function type is realized as an Agda
function type.

Next, we give semantics to contexts.

\noindent\begin{minipage}[]{\textwidth}\begin{code}
  ⟦_⟧C : Context → Set
  ⟦ [] ⟧C      = ⊤
  ⟦ x ∷ xs ⟧C  = ⟦ x ⟧★ × ⟦ xs ⟧C
\end{code}\end{minipage}
The empty context can be realized trivially by the unit type. A non-empty
context is realized as the product of the realization of the first element
and, inductively, a realization of the rest of the context.

Now we are ready to give semantics to terms. In order to be able to proceed by
induction with regard to the structure of the term, we must operate on open terms.

\noindent\begin{minipage}[]{\textwidth}\begin{code}
  ⟦_⟧_ : ∀ {Γ α} → Γ ⊢ α → ⟦ Γ ⟧C → ⟦ α ⟧★
\end{code}\end{minipage}
The second argument is a realization of the context in the term, which we shall
need for variables,

\noindent\begin{minipage}[]{\textwidth}\begin{code}
  ⟦ var here ⟧ (x , _)        = x
  ⟦ var (there x) ⟧ (_ , xs)  = ⟦ var x ⟧ xs
\end{code}\end{minipage}
Here we case-split on the variable, in case it is zero we take the first element
of the context, otherwise we recurse into the context until we hit zero. Note
that the shape of the context Γ is guaranteed here to never be empty, because the
argument to \I{var} is a proof of membership for Γ. Thus, Agda realizes that Γ
can never be empty and we need not bother ourselves with a case-split for the
empty context; indeed, we would be hard-pressed to give it an implementation. In
other words, we are allowed to pattern-match on the semantics of \A{Γ}, which is
guaranteed to be a product of realizations of the types therein contained. This
is an advantage of the typed syntax with De Bruijn indices, as we can never
encounter an index which would be out of bounds with respect to the context.

\noindent\begin{minipage}[]{\textwidth}\begin{code}
  ⟦ ƛ x ⟧ γ                   = λ α → ⟦ x ⟧ (α , γ)
\end{code}\end{minipage}
The case for lambda abstraction constructs an Agda anonymous function that takes
as the argument a value of the corresponding type and compute the semantics for
the lambda's body, after extending the context with the argument.

\noindent\begin{minipage}[]{\textwidth}\begin{code}
  ⟦ f $ x ⟧ γ                 = (⟦ f ⟧ γ) (⟦ x ⟧ γ)
\end{code}\end{minipage}
Finally, to give semantics to function application, we simply perform Agda
function application on the subexpressions, after having computed their
semantics in the current context.

Thanks to propositional equality, we can embed tests directly into Agda code and
see whether the terms we defined above receive the expected semantics.

\noindent\begin{minipage}[]{\textwidth}\begin{code}
  Kℕ : ℕ → ℕ → ℕ
  Kℕ x _ = x

  _ : ⟦ K ⟧ ⋅ ≡ Kℕ
  _ = refl

  Sℕ : (ℕ → ℕ → ℕ) → (ℕ → ℕ) → ℕ → ℕ
  Sℕ x y z = x z (y z)

  _ : ⟦ S ⟧ ⋅ ≡ Sℕ
  _ = refl
\end{code}\end{minipage}
Since this thesis can only be rendered if all the Agda code has successfully
type-checked, the fact that the reader is currently reading this paragraph means
the semantics functions as expected!
\chapter{SECD Machine}
\begin{chapquote}{Christopher Strachey, discussion following~\parencite{landin1966next}, 1966}
  Any language which by mere chance of the way it is written makes it extremely
  difficult to write compositions of functions and very easy to write sequences of
  commands will, of course, in an obvious psychological way, hinder people from
  using descriptive rather than imperative features. In the long run, I think the
  effect will delay our understanding of basic similarities, which underlie
  different sorts of programs and different ways of solving problems.
\end{chapquote}
\section{Introduction}
The original \textbf{S}tack, \textbf{E}nvironment, \textbf{C}ontrol,
\textbf{D}ump machine is a stack-based, call-by-value abstract execution machine
that was first outlined by Landin in~\parencite{landin1964mechanical}. It was
regarded as an underlying model of execution for a family of languages,
specifically, languages based on the abstract formalism of λ calculus.

Other machines modeling execution of functional languages have since been
proposed, some derived from SECD, others not. Notable examples are the Krivine
machine~\parencite{krivine2007call}, which implements a call-by-name semantics,
and the ZAM (Zinc abstract machine), which serves as a backend for the OCaml
strict functional programming language~\parencite{leroy1990zinc}.

For an overview of different kinds of SECD machines, including a modern
presentation of the standard call-by-value, and also call-by-name and
call-by-need versions of the machine, see~\parencite{danvy2004rational}.

There have also been hardware implementations of this formalism,
e.g.~\parencite{graham1989secd, secdchip}.

This chapter is meant as an intuitive overview of the formalism. We present
the machine with the standard call-by-value semantics, following the original
presentation by Landin~\parencite{landin1964mechanical}. At the
end of this chapter we also present an extension of the machine with a
\textit{function} dump, which, to the best knowledge of the author, is a novel
concept. This extension is crucial for the formalization of SECD with typed code
in the next chapter.
\section{Definition}
The machine operates by executing instructions stored as a linked list, referred
to as the control. Each instruction has the ability to change the machine state.
The machine is notable for its first-class treatment of functions. As a natural
target of compilation from the Untyped λ Calculus, the machine is a
Turing-complete formalism.

Faithful to its name, the machine is made up of four components:
\begin{itemize}
  \item Stack -- stores values and functions operated on. Atomic operations,
    such as integer addition, are performed here;
  \item Environment -- stores immutable assignments, such as function arguments and
    values bound by the \textit{let} construct;
  \item Control -- stores a list of instructions awaiting execution;
  \item Dump -- serves as a store for pushing the current context when a
    function call is performed. The context is again retrieved when a function
    call returns.
\end{itemize}
The standard implementation sees all four of the above items as linked lists.  
\section{Execution}
Execution of the machine consists of reading instructions from the Control and
modifying the state of the machine as necessary. The basic instructions are:
\begin{itemize}
  \item \texttt{ld x} -- load the value bound to the identifier \texttt{x} from
    the environment and put it on the stack;
  \item \texttt{ldf f} -- load the function — i.e., a sequence of instructions —
    \texttt{f} in the current environment, constructing a \textit{closure}, and put it on the
    stack. A Closure is therefore a list of instructions together with an
    environment it can be executed in;
  \item \texttt{ap} -- given that a closure and a value are present on the top
    of the stack, perform function application and afterwards put the return
    value on the stack. Function application consists of popping the closure and
    value from the stack, dumping the current context onto the dump, emptying the
    stack, installing the closure's environment together with the argument, and
    finally loading the closure's code into the control register;
  \item \texttt{rtn} -- return from a function, restoring the context from the
    function dump.
\end{itemize}
In addition, there are instructions for primitive operations, such as integer
addition, list operations such as the head and tail operations, etc. All these
only transform the stack, e.g. integer addition would consume two integers from
the top of the stack and put back the result.

We use the notation $f[e]$ to mean the closure of function $f$ in the
environment $e$ and $∅$ to mean an empty stack, environment, control, or dump.
The notation $e(x)$ refers to the value in environment $e$ bound to the
identifier $x$.

To see how the basic instructions and the addition instruction transform the
machine state, please refer to Figure~\ref{secd}.
\newcolumntype{L}{>{$}l<{$}}
\begin{figure}[h]
  \centering
  \begin{tabular}{L | L | L | L || L | L | L | L}
    \toprule
    \multicolumn{4}{c||}{Before} & \multicolumn{4}{c}{After} \\[2mm]
    \multicolumn{1}{c}{S} & \multicolumn{1}{c}{E} & \multicolumn{1}{c}{C} & \multicolumn{1}{c||}{D} & \multicolumn{1}{c}{S'} & \multicolumn{1}{c}{E'} & \multicolumn{1}{c}{C'} & \multicolumn{1}{c}{D'} \\
    \midrule
    s             & e & \texttt{ld x}\ , c  & d                  & e(x) , s & e    & c  & d               \\
    s             & e & \texttt{ldf f}\ , c & d                  & f[e] , s & e    & c  & d               \\
    x , f[e'] , s & e & \texttt{ap}\ , c    & d                  & ∅        & x,e' & f  & (s , e , c) , d \\
    y , s         & e & \texttt{rtn}\ , c   & (s' , e' , c') , d & y , s'   & e'   & c' & d               \\
    a,b,s         & e & \texttt{add}\ , c   & d                  & a+b , s  & e    & c  & d               \\
    \bottomrule
  \end{tabular}
  \caption{The above table presents the transition relation of the SECD Machine.
  On the left is the state of the machine before the execution of a single
  instruction. On the right is the newly mutated state. The components are read
  from left to right, i.e., the top is the leftmost value.}
  \label{secd}
\end{figure}
It is usual to use De Bruijn indices when referring to identifiers in the
\texttt{ld} instruction. E.g. \texttt{ld 0} loads the topmost value in the
environment and puts it on the stack. Hence, De Bruijn indices are used in the
example in this chapter. They will also be used in the following chapter in the
Agda formalization.

\begin{figure}[h]
  \centering
  \begin{tabular}{L | L | L | L}
    \toprule
    \multicolumn{1}{c}{S} & \multicolumn{1}{c}{E} & \multicolumn{1}{c}{C} & \multicolumn{1}{c}{D} \\
    \midrule
    ∅       & ∅ & \texttt{ldf f, ldc 1, ap, …} & ∅                         \\
    f[∅]    & ∅ & \texttt{ldc 1, ap, ldc 3, add}        & ∅                         \\
    1, f[∅] & ∅ & \texttt{ap, ldc 3, add}               & ∅                         \\
    ∅       & 1 & \texttt{ldc 1, ld 0, add, rtn}        & (∅,∅,\texttt{ldc 3, add}) \\
    1       & 1 & \texttt{ld 0, add, rtn}               & (∅,∅,\texttt{ldc 3, add}) \\
    1,1     & 1 & \texttt{add, rtn}                     & (∅,∅,\texttt{ldc 3, add}) \\
    2       & 1 & \texttt{rtn}                          & (∅,∅,\texttt{ldc 3, add}) \\
    2       & ∅ & \texttt{ldc 3, add}                   & ∅                         \\
    3,2     & ∅ & \texttt{add}                          & ∅                         \\
    5       & ∅ & ∅                                     & ∅                         \\
    \bottomrule
  \end{tabular}
  \caption{Example execution from an empty initial state of the code \texttt{ldf
      f, ldc 1, ap, ldc 3, add} where $\texttt{f} = \texttt{ldc 1, ld 0, add,
      rtn}$.}
  \label{secdexample}
\end{figure}
To see an example of execution of the machine, please refer to Figure
~\ref{secdexample}. This example loads a function, the number $1$, and performs
application of the loaded function, turned closure, to the number. The closure
increments its argument by one. After the closure returns, $3$ is added to the
returned value. The final state has the number $5$ on the stack.

\section{Recursion}
An attentive reader may notice that the above presentation does not give an
obvious way of implementing recursive functions. The issue is that after
execution of the instruction \texttt{ap}, the closure being applied is not
retrievable. In practice, this may be resolved by storing the function on the
stack that is then pushed onto the dump, and reconstructing the closure with the
corresponding environment from the dump when needed.

The additional instructions introduced in this section are summarized in
Figure~\ref{secd_extra}.

\subsection{Function dump}
We propose a dedicated register for storing the closure being applied. Referred
to as the \textit{function dump}, the closure being applied is pushed onto this
register during the instruction \texttt{ap}. With the instruction \texttt{rtn},
the topmost closure is then popped from the function dump and execution proceeds
as normal. The advantages of this approach consist of: (1) better isolation of
components of the machine, leading to a simpler description and formalization,
and (2) the fact that the closure does not need to be reconstructed from the
code of the function and the corresponding environment.

We also introduce the instruction \texttt{ldr} for loading closures from the
function dump. It behaves analogously to the instruction \texttt{ld}, with the
difference that \texttt{ld} serves for retrieving values from the environment,
whereas \texttt{ldr} retrieves closures from the function dump.

\begin{figure}[h]
  \centering
  \begin{tabular}{L | L | L | L | L || L | L | L | L | L}
    \toprule
    \multicolumn{5}{c||}{Before} & \multicolumn{5}{c}{After} \\[2mm]
    \multicolumn{1}{c}{S} & \multicolumn{1}{c}{E} & \multicolumn{1}{c}{C} & \multicolumn{1}{c}{F} & \multicolumn{1}{c||}{D} & \multicolumn{1}{c}{S'} & \multicolumn{1}{c}{E'} & \multicolumn{1}{c}{C'} & \multicolumn{1}{c}{F'} & \multicolumn{1}{c}{D'} \\
    \midrule
    s              & e & \texttt{ldr x}\ , c & f & d & f(x) , s & e    & c  & f & d \\
    x , c'[e'] , s & e & \texttt{rap}\ , c   & f & d & ∅        & x,e' & c' & f & d \\
    \bottomrule
  \end{tabular}
  \caption{The above table presents the additional instructions from this
    section. The capital letter F stands for the function dump.}
  \label{secd_extra}
\end{figure}

\subsection{Tail call optimization}
Another consideration is the elimination of tail calls. The standard
approach~\parencite{modernsecd} is to introduce a new instruction \texttt{rap}
which behaves similarly to \texttt{ap}, with the modification that it does not
bother pushing a return frame onto the dump.

\chapter{Formalization}
In this chapter, we approach the main topic of this thesis. We formalize a
SECD machine in Agda, with typed syntax, and then proceed to define the
semantics by way of coinduction. By typed syntax we mean an approach to SECD
code which performs static verification of the code in question. For example,
the \I{add} instruction is only allowed when two integers are provably on the
top of stack, and a function can only access values from the environment if the
function in question states so in advance in its type.

Finally, we define a typed λ calculus, corresponding to the capabilities of the
SECD machine, and define a compilation procedure from this calculus to typed
SECD programs.

\section{Syntax}
\subsection{Preliminaries}
Before we can proceed, we shall require certain machinery to aid us in
formalizing the type system.

We define the data type \AgdaDatatype{Path}, parametrized by a binary relation,
whose values are finite sequences of values such that each value is in relation
with the next one.

\noindent\begin{minipage}[]{\textwidth}\begin{code}
data Path {A : Set} (R : A → A → Set) : A → A → Set where
  ∅     : ∀ {a} → Path R a a
  _>>_  : ∀ {a b c} → R a b → Path R b c → Path R a c
\end{code}\end{minipage}

\noindent\begin{minipage}[]{\textwidth}\begin{code}[hide]
infixr 5 _>>_
\end{code}\end{minipage}
The first constructor creates an empty path. The second takes an
already existing path and prepends to it a value, given a proof that this value
is in relation with the first element of the already-existing path. The reader
may notice certain similarity to linked lists; indeed if for the relation we
take the universal relation for \AgdaDatatype{A}, we obtain a type that is
isomorphic to linked lists.

We can view this type as the type of finite paths through a graph connected
according to the binary relation.

We also define a shorthand for constructing the end of a path out of two edges.
We use this in examples later on.

\noindent\begin{minipage}[]{\textwidth}\begin{code}
_>|_ : ∀ {A R} {a b c : A} → R a b → R b c → Path R a c
a >| b = a >> b >> ∅
\end{code}\end{minipage}
Furthermore, we can also concatenate two paths, given that the end of the first
path connects to the start of the second one. This is enforced by the type
system of Agda.

\noindent\begin{minipage}[]{\textwidth}\begin{code}
_>+>_ : ∀ {A R} {a b c : A} → Path R a b → Path R b c → Path R a c
∅        >+> r  = r
(x >> l) >+> r  = x >> (l >+> r)
\end{code}\end{minipage}

\noindent\begin{minipage}[]{\textwidth}\begin{code}[hide]
infixr 4 _>+>_
\end{code}\end{minipage}
\subsection{Machine types}
\label{secd_types}
We start by defining the atomic constants our machine operates on. We limit
ourselves to booleans and integers.

\noindent\begin{minipage}[]{\textwidth}\begin{code}
data Const : Set where
  bool  : Bool → Const
  int   : ℤ → Const
\end{code}\end{minipage}
Next, we define an Agda data type which captures the machine's types.

\noindent\begin{minipage}[]{\textwidth}\begin{code}
data Type : Set where
  intT boolT  : Type
  pairT       : Type → Type → Type
  listT       : Type → Type
  _⇒_         : Type → Type → Type
\end{code}\end{minipage}

\noindent\begin{minipage}[]{\textwidth}\begin{code}[hide]
infixr 15 _⇒_
\end{code}\end{minipage}
Firstly, there are types corresponding to the constants we have already defined
above. Then, we also introduce a product type and a list type. Finally, there is
the function type, \AgdaInductiveConstructor{\_⇒\_}, in infix notation.

Now, we define the type assignment of constants.

\noindent\begin{minipage}[]{\textwidth}\begin{code}
typeof : Const → Type
typeof (bool _)  = boolT
typeof (int _)   = intT
\end{code}\end{minipage}
Next, we define the typed stack, environment, and function dump.

\noindent\begin{minipage}[]{\textwidth}\begin{code}
Stack    = List Type
Env      = List Type
FunDump  = List Type
\end{code}\end{minipage}
For now, these only store the information regarding the types of the values in
the machine. Later, when defining semantics, we will give realizations to these,
similarly to how we handled contexts in the formalization of Simply Typed λ
Calculus in~\ref{lambda_semantics}.

Finally, we define the state as a record storing the stack, environment, and the
function dump. Note that we do not formalize the dump register.

\noindent\begin{minipage}[]{\textwidth}\begin{code}
record State : Set where
  constructor _#_#_
  field
    s  : Stack
    e  : Env
    f  : FunDump
\end{code}\end{minipage}
Note that, unlike in the standard presentation of SECD Machines, which we saw in
chapter 4, here the state does not include the code. This is because we are
aiming for a version of SECD with typed assembly code: code will be defined in
the next subsection as a binary relation on states.
\subsection{Syntax}
Since we aim to have typed code, we have to take a different approach to
defining code. We define a binary relation that determines how a state of
a certain \textit{shape} is mutated following the execution of an instruction.
By shape, we mean the types present in the separate components of the state.
Using pattern matching, we are able to put certain restrictions on these, e.g.
we can require that preceding a certain instruction, an integer must be on the
top of the stack.

We have two versions of this relation: the first is the single-step
relation, the second is the reflexive and transitive closure of the first using
\D{Path}.

\noindent\begin{minipage}[]{\textwidth}\begin{code}
infix 5 ⊢_⊳_
infix 5 ⊢_↝_
\end{code}\end{minipage}
Their definitions need to be mutually recursive, because certain instructions —
defined in the single-step relation — need to refer to whole programs, a concept
captured by the multi-step relation.

\noindent\begin{minipage}[]{\textwidth}\begin{code}
mutual
  ⊢_↝_ : State → State → Set
  ⊢ s₁ ↝ s₂ = Path ⊢_⊳_ s₁ s₂
\end{code}\end{minipage}
There is nothing surprising here, we use \D{Path} to define the multi-step
relation.

Next, we define the single-step relation. As mentioned before, this relation
captures how one state might change into another.

\noindent\begin{minipage}[]{\textwidth}\begin{code}
  data ⊢_⊳_ : State → State → Set where
\end{code}\end{minipage}
Here we must define all the instructions our machine should handle. We start
with the simpler ones.

\noindent\begin{minipage}[]{\textwidth}\begin{code}
    ldc  : ∀ {s e f}
         → (const : Const)
         → ⊢ s # e # f ⊳ (typeof const ∷ s) # e # f
\end{code}\end{minipage}
Instruction \I{ldc} loads a constant which is embedded in it. It poses no
restrictions on the state of the machine and mutates the state by pushing the
type of constant on the stack.

\noindent\begin{minipage}[]{\textwidth}\begin{code}
    ld   : ∀ {s e f a}
         → (a ∈ e)
         → ⊢ s # e # f ⊳ (a ∷ s) # e # f
\end{code}\end{minipage}
Instruction \I{ld} loads a value of type \A{a} from the environment and puts it
on the stack. It requires a proof that this value is, indeed, in the
environment.

\noindent\begin{minipage}[]{\textwidth}\begin{code}
    ldf  : ∀ {s e f a b}
         → (⊢ [] # (a ∷ e) # (a ⇒ b ∷ f) ↝ [ b ] # (a ∷ e) # (a ⇒ b ∷ f))
         → ⊢ s # e # f ⊳ (a ⇒ b ∷ s) # e # f
\end{code}\end{minipage}
The \I{ldf} instruction is considerably more involved. It loads a function of
the type \A{a}~\I{⇒}~\A{b}, given as an argument, and puts it on the stack. In
addition, the code we are loading also has to be of a certain shape to make it a
function: it starts with the empty stack and finishes with a single value of
type \A{b} (being returned) on the stack, the argument of type \A{a} it was
called with must be put in the environment, and the function dump is to be
extended with the type of the function itself to permit recursive calls in the
function body. Note that we use the multi-step relation here to describe the
type of the code.

Once a function is loaded, we may apply it,

\noindent\begin{minipage}[]{\textwidth}\begin{code}
    ap   : ∀ {s e f a b}
         → ⊢ (a ∷ a ⇒ b ∷ s) # e # f ⊳ (b ∷ s) # e # f
\end{code}\end{minipage}
The instruction \I{ap} requires that a function and its argument are on the
stack. After it has run, the returned value from the function will be put on the
stack in their stead. The type of this instruction is fairly simple, the
difficult part awaits us further on in the implementation.

\noindent\begin{minipage}[]{\textwidth}\begin{code}
    rtn  : ∀ {s e a b f}
         → ⊢ (b ∷ s) # e # (a ⇒ b ∷ f) ⊳ [ b ] # e # (a ⇒ b ∷ f)
\end{code}\end{minipage}
Return is an instruction we are to use at the end of a function in order to get
the machine state into the one required by \I{ldf}. It throws away what is on
the stack, with the exception of the return value.

Next, let us look at recursive calls.

\noindent\begin{minipage}[]{\textwidth}\begin{code}
    ldr  : ∀ {s e f a b}
         → (a ⇒ b ∈ f)
         → ⊢ s # e # f ⊳ (a ⇒ b ∷ s) # e # f
\end{code}\end{minipage}
The instruction \I{ldr} loads a function for a recursive application from the
function dump. We can be many scopes deep in the function and we use a De Bruijn
index here to count the scopes, same as we do with the environment. This is
important, e.g., for curried functions where we want to be able to load the
topmost function, not one that was already partially applied.

\noindent\begin{minipage}[]{\textwidth}\begin{code}
    rap  : ∀ {s e f a b}
         → ⊢ (a ∷ a ⇒ b ∷ s) # e # f ⊳ [ b ] # e # f
\end{code}\end{minipage}
This instruction looks exactly the same way as \I{ap}. The difference will be in
implementation, as this one will attempt to perform tail call elimination.

\noindent\begin{minipage}[]{\textwidth}\begin{code}
    if   : ∀ {s s' e f}
         → ⊢ s # e # f ↝ s' # e # f
         → ⊢ s # e # f ↝ s' # e # f
         → ⊢ (boolT ∷ s) # e # f ⊳ s' # e # f
\end{code}\end{minipage}
The \I{if} instruction requires that a boolean value is present on the top of
the stack. Based on this value, it decides which branch to execute. Here we hit
on one limitation of the typed presentation: both branches must finish with a
stack of the same shape, otherwise it would be unclear what the stack looks like
after this instruction and static verification of the typed code could not
proceed.

The remaining instructions are fairly simple in that they only manipulate the
stack. Their types are outlined in Figure~\ref{instypes}.
\begin{figure}[h]
  \centering
  \begin{tabular}{L | L | L}
    \toprule
    \multicolumn{1}{c}{Instruction} & \multicolumn{1}{c}{Stack before} & \multicolumn{1}{c}{Stack after} \\
    \midrule
    \I{nil}  & \A{s}                               & \A{}\I{listT}\A{\ a ∷ s}     \\
    \I{flp}  & \A{a ∷ b ∷ s}                       & \A{b ∷ a ∷ s}                \\
    \I{cons} & \A{a ∷\ }\I{listT}\A{\ a ∷ s}       & \A{}\I{listT}\A{\ a ∷ s}     \\
    \I{head} & \I{listT}\A{\ a ∷ s}                & \A{a ∷ s}                    \\
    \I{tail} & \I{listT}\A{\ a ∷ s}                & \A{}\I{listT}\A{\ a ∷ s}     \\
    \I{pair} & \A{a ∷ b ∷ s}                       & \A{}\I{pairT}\A{\ a \ b ∷ s} \\
    \I{fst}  & \I{pairT}\A{\ a \ b ∷ s}            & \A{a ∷ s}                    \\
    \I{snd}  & \I{pairT}\A{\ a \ b ∷ s}            & \A{b ∷ s}                    \\
    \I{add}  & \I{intT}\A{\ ∷ \ }\I{intT}\A{\ ∷ s} & \I{intT}\A{\ ∷ s}            \\
    \I{sub}  & \I{intT}\A{\ ∷ \ }\I{intT}\A{\ ∷ s} & \I{intT}\A{\ ∷ s}            \\
    \I{mul}  & \I{intT}\A{\ ∷ \ }\I{intT}\A{\ ∷ s} & \I{intT}\A{\ ∷ s}            \\
    \I{eq?}  & \A{a ∷ a ∷ s}                       & \I{boolT}\A{\ ∷ s}           \\
    \I{not}  & \I{boolT}\A{\ ∷ s}                  & \I{boolT}\A{\ ∷ s}           \\
    \bottomrule
  \end{tabular}
  \caption{Instructions implementing primitive operations and their associated
    types, i.e., their manipulations of the stack.}
  \label{instypes}
\end{figure}

\noindent\begin{minipage}[]{\textwidth}\begin{code}[hide]
    nil  : ∀ {s e f a}
         → ⊢ s # e # f ⊳ (listT a ∷ s) # e # f
    flp  : ∀ {s e f a b}
         → ⊢ (a ∷ b ∷ s) # e # f ⊳ (b ∷ a ∷ s) # e # f
    cons : ∀ {s e f a}
         → ⊢ (a ∷ listT a ∷ s) # e # f ⊳ (listT a ∷ s) # e # f
    head : ∀ {s e f a}
         → ⊢ (listT a ∷ s) # e # f ⊳ (a ∷ s) # e # f
    tail : ∀ {s e f a}
         → ⊢ (listT a ∷ s) # e # f ⊳ (listT a ∷ s) # e # f
    pair : ∀ {s e f a b}
         → ⊢ (a ∷ b ∷ s) # e # f ⊳ (pairT a b ∷ s) # e # f
    fst  : ∀ {s e f a b}
         → ⊢ (pairT a b ∷ s) # e # f ⊳ (a ∷ s) # e # f
    snd  : ∀ {s e f a b}
         → ⊢ (pairT a b ∷ s) # e # f ⊳ (b ∷ s) # e # f
    add  : ∀ {s e f}
         → ⊢ (intT ∷ intT ∷ s) # e # f ⊳ (intT ∷ s) # e # f
    sub  : ∀ {s e f}
         → ⊢ (intT ∷ intT ∷ s) # e # f ⊳ (intT ∷ s) # e # f
    mul  : ∀ {s e f}
         → ⊢ (intT ∷ intT ∷ s) # e # f ⊳ (intT ∷ s) # e # f
    eq?  : ∀ {s e f a}
         → ⊢ (a ∷ a ∷ s) # e # f ⊳ (boolT ∷ s) # e # f
    nt   : ∀ {s e f}
         → ⊢ (boolT ∷ s) # e # f ⊳ (boolT ∷ s) # e # f
\end{code}\end{minipage}
\subsection{Derived instructions}
For the sake of sanity we also define what amounts to simple programs,
masquerading as instructions, for use in more complex programs later. The chief
limitation here is that since these are members of the multi-step relation, we
have to be mindful when using them and use concatenation of paths, \F{\_>+>\_}, as
necessary.

\noindent\begin{minipage}[]{\textwidth}\begin{code}
nil? : ∀ {s e f a} → ⊢ (listT a ∷ s) # e # f ↝ (boolT ∷ s) # e # f
nil? = nil >| eq?

loadList : ∀ {s e f} → List ℕ → ⊢ s # e # f ↝ (listT intT ∷ s) # e # f
loadList []        = nil >> ∅
loadList (x ∷ xs)  = loadList xs >+> ldc (int (+ x)) >| cons
\end{code}\end{minipage}
The first one is simply the check for an empty list. The second one is more
interesting, it constructs a sequence of instructions which will load a list of
natural numbers. Note that the constructor \I{+\_} is used to construct a
positive Agda integer from a natural number.
\subsection{Examples}
\label{syntax_tests}
In this section, we present some examples of SECD programs in our current
formalism. Starting with trivial ones, we work our way up to using full
capabilities of the machine.

The first example loads two constants and adds them.

\noindent\begin{minipage}[]{\textwidth}\begin{code}
2+3 : ⊢ [] # [] # [] ↝ [ intT ] # [] # []
2+3 =
    ldc (int (+ 2))
 >> ldc (int (+ 3))
 >| add
\end{code}\end{minipage}
The second example constructs a function which expects an integer and increases
it by one before returning it.

\noindent\begin{minipage}[]{\textwidth}\begin{code}
inc : ∀ {e f} → ⊢ [] # (intT ∷ e) # (intT ⇒ intT ∷ f)
                ↝ [ intT ] # (intT ∷ e) # (intT ⇒ intT ∷ f)
inc =
    ld 𝟎
 >> ldc (int (+ 1))
 >> add
 >| rtn
\end{code}\end{minipage}
Here, we can see the type of the expression getting more complicated. We use
polymorphism to make sure we can load this function in any environment. In the
type of the environment, we have to declare that an argument of type \I{intT} is
expected, and the function dump has to be extended with the type of this
function.

In the next example, we load the above function and apply it to the integer 2.

\noindent\begin{minipage}[]{\textwidth}\begin{code}
inc2 : ⊢ [] # [] # [] ↝ [ intT ] # [] # []
inc2 =
    ldf inc
 >> ldc (int (+ 2))
 >| ap
\end{code}\end{minipage}
In the next example we test partial application.

\noindent\begin{minipage}[]{\textwidth}\begin{code}
λTest : ⊢ [] # [] # [] ↝ [ intT ] # [] # []
λTest =
     ldf
       (ldf
         (ld 𝟎 >> ld 𝟏 >> add >| rtn) >| rtn)
  >> ldc (int (+ 1))
  >> ap
  >> ldc (int (+ 2))
  >| ap
\end{code}\end{minipage}
First we construct a function which constructs a function which adds two topmost
values from the environment. The types of these two values are inferred to be
integers by Agda, as this is what the \I{add} instruction requires. Then, we
load and apply the constant \AgdaNumber{1}. This results in another function,
partially applied. Lastly, we load \AgdaNumber{2} and apply.

In the example \F{inc}, we saw how we could define a function. In the next
example we also construct a function. However, this time we embed the instruction
\I{ldf} in our definition directly, as this simplifies the type considerably.

\noindent\begin{minipage}[]{\textwidth}\begin{code}
plus : ∀ {s e f} → ⊢ s # e # f ⊳ ((intT ⇒ intT ⇒ intT) ∷ s) # e # f
plus = ldf (ldf (ld 𝟎 >> ld 𝟏 >> add >| rtn) >| rtn)
\end{code}\end{minipage}
The only consideration is that when we wish to use this function in another
program, rather than writing \I{ldf} \F{plus}, we must only write \F{plus}.

For an example of a recursive function, consider that of a mapping function,

\noindent\begin{minipage}[]{\textwidth}\begin{code}
map : ∀ {e f a b} →
      ⊢ [] # e # f ⊳ [ (a ⇒ b) ⇒ listT a ⇒ listT b ] # e # f
map = ldf (ldf body >| rtn)
  where
  body =
           ld 𝟎
        >> nil?
        >+> if (nil >| rtn)
            (ldr 𝟎 >> ld 𝟎 >> tail >> ap
            >> ld 𝟏 >> ld 𝟎 >> head >> ap
            >| cons)
        >> ∅
\end{code}\end{minipage}

Here we first load the list we are mapping over. We check for emptiness, if the
argument is empty we return the empty list. In the case that it is not, we need
to make a recursive call. We use a trick: we load \F{map} already partially
applied with the first argument, i.e., the mapping function, with the call
\I{ldr} \F{𝟎}. Then we load the list with \I{ld} \F{𝟎}, obtain its \I{head}, and
apply. Result is the rest of the list already mapped over.

Now to map over the first element, we load the mapping function with \I{ld}
\F{𝟏}. Then we retrieve the first element of the list — similarly as we did
above, only this time we use \I{head} — and apply. Result is the newly mapped
element on the top of the stack and the rest of the transformed list below it:
we \I{cons} the two.

Lastly, a more involved example: that of a folding function. Here we test all
capabilities of the machine.

\noindent\begin{minipage}[]{\textwidth}\begin{code}
foldl : ∀ {e f a b} →
        ⊢ [] # e # f ⊳ [ ((b ⇒ a ⇒ b) ⇒ b ⇒ (listT a) ⇒ b) ] # e # f
foldl = ldf (ldf (ldf body >| rtn) >| rtn)
  where
    body =
         ld 𝟎
      >> nil?
      >+> if (ld 𝟏 >| rtn)
          (ld 𝟐 >> ld 𝟏 >> ap
        >> ld 𝟎 >> head >> ap
        >> ldr 𝟐 >> ld 𝟐 >> ap
        >> flp >> ap
        >> ld 𝟎 >> tail >| rap)
      >> ∅
\end{code}\end{minipage}
To start, we load the list we are folding. We check
whether it is empty: if so, the accumulator \F{𝟏} is loaded and returned. On the other
hand, if the list is not empty, we start with loading the folding function \F{𝟐}.
Next, we load the accumulator \F{𝟏}. We perform partial application. Then, we
load the list \F{𝟎} and obtain its first element with \I{head}. We apply to the
already partially-applied folding function, yielding the new accumulator on the
top of the stack.

Now we need to make the recursive call: we load the function \F{foldl} itself
with \I{ldr} \F{𝟐}. Next we need to apply all three arguments: we start with
loading the folding function \F{𝟐} and applying it. We are now in a state where
the partially applied \F{foldl} is on the top of the stack and the new
accumulator is right below it; we flip\footnote{Note we could have reorganized
  the instructions in a manner so that this flip would not be necessary. Indeed,
  later we see that there is no need for this instruction in
  section~\ref{compilation}} the two and apply. Lastly, we load the list \F{𝟎},
drop the first element with \I{tail} and perform the recursive application with
tail-call elimination.
\section{Semantics}
Having defined the syntax, we can now turn to semantics. In this section, we
give operational semantics to the SECD machine syntax defined in the previous
section.

\subsection{Types}
We begin, similarly to how we handled the semantics in Section ~\ref{lambda_semantics},
by giving semantics to the types. Here we have to proceed by mutual
induction, as in certain places we need to make references to the semantics
of other types, and vice versa. The order of the following definitions is
arbitrary from the point of view of correctness and was chosen purely for
improving readability.

\noindent\begin{minipage}[]{\textwidth}\begin{code}
mutual
  ⟦_⟧ᵗ : Type → Set
  ⟦ intT ⟧ᵗ         = ℤ
  ⟦ boolT ⟧ᵗ        = Bool
  ⟦ pairT t₁ t₂ ⟧ᵗ  = ⟦ t₁ ⟧ᵗ × ⟦ t₂ ⟧ᵗ
  ⟦ a ⇒ b ⟧ᵗ        = Closure a b
  ⟦ listT t ⟧ᵗ      = List ⟦ t ⟧ᵗ
\end{code}\end{minipage}
Here we realized the machine types as the corresponding types in Agda. The
exception is the type of functions, which we realize as a closure. The meaning
of \D{Closure} will be defined at a later moment in the mutual block.

We proceed by giving semantics to the environment,

\noindent\begin{minipage}[]{\textwidth}\begin{code}
  ⟦_⟧ᵉ : Env → Set
  ⟦ [] ⟧ᵉ      = ⊤
  ⟦ x ∷ xs ⟧ᵉ  = ⟦ x ⟧ᵗ × ⟦ xs ⟧ᵉ
\end{code}\end{minipage}
The semantics of an environment are fairly straightforward, we make a reference to
the semantic function for types and inductively define the environment as a
product of semantics of each type in it.

Next, we define the semantics of the function dump, which will be necessary in
the definition in \D{Closure},

\noindent\begin{minipage}[]{\textwidth}\begin{code}
  ⟦_⟧ᵈ : FunDump → Set
  ⟦ [] ⟧ᵈ               = ⊤
  ⟦ intT ∷ xs ⟧ᵈ        = ⊥
  ⟦ boolT ∷ xs ⟧ᵈ       = ⊥
  ⟦ pairT x x₁ ∷ xs ⟧ᵈ  = ⊥
  ⟦ a ⇒ b ∷ xs ⟧ᵈ       = Closure a b × ⟦ xs ⟧ᵈ
  ⟦ listT x ∷ xs ⟧ᵈ     = ⊥
\end{code}\end{minipage}
Since the type of the function dump technically permits also non-function types
in it, we have to handle them here by simply saying that they may not be
present in the function dump. There is, after all, no instruction that would
allow putting a non-function type in the dump.

Now, finally for the definition of \D{Closure}. We define it as a record
containing the code of the function, a realization of the starting environment,
and finally a realization of the function dump. Recall that the function dump
contains the closures introduced by \I{ldf} instructions higher in the syntax tree.

\noindent\begin{minipage}[]{\textwidth}\begin{code}
  record Closure (a b : Type) : Set where
    inductive
    constructor ⟦_⟧ᶜ×⟦_⟧ᵉ×⟦_⟧ᵈ
    field
      {e}   : Env
      {f}   : FunDump
      ⟦c⟧ᶜ  : ⊢ [] # (a ∷ e) # (a ⇒ b ∷ f)
              ↝ [ b ] # (a ∷ e) # (a ⇒ b ∷ f)
      ⟦e⟧ᵉ  : ⟦ e ⟧ᵉ
      ⟦f⟧ᵈ  : ⟦ f ⟧ᵈ
\end{code}\end{minipage}
This concludes the mutual block of definitions.

There is one more type we have not handled yet, \D{Stack}, which is not required
to be in the mutual block above,

\noindent\begin{minipage}[]{\textwidth}\begin{code}
⟦_⟧ˢ : Stack → Set
⟦ [] ⟧ˢ      = ⊤
⟦ x ∷ xs ⟧ˢ  = ⟦ x ⟧ᵗ × ⟦ xs ⟧ˢ
\end{code}\end{minipage}
The stack is realized similarly to the environment, however the environment is
referenced in the definition of \D{Closure}, making it necessary for it to be in
the mutual definition block.

\subsection{Auxiliary functions}
In order to proceed with giving semantics to SECD execution, we first need
a few auxiliary functions to lookup values from the environment and from the
function dump.

As for the environment, the situation is fairly simple,

\noindent\begin{minipage}[]{\textwidth}\begin{code}
lookupᵉ : ∀ {x xs} → ⟦ xs ⟧ᵉ → x ∈ xs → ⟦ x ⟧ᵗ
lookupᵉ (x , _) here        = x
lookupᵉ (_ , xs) (there w)  = lookupᵉ xs w
\end{code}\end{minipage}
Looking up values from the function dump is slightly more involved, because Agda
doesn't let us pattern-match on the first argument as we did here. This is
because the definition of \F{⟦\_⟧ᵈ} is more involved than that of \F{⟦\_⟧ᵉ}.
Specifically, there is the possibility of the dump being uninhabited. Instead,
we must define an auxiliary function to drop the first element of the product,

\noindent\begin{minipage}[]{\textwidth}\begin{code}
tailᵈ : ∀ {x xs} → ⟦ x ∷ xs ⟧ᵈ → ⟦ xs ⟧ᵈ
tailᵈ {intT} ()
tailᵈ {boolT} ()
tailᵈ {pairT x x₁} ()
tailᵈ {a ⇒ b} (_ , xs) = xs
tailᵈ {listT x} ()
\end{code}\end{minipage}
We pattern-match on the type of the value in the environment. This forces Agda
to realize that only a closure may be in the function dump, at which point we
can pattern-match on the product and drop the first element.

Now we can define the lookup operation for the function dump,

\noindent\begin{minipage}[]{\textwidth}\begin{code}
lookupᵈ : ∀ {a b f} → ⟦ f ⟧ᵈ → a ⇒ b ∈ f → Closure a b
lookupᵈ (x , _) here  = x
lookupᵈ f (there w)   = lookupᵈ (tailᵈ f) w
\end{code}\end{minipage}
dropping the elements as necessary with \F{tailᵈ} until we get to the desired
closure.

Lastly, we define a function for comparing two values of the machine,

\noindent\begin{minipage}[]{\textwidth}\begin{code}
compare : {t : Type} → ⟦ t ⟧ᵗ → ⟦ t ⟧ᵗ → Bool
compare {intT} a b                   = ⌊ a ≟ℤ b ⌋
compare {boolT} a b                  = ⌊ a ≟B b ⌋
compare {pairT _ _} (a , b) (c , d)  = compare a c ∧ compare b d
compare {listT _} [] []              = tt
compare {listT _} (a ∷ as) (b ∷ bs)  = compare a b ∧ compare as bs
compare {listT _} _ _                = ff
compare {_ ⇒ _} _ _                  = ff
\end{code}\end{minipage}
The above code implements standard comparison by structural induction. Functions
\F{\_≟ℤ\_} and \F{\_≟B\_} are standard functions implementing decidable equality
for the corresponding types. We refuse to perform any meaningful comparison of
functions, instead treating any two functions as dissimilar.

\subsection{Execution}
Now we are finally ready to define the execution of instructions. Let us start
with the type,

\noindent\begin{minipage}[]{\textwidth}\begin{code}
run : ∀ {s s' e e' f f' i} → ⟦ s ⟧ˢ → ⟦ e ⟧ᵉ → ⟦ f ⟧ᵈ
                           → ⊢ s # e # f ↝ s' # e' # f'
                           → Delay ⟦ s' ⟧ˢ i
\end{code}\end{minipage}
Here we say that in order to execute the code
\[
  \D {⊢}\ s\ \I{\#}\ e\ \I{\#}\ f\ \D{↝}\ s'\ \I{\#}\ e'\ \I{\#}\ f'
\]
we require realizations of the stack \A{s}, environment \A{e}, and function dump
\A{f}. We return the stack the code stops execution in, wrapped in the
\D{Delay} monad in order to allow for non-structurally inductive and — possibly
non-terminating — calls that will be necessary in some cases.

We proceed by structural induction on the last argument, i.e., the code. We start
with the empty run,

\noindent\begin{minipage}[]{\textwidth}\begin{code}
run s e d ∅ = now s
\end{code}\end{minipage}
In the case of an empty run, it holds that $s = s'$ and so we simply finish the
execution, returning the current stack.

Next we consider all the cases when the run is not empty. We start with the
instruction \I{ldf},

\noindent\begin{minipage}[]{\textwidth}\begin{code}
run s e d (ldf code >> r) =
  run (⟦ code ⟧ᶜ×⟦ e ⟧ᵉ×⟦ d ⟧ᵈ , s) e d r
\end{code}\end{minipage}
Recall that this instruction is supposed to load a function. Since the
semantical meaning of a function is a closure, this is what we must construct.
We do so out of the code, given as an argument to \I{ldf}, and the current
environment and function dump. We use the constructor of \F{Closure},
\I{⟦\_⟧ᶜ×⟦\_⟧ᵉ×⟦\_⟧ᵈ}. We put this closure on the stack and proceed with
execution of the rest of the run.

\noindent\begin{minipage}[]{\textwidth}\begin{code}
run s e d (ld at >> r) = run (lookupᵉ e at , s) e d r
\end{code}\end{minipage}
This instruction loads a value from the environment with the help of the
auxiliary function \F{lookupᵉ} and puts it on the stack.

\noindent\begin{minipage}[]{\textwidth}\begin{code}
run s e d (ldc const >> r) = run (makeConst const , s) e d r
  where makeConst : (c : Const) → ⟦ typeof c ⟧ᵗ
        makeConst (bool x)  = x
        makeConst (int x)   = x
\end{code}\end{minipage}
In order to load a constant, we introduce an auxiliary conversion function for
converting from an embedded constant to a semantical value. The constant is then
put on the stack.

\noindent\begin{minipage}[]{\textwidth}\begin{code}
run s e d (ldr at >> r) =
  run (lookupᵈ d at , s) e d r
\end{code}\end{minipage}
This instruction loads a closure from the function dump and puts it on the
stack. Similarly to \I{ld}, we use an auxiliary function, in this case
\F{lookupᵈ}.

Next, we handle the instruction for function application, employing
\AgdaKeyword{do}-syntax,

\noindent\begin{minipage}[]{\textwidth}\begin{code}
run (a , ⟦ code ⟧ᶜ×⟦ fE ⟧ᵉ×⟦ dump ⟧ᵈ , s) e d (ap >> r) =
  later
    λ where
      .force →
        do
          (b , _) ← run ⋅
                        (a , fE)
                        (⟦ code ⟧ᶜ×⟦ fE ⟧ᵉ×⟦ dump ⟧ᵈ , dump)
                        code
          run (b , s) e d r
\end{code}\end{minipage}
Here we have to employ coinduction for the first time, as we need to perform a
call to \F{run} that is not structurally recursive. This call is used to
evaluate the closure, starting from the empty stack \I{⋅}, in environment \A{fE}
extended with the function argument \A{a}. The function dump also needs to be
extended with the closure being evaluated in order to allow recursive calls.
Once the call to \F{run} has returned, we grab the first item on the stack \A{b}
and resume execution of the rest of the run \A{r} with \A{b} put on the stack.

We now handle recursive tail calls, i.e., the instruction \I{rap}. We need
to make an additional case split here on the rest of the run \A{r}, as a tail
call can really only occur if \I{rap} is the last instruction in the current
run. However, there is no syntactic restriction that would prevent more
instructions to follow a \I{rap}.

\noindent\begin{minipage}[]{\textwidth}\begin{code}
run (a , ⟦ code ⟧ᶜ×⟦ fE ⟧ᵉ×⟦ dump ⟧ᵈ , s) e d (rap >> ∅) =
  later
    λ where
      .force →
        run ⋅ (a , fE) (⟦ code ⟧ᶜ×⟦ fE ⟧ᵉ×⟦ dump ⟧ᵈ , dump) code
\end{code}\end{minipage}
Above is the case when we can perform the tail call. In this case, the types
align: recall that in the type signature of \F{run} we promised to return a
stack of the type \A{s'}. Here, as \I{rap} is the last instruction, this means a
stack containing a single item of some type \A{β}. This is exactly what the
closure on the stack constructs. Hence, we can shift execution to the closure.

If there are more instructions after \I{rap}, we are not so lucky: here we don't
know what \A{s'} is, and we have but one way to obtain a stack of this type:
proceed with evaluating the rest of the run \A{r}. As such, we are unable to
perform a tail call. Thus, we side-step the problem by converting \I{rap} to
\I{ap}, performing the standard function application.

\noindent\begin{minipage}[]{\textwidth}\begin{code}
run (a , ⟦ code ⟧ᶜ×⟦ fE ⟧ᵉ×⟦ dump ⟧ᵈ , s) e d (rap >> r) =
  later
    λ where
      .force →
        run (a , ⟦ code ⟧ᶜ×⟦ fE ⟧ᵉ×⟦ dump ⟧ᵈ , ⋅) e d (ap >> r)
\end{code}\end{minipage}
This approach also has the advantage of being able to use the instruction
\I{rap} indiscriminately instead of \I{ap} in all situations, at the cost of
delaying the execution slightly. However, as we discover in Section
~\ref{compilation}, this is hardly necessary.

Next, we have the \I{rtn} instruction, which simply drops all items from the stack
but the topmost one. Once again, we have no guarantee that there are no more
instructions after \I{rtn}, hence we make a recursive call to \F{run}. Under
normal circumstances, \A{r} is the empty run \I{∅} and the execution returns the
stack here constructed.

\noindent\begin{minipage}[]{\textwidth}\begin{code}
run (b , _) e d (rtn >> r) = run (b , ⋅) e d r
\end{code}\end{minipage}
The \I{if} instruction follows,

\noindent\begin{minipage}[]{\textwidth}\begin{code}
run (test , s) e d (if c₁ c₂ >> r) with test
… | tt  = later λ where .force → run s e d (c₁ >+> r)
… | ff  = later λ where .force → run s e d (c₂ >+> r)
\end{code}\end{minipage}
This instruction examines the boolean value on top of the stack and prepends the
correct branch to \A{r}.

The instructions that remain are those implementing primitive operations that
only manipulate the stack. We include them here for completeness' sake.

\noindent\begin{minipage}[]{\textwidth}\begin{code}
run s e d (nil >> r)              = run ([] , s) e d r
run (x , y , s) e d (flp >> r)    = run (y , x , s) e d r
run (x , xs , s) e d (cons >> r)  = run (x ∷ xs , s) e d r
run ([] , s) e d (head >> r)      = never
run (x ∷ _ , s) e d (head >> r)   = run (x , s) e d r
run ([] , s) e d (tail >> r)      = never
run (_ ∷ xs , s) e d (tail >> r)  = run (xs , s) e d r
run (x , y , s) e d (pair >> r)   = run ((x , y) , s) e d r
run ((x , _) , s) e d (fst >> r)  = run (x , s) e d r
run ((_ , y) , s) e d (snd >> r)  = run (y , s) e d r
run (x , y , s) e d (add >> r)    = run (x + y , s) e d r
run (x , y , s) e d (sub >> r)    = run (x - y , s) e d r
run (x , y , s) e d (mul >> r)    = run (x * y , s) e d r
run (a , b , s) e d (eq? >> r)    = run (compare a b , s) e d r
run (x , s) e d (nt >> r)         = run (not x , s) e d r
\end{code}\end{minipage}
The only interesting cases here are \I{head} and \I{tail} when called on an
empty list. In this case, we signal an error by terminating the execution,
returning instead an infinitely delayed value with \F{never}.

\subsection{A note regarding function application}
There is one final remark to be said regarding the above implementation of the
semantics. We have not captured the concept of the dump as introduced first in
Chapter 5. Rather, we have exploited the Agda calls stack for the dump's
purposes. The instruction in question is function application \I{ap}, where we
use a \AgdaKeyword{do} block in which we launch execution of the closure using a
recursive call to \F{run}. We then use the result thus obtained to proceed with
execution. In other words, Agda call stack serves as our function dump.

The reason for this approach is twofold. Firstly, this simplifies the
formalization slightly, as we avoided having to formalize the dump register. The
second reason is more serious: there is no simple approach to extending the
above formalization with the dump register. This is due to the typed syntax of
code. When writing some typed code, we must treat the \I{ap} instruction as
having completed in one step, the next instruction after \I{ap} must already
have access to the result of the function application in question; pretending
that the function has already returned. However, when implementing the
semantics, we need to perform all the instructions between the execution of
\I{ap} and the return from the function with \I{rtn}. The types do not align
here: in syntax, we only care about the type of the return value of \I{ap},
whereas in semantics we must also perform all the work of the function before
returning.

In other words, it appears that there is no simple way to extend the above
approach to also formalize the dump register. This is however an interesting
problem that may be worthy of future considerations.
\subsection{Tests}
Being done with the trickiest part, we now define an auxiliary function for use
in tests. It takes some code which starts from an empty initial state. In
addition, there is a second argument, which signifies an upper bound on the
number of indirections that may be encountered during execution. If this bound
is exceeded, \I{nothing} is returned.

\noindent\begin{minipage}[]{\textwidth}\begin{code}
runℕ : ∀ {x s} → ⊢ [] # [] # [] ↝ (x ∷ s) # [] # []
               → ℕ
               → Maybe ⟦ x ⟧ᵗ
runℕ c n = runFor n
  do
    (x , _) ← run ⋅ ⋅ ⋅ c
    now x
\end{code}\end{minipage}
Here we made use of \F{runFor} defined in Section~\ref{delay_monad}.

Now for the promised tests, we evaluate the examples from~\ref{syntax_tests}.

\noindent\begin{minipage}[]{\textwidth}\begin{code}
_ : runℕ 2+3 0 ≡ just (+ 5)
_ = refl

_ : runℕ inc2 1 ≡ just (+ 3)
_ = refl

_ : runℕ λTest 2 ≡ just (+ 3)
_ = refl
\end{code}\end{minipage}
So far, so good! Now for something more complicated, we \F{foldl} the list
$[1,2,3,4]$ with \F{plus} and the initial accumulator \AgdaNumber{0}. Below we
have the code to achieve this,

\noindent\begin{minipage}[]{\textwidth}\begin{code}
foldTest : ⊢ [] # [] # [] ↝ [ intT ] # [] # []
foldTest =
     foldl
  >> plus
  >> ap
  >> ldc (int (+ 0))
  >> ap
  >> loadList (1 ∷ 2 ∷ 3 ∷ 4 ∷ [])
  >+> ap
  >> ∅
\end{code}\end{minipage}
And indeed,

\noindent\begin{minipage}[]{\textwidth}\begin{code}
_ : runℕ foldTest 28 ≡ just (+ 10)
_ = refl
\end{code}\end{minipage}
Let us also examine the mapping function \F{map}, employed here to
increment each element of the list $[1,2,3]$ by $1$,

\noindent\begin{minipage}[]{\textwidth}\begin{code}
mapTest : ⊢ [] # [] # [] ↝ [ listT intT ] # [] # []
mapTest =
     map
  >> plus
  >> ldc (int (+ 1))
  >> ap
  >> ap
  >> loadList (1 ∷ 2 ∷ 3 ∷ [])
  >+> ap
  >> ∅
\end{code}\end{minipage}

\noindent\begin{minipage}[]{\textwidth}\begin{code}
_ : runℕ mapTest 13 ≡ just ((+ 2) ∷ (+ 3) ∷ (+ 4) ∷ [])
_ = refl
\end{code}\end{minipage}
\section{Compilation from a high-level language}
\label{compilation}
As a final step, we define a typed λ calculus and implement compilation to typed
SECD instructions defined in previous sections.

\subsection{Syntax}
We reuse the types defined in Section~\ref{secd_types}. This will not only
make compilation cleaner, but also makes sense from a moral standpoint: we want
our λ calculus to model the capabilities of our SECD machine. Hence, a context
is a list of (SECD) types,

\noindent\begin{minipage}[]{\textwidth}\begin{code}
Ctx = List Type
\end{code}\end{minipage}
As for the typing relation, we use a similar trick as with the SECD function
dump to allow recursive calls. We keep two contexts, \A{Γ} for tracking
variables, as in Section~\ref{lambda_syntax}, and \A{Ψ} for tracking types of
functions we can call recursively.

\noindent\begin{minipage}[]{\textwidth}\begin{code}[hide]
infix 2 _×_⊢_
\end{code}\end{minipage}

\noindent\begin{minipage}[]{\textwidth}\begin{code}
data _×_⊢_ : Ctx → Ctx → Type → Set where
  var  : ∀ {Ψ Γ x} → x ∈ Γ → Ψ × Γ ⊢ x
  ƛ_   : ∀ {Ψ Γ α β} → (α ⇒ β ∷ Ψ) × α ∷ Γ ⊢ β → Ψ × Γ ⊢ α ⇒ β
  _$_  : ∀ {Ψ Γ α β} → Ψ × Γ ⊢ α ⇒ β → Ψ × Γ ⊢ α → Ψ × Γ ⊢ β
\end{code}\end{minipage}
The first three typing rules resemble closely the ones from Section~\ref{lambda_syntax},
with the addition of the function context \A{Ψ}.

Next, we have a variation of \I{var} for loading functions from \A{Ψ},

\noindent\begin{minipage}[]{\textwidth}\begin{code}
  rec : ∀ {Ψ Γ α β} → (α ⇒ β) ∈ Ψ → Ψ × Γ ⊢ α ⇒ β
\end{code}\end{minipage}
We also have an if-then-else construct and a polymorphic comparison operator,

\noindent\begin{minipage}[]{\textwidth}\begin{code}
  if_then_else_ : ∀ {Ψ Γ α} → Ψ × Γ ⊢ boolT
                            → Ψ × Γ ⊢ α → Ψ × Γ ⊢ α
                            → Ψ × Γ ⊢ α
  _==_ : ∀ {Ψ Γ α} → Ψ × Γ ⊢ α → Ψ × Γ ⊢ α → Ψ × Γ ⊢ boolT
\end{code}\end{minipage}
Finally, we have the integers and some primitive operations on them,

\noindent\begin{minipage}[]{\textwidth}\begin{code}
  #_   : ∀ {Ψ Γ} → ℤ → Ψ × Γ ⊢ intT
  _＋_ _∗_ _–_  : ∀ {Ψ Γ} → Ψ × Γ ⊢ intT → Ψ × Γ ⊢ intT
                         → Ψ × Γ ⊢ intT
\end{code}\end{minipage}

\noindent\begin{minipage}[]{\textwidth}\begin{code}[hide]
infixr 2 ƛ_
infixl 3 _$_
infix 5 _==_
infixl 10 _∗_
infixl 5 _–_
\end{code}\end{minipage}
We also define the shorthand operator \F{\#⁺\_} for embedding Agda natural
numbers into \I{\#\_},

\noindent\begin{minipage}[]{\textwidth}\begin{code}
#⁺_ : ∀ {Ψ Γ} → ℕ → Ψ × Γ ⊢ intT
#⁺ n = # (+ n)
\end{code}\end{minipage}

As an example, consider the factorial function in this formalism,

\noindent\begin{minipage}[]{\textwidth}\begin{code}
fac : [] × [] ⊢ (intT ⇒ intT)
fac = ƛ if (var 𝟎 == #⁺ 1)
          then #⁺ 1
          else (var 𝟎 ∗ (rec 𝟎 $ (var 𝟎 – #⁺ 1)))
\end{code}\end{minipage}
\subsection{Compilation}
For the compilation, we use a scheme of two mutually recursive functions
adapted from~\parencite{modernsecd}. The first function, \F{compileT}, is used
to compile expressions in the tail position, whereas \F{compile} is used for the
other cases.

\noindent\begin{minipage}[]{\textwidth}\begin{code}
mutual
  compileT : ∀ {Ψ Γ α β} → (α ⇒ β ∷ Ψ) × (α ∷ Γ) ⊢ β
                         → ⊢ [] # (α ∷ Γ) # (α ⇒ β ∷ Ψ)
                           ↝ [ β ] # (α ∷ Γ) # (α ⇒ β ∷ Ψ)
  compileT (f $ x) =
    compile f >+> compile x >+> rap >> ∅
  compileT (if t then a else b) =
    compile t >+> if (compileT a) (compileT b) >> ∅
  compileT t = compile t >+> rtn >> ∅
\end{code}\end{minipage}

\noindent\begin{minipage}[]{\textwidth}\begin{code}
  compile : ∀ {Ψ Γ α s} → Ψ × Γ ⊢ α
                        → ⊢ s # Γ # Ψ ↝ (α ∷ s) # Γ # Ψ
  compile (var x)  = ld x >> ∅
  compile (ƛ t)    = ldf (compileT t) >> ∅
  compile (f $ x)  = compile f >+> compile x >+> ap >> ∅
  compile (rec x)  = ldr x >> ∅
  compile (if t then a else b) =
    compile t >+> if (compile a) (compile b) >> ∅
  compile (a == b)  = compile b >+> compile a >+> eq? >> ∅
  compile (# x)     = ldc (int x) >> ∅
  compile (a ＋ b)  = compile b >+> compile a >+> add >> ∅
  compile (a ∗ b)   = compile b >+> compile a >+> mul >> ∅
  compile (a – b)   = compile b >+> compile a >+> sub >> ∅
\end{code}\end{minipage}
We now compile the above definition of \F{fac}. Below is the result,
adjusted for readability.

\noindent\begin{minipage}[]{\textwidth}\begin{code}
_ : compile {s = []} fac ≡ ldf (
     ldc (int (+ 1)) >> ld 𝟎 >> eq?
  >| if (ldc (int (+ 1)) >| rtn)
        (ldr 𝟎
        >> ldc (int (+ 1))
        >> ld 𝟎
        >> sub
        >> ap
        >> ld 𝟎
        >> mul
        >| rtn)
  ) >> ∅
_ = refl
\end{code}\end{minipage}

As a final test, we apply the function \F{fac} to the number 5, compile the
expression, and evaluate it on the SECD,

\noindent\begin{minipage}[]{\textwidth}\begin{code}
_ : runℕ (compile (fac $ #⁺ 5)) 10 ≡ just (+ 120)
_ = refl
\end{code}\end{minipage}

\chapter{Epilogue}
\begin{chapquote}{Jorge Luis Borges, \textit{Selected poems}}
  I walk slowly, like one who comes from so far away he doesn't expect to
  arrive.
\end{chapquote}
We succeeded in formalizing syntax and semantics of a version of the SECD
machine with typed code. We employed Agda as a tool for writing this
formalization, using dependent types to make only well-typed SECD code
representable, and using coinduction to handle the Turing-complete semantics.

As for the practical usability of this implementation, it would be possible to
produce an executable binary file implementing the semantics, as Agda compiles
to Haskell. In addition, there is also an experimental JavaScript compiler.

As a final remark, the author would like to note that the above implementation
of semantics did not require any sort of de-bugging: as soon as the Agda
type-checker was satisfied, all the tests succeeded without any further need of
modification to the semantics. This suggests that dependent types could be a
valuable tool in implementation of safety-critical systems, a direction perhaps
worthy of further pursuit.
\end{document}
