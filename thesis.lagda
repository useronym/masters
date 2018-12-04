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
  nolof    %% This option prints the List of Figures. Replace with
           %% `nolof` to hide the List of Figures.
  %% More options are listed in the user guide at
  %% <http://mirrors.ctan.org/macros/latex/contrib/fithesis/guide/mu/fi.pdf>.
]{fithesis3}

%%\usepackage{fontspec}
%%\usepackage{yfonts}
%%\usepackage{unicode-math}
%%\usepackage{xunicode}
\usepackage[main=english]{babel}

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
    thanks        = {These are the acknowledgements for my thesis, which can

                     span multiple paragraphs.},
    bib           = bibliography.bib
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
\newunicodechar{ℕ}{\ensuremath{\mathnormal\mathbb{N}}}
\newunicodechar{ℤ}{\ensuremath{\mathnormal\mathbb{Z}}}
\newunicodechar{↝}{\ensuremath{\mathnormal\leadsto}}
\newunicodechar{ᵈ}{\ensuremath{^d}}
\newunicodechar{ᶜ}{\ensuremath{^c}}
\newunicodechar{★}{\ensuremath{\mathnormal\star}}
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

\chapter{Intuitionistic logic}
\begin{chapquote}{R. Feynman}
  What I cannot create, I do not understand.
\end{chapquote}
\section{History}
\section{Curry-Howard correspondence}

\chapter{Agda}
\begin{chapquote}{From the topic of the official Agda IRC channel}
  Agda: is it a dependently-typed programming language? Is it a proof-assistant
  based on intuitionistic type theory?

  \verb| ¯\(°_0)/¯| Dunno, lol.
\end{chapquote}
Agda\parencite{norell2007towards} is a functional programming language with
first-class support for dependent types. As per the Curry-Howard correspondence,
well-typed programs in Agda can also be understood as proofs of inhabitance of
their correspoinding types; types being understood as propositions.

This section is meant as a crash-course in Agda syntax, not semantics. In other
words, those not familiar with dependently typed programming languages and/or
proof assistants would do better to follow one of the books published on this
topic. See \parencite{friedman2018little} for an introduction to dependent types
as a whole, or \parencite{stump2016verified} for an in-depth introduction to
dependendly typed programming and theorem proving in Agda.
\section{Overview}
Due to the presence of dependent types, all functions defined must be provably
terminating. Failure to do so would result in type-checking becoming
undecidable. However, this does not mean the loss of Turing-completeness; indeed
we will see in section \ref{coinduction} how possibly non-terminating
computations can still be expressed, with some help from the type system.

Agda has strong support for mixfix operators\footnote{Operators which can have
  multiple name parts and are infix, prefix, postfix, or
  closed\parencite{mixfix}.} and Unicode identifiers. This often allows for
developing a notation close to what one has come to expect in mathematics.
However, with great power comes great responsibility and one should be careful
to not abuse the notation too much, a problem exacerbated by the fact that
operator overloading, as used excessively in mathematics, is not directly
possible.

As an aside, there is also some support for proof automation in
Agda\parencite{auto}, however from the author's experience the usability of this
tool is limited to simple cases. In contrast with tools such as
Coq\parencite{barras1997coq}, Agda suffers from lower degree of automation: there are no
built-in tactics, though their implementation is possible through
reflection\parencite{agda-manual}.
\subsection{Trivial Types}
A type which is trivially inhabited by a single value, This
type is often refered to as \textit{Top} or \textit{Unit}. In Agda,
\begin{code}
data ⊤ : Set where
  ⋅ : ⊤
\end{code}
declares the new data type \AgdaDatatype{⊤} which is itself of type
\AgdaPrimitiveType{Set}\footnote{For the reader familiar with the Haskell type
  system, the Agda type $Set$ is akin to the Haskell kind \textit{Star}. Agda has
  a stratified hierarchy of universes, where $Set$ itself is of the type $Set_1$, and
  so on.}. The second line declared a constructor for this type, here called
simply \AgdaInductiveConstructor{⋅}, which constructs a value of type
\AgdaDatatype{⊤}\footnote{Again for the Haskell-able, note how the syntax here
  resembles that of Haskell with the extension \texttt{GADTs}.}.

The dual of \AgdaDatatype{⊤} is the trivially uninhabited type, often called
\textit{Bottom} or \textit{Empty}. Complete definition in Agda follows.
\begin{code}
data ⊥ : Set where
\end{code}
Note how there are no constructors declared for this type, therefore it is
clearly uninhabited.

The empty type also allows us to define the negation of a proposition,
\begin{code}
¬_ : Set → Set
¬ P = P → ⊥
\end{code}
\subsection{Booleans}
A step-up from the trivially inhabited type \AgdaDatatype{⊤}, the type of
booleans is made up of two distinct values.
\begin{code}
data Bool : Set where
  tt ff : Bool
\end{code}
Since both constructors have the same type signature, we took advantage of a
feature in Agda that allows us to declare such constructors on one line,
together with the shared type.

We can also declare our first function now, one that will perform negation of
Boolean values.
\begin{code}
not : Bool → Bool
not tt = ff
not ff = tt
\end{code}
Here we utilized pattern matching to split on the argument and
flipped one into the other. Note the underscore \texttt{\_} in the name declaration of this
function: it symbolizes where the argument is to be expected and declares it as
a mixfix operator.

Another function we can define is the conjunction of two boolean values, using a
similar approach.
\begin{code}
_∧_ : Bool → Bool → Bool
tt ∧ b = b
ff ∧ _ = ff
\end{code}
\subsection{Products}
To define the product type, it is customary to use a record. This will give us
implicit projection functions from the type.
\begin{code}
record _×_ (A : Set) (B : Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B
infixr 4 _,_
\end{code}
Here we declared a new record type, parametrized by two other types,
\AgdaArgument{A} and \AgdaArgument{B}. These are the types of the values stored
in the pair, which we construct with the operator
\AgdaInductiveConstructor{\_,\_}. We also declare the fixity of this operator to
be right-associative.
\subsection{Natural numbers}
To see a more interesting example of a type, let us consider the type of natural numbers. These can be implemented using Peano encoding, as shown below.
\begin{code}[hide]
module Hidden where
\end{code}
\begin{code}
  data ℕ : Set where
    zero : ℕ
    suc  : ℕ → ℕ
\end{code}
Here we have a nullary constructor for the value zero, and then a unary
constructor which corresponds to the successor function. As an example, consider the
number 3, which would be encoded as~\AgdaInductiveConstructor{suc(suc(suc\
  zero))}.

As an example of a function on the naturals, let us define the addition function.
\begin{code}
  _+_ : ℕ → ℕ → ℕ
  zero + b  = b
  suc a + b = suc (a + b)
\end{code}
We proceed by induction on the left argument: if that number is zero, the result
is simply the right argument. If the left argument is a successor to some number
\AgdaArgument{a}, we inductively perform addition of \AgdaArgument{a} to
\AgdaArgument{b}, and then apply the successor function.
\section{Propositional Equality}
In this section, we will take a short look at one of the main features of
intuitionistic type theory, namely, the identity type. This type allows us to
state the proposition that two values of some data type are \textit{equal}. The
meaning of \textit{equal} here is that both of the values are convertible to the
same value through reductions. This is the concept of propositional equality.
Compare this with definitional equality, which only allows us to express
when two values have the same syntactic representation. For example,
definitionaly it holds that $2=2$, however, $1+1=2$ only holds propositionaly,
because a reduction is required on the left-hand side.

We can define propositional equality in Agda as follows.
\begin{code}
  data _≡_ {A : Set} : A → A → Set where
    refl : {x : A} → x ≡ x
\end{code}
\begin{code}[hide]
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
\end{code}
The curly braces denote an implicit argument, i.e. an argument that is to be
inferred by the type-checker. The equality type is polymorphic in this
underlying type, \AgdaArgument{A}.

The only way we have to construct values of
this type is by the constructor \AgdaInductiveConstructor{refl}, which says that
each value is propositionaly equal to itself. Symmetry and transitivity of
\AgdaDatatype{\_≡\_} are theorems in Agda.
\begin{code}
sym : {A : Set} {a b : A} → a ≡ b → b ≡ a
sym refl = refl

trans : {A : Set} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
trans refl refl = refl
\end{code}
By case splitting on the arguments we force Agda to unify the variables \A{a},
\A{b}, and \A{c}. Afterwards, we can construct the required proof with the
\I{refl} constructor. This is a feature of the underlying type theory of Agda.

Finally, let us see the promised proof of $1+1=2$,
\begin{code}[hide]
module Hidden2 where
  open import Data.Nat using (zero; suc; _+_)
\end{code}
\begin{code}
  1+1≡2 : 1 + 1 ≡ 2
  1+1≡2 = refl
\end{code}
The proof is trivial, as $1+1$ reduces directly to two. A more interesting proof
would be that of associativity of addition,
\begin{code}
  +-assoc : ∀ {a b c} → a + (b + c) ≡ (a + b) + c
  +-assoc {zero}  = refl
  +-assoc {suc a} = let a+[b+c]≡[a+b]+c = +-assoc {a}
                      in ≡-cong suc a+[b+c]≡[a+b]+c
    where ≡-cong : {A B : Set} {a b : A} → (f : A → B) → a ≡ b → f a ≡ f b
          ≡-cong f refl = refl
\end{code}
TODO: If this is to be kept here, explain.
\section{Decidable Equality}
A different concept of equality is that of \textit{Decidable equality}. This is
a form of equality that, unlike Propositional equality, can be decided
programatically. We define this equality as a restriction of propositional
equality to those comparisons which are decidable. Firstly, we will need the
definition of a decidable relation.
\begin{code}
data Dec (R : Set) : Set where
  yes : R → Dec R
  no  : ¬ R → Dec R
\end{code}
This data type allows us to embed either a \I{yes} or a \I{no} answer as to
whether \A{R} is inhabited. Now we can define what it means for a type to
possess Decidable equality,
\begin{code}
Decidable : (A : Set) → Set
Decidable A = ∀ (a b : A) → Dec (a ≡ b)
\end{code}
Here we specify that for any two values of that type we must be able to produce
an answer whether they are equal or not.

As an example, let us define decidable equality for the type of Naturals,
\begin{code}[hide]
open import Data.Nat using (ℕ; zero; suc)
\end{code}
\begin{code}
_≟ℕ_ : Decidable ℕ
zero ≟ℕ zero    = yes refl
(suc _) ≟ℕ zero = no λ()
zero ≟ℕ (suc _) = no λ()
(suc m) ≟ℕ (suc n) with m ≟ℕ n
… | yes refl  = yes refl
… | no ¬m≡n = no λ m≡n → ¬m≡n (suc-injective m≡n)
  where suc-injective : ∀ {m n} → suc m ≡ suc n → m ≡ n
        suc-injective refl = refl
\end{code}
Given a proof of equality of two values of a decidable type, we can forget all
about the proof and simply ask whether the two values are equal or not,
\begin{code}
⌊_⌋ : {A : Set} {a b : A} → Dec (a ≡ b) → Bool
⌊ yes p ⌋ = tt
⌊ no ¬p ⌋ = ff
\end{code}
\begin{code}[hide]
open import Data.Integer using (ℤ)
open import Data.Integer.Properties renaming (_≟_ to _≟ℤ'_)
import Relation.Nullary as N
import Data.Empty as E

_≟B_ : Decidable Bool
tt  ≟B tt = yes refl
ff ≟B ff  = yes refl
tt  ≟B ff = no λ()
ff ≟B tt  = no λ()

_≟ℤ_ : Decidable ℤ
a ≟ℤ b with a ≟ℤ' b
… | N.yes refl = yes refl
… | N.no ¬p = no λ x → ⊥⊥ (¬p x)
  where ⊥⊥ : E.⊥ → ⊥
        ⊥⊥ ()
\end{code}
\section{Formalizing Type Systems}
In what follows, we will take a look at how we can use Agda to formalize
deductive systems. We will take the simplest example there is, the Simply Typed
λ Calculus. Some surface-level knowledge of this calculus is assumed.

For a more in-depth treatment of the topic of formalizing programming languages
and programming language theory in Agda, please refer to
\parencite{wadler2018programming}.

\subsection{De Bruijn Indices}
Firstly, we shall need some machinery to make our lives easier. We could use
string literals as variable names in our system, however this would lead to
certain difficulties further on. Instead, we shall use the concept commonly
referred to as De Bruijn indices\parencite{de1972lambda}. These replace variable
names with natural numbers, where each number $n$ refers to the variable bound
by the binder $n$ positions above the current scope in the syntactical tree. Some
examples of this naming scheme are shown in Figure \ref{debruijn}.
\begin{figure}[h]
  \centering
  \begin{tabular}{ l l }
    \multicolumn{1}{c}{Literal syntax} & \multicolumn{1}{c}{De Bruijn syntax} \\
    \midrule
    \verb|λx.x| & \verb|λ 0| \\
    \verb|λx.λy.x| & \verb|λλ 1| \\
    \verb|λx.λy.λz.x z (y z)| & \verb|λλλ 2 0 (1 0)| \\
    \verb|λf.(λx.f(x x)) (λx.f(x x))| & \verb|λ(λ 1 (0 0)) (λ 1 (0 0))| \\
  \end{tabular}
  \caption{Examples of λ terms using standard naming scheme on the left and
    using De Bruijn indices on the right.}
  \label{debruijn}
\end{figure}
The immediately apparent advantage of using De Bruijn indices is that
α-equivalence of λ terms becomes trivially decidable by way of purely syntactic
equality. Other advantages include easier formalization.
\subsubsection{Implementation}
To implement De Bruijn indices in Agda, we will express what it means for a
variable to be present in a context. We shall assume that a context is a list of
types, as this is how contexts will be defined in the next subsection. We will
express list membership as a new data type,
\begin{code}[hide]
open import Data.List using (List; []; [_]; _∷_; null; map; all; length)
\end{code}
\begin{code}
data _∈_ {A : Set} : A → List A → Set where
  here : ∀ {x xs} → x ∈ (x ∷ xs)
  there : ∀ {x a xs} → x ∈ xs → x ∈ (a ∷ xs)
infix 10 _∈_
\end{code}
The first constructor says that an element is present in a list if that element
is the head of the list. The second constructor says that if we already know
that our element \A{x} is in a list, we can extend the list with some other
element \A{a} and \A{x} will still be present in the new list.

Now we can also define a function which, given a proof that an element is in a
list, returns the aforementioned element.
\begin{code}
lookup : ∀ {A x xs} → x ∈ xs → A
lookup {x = x} here = x
lookup (there w)    = lookup w
\end{code}
We will also define shorthands to construct often-used elements of \D{\_∈\_} for
use in examples later on.
\begin{code}
𝟎 : ∀ {A} {x : A} {xs : List A} → x ∈ (x ∷ xs)
𝟎 = here

𝟏 : ∀ {A} {x y : A} {xs : List A} → x ∈ (y ∷ x ∷ xs)
𝟏 = there here

𝟐 : ∀ {A} {x y z : A} {xs : List A} → x ∈ (z ∷ y ∷ x ∷ xs)
𝟐 = there (there here)
\end{code}
\subsection{Example: Simply Typed λ Calculus}
In this subsection we will, in preparation of the main matter of this thesis,
introduce the way typed deductive systems can be formalized in Agda. As
promised, we will formalize the Simply Typed λ Calculus.
\subsubsection{Syntax}
\label{lambda_syntax}
First, we define the types in our system.
\begin{code}[hide]
module Hidden3 where
\end{code}
\begin{code}
  data ★ : Set where
    ι   : ★
    _⇒_ : ★ → ★ → ★
  infixr 20 _⇒_
\end{code}
Here we defined some atomic type \I{ι} and a binary type constructor for
function types. We proceed by defining context as a list of types.
\begin{code}
  Context : Set
  Context = List ★
\end{code}
Now we are finally able to define the deductive rules that make up the calculus,
using De Bruijn indices as explained above.
\begin{code}
  data _⊢_ : Context → ★ → Set where
    var : ∀ {Γ α}   → α ∈ Γ → Γ ⊢ α
    ƛ_  : ∀ {Γ α β} → α ∷ Γ ⊢ β → Γ ⊢ α ⇒ β
    _$_ : ∀ {Γ α β} → Γ ⊢ α ⇒ β → Γ ⊢ α → Γ ⊢ β
  infix 4 _⊢_
  infixr 5 ƛ_
  infixl 10 _$_
\end{code}
The constructors above should be fairly self-explanatory: they correspond
exactly to the typing rules of the calculus. In the first rule we employed the
data type \D{\_∈\_} implenting De Bruijn indices. Second rule captures the
concept of λ-abstraction, and the last rule is function application.

We can see some examples now,
\begin{code}
  I : ∀ {Γ α} → Γ ⊢ α ⇒ α
  I = ƛ (var 𝟎)

  S : ∀ {Γ α β γ} → Γ ⊢ (α ⇒ β ⇒ γ) ⇒ (α ⇒ β) ⇒ α ⇒ γ
  S = ƛ ƛ ƛ var 𝟐 $ var 𝟎 $ (var 𝟏 $ var 𝟎)
\end{code}
Note how we use Agda polymorphism to construct a polymorphic term of our
calculus; there is no polymorhism in the calculus itself.

The advantage of this presentation is that only well-typed syntax is
representable. Thus, whenever we work with a term of our calculus, it is
guaranteed to be well-typed, which often simplifies things. We will see an
example of this in what follows.
\subsubsection{Semantics by Embedding into Agda}
\label{lambda_semantics}
Now that we have defined the syntax, the next step is to give it semantics. We
will do this in a straightforward manned by way of embedding our calculus into
Agda.

First, we define the semantics of types, by assigning Agda types to types in our calculus.
\begin{code}
  ⟦_⟧★ : ★ → Set
  ⟦ ι ⟧★     = ℕ
  ⟦ α ⇒ β ⟧★ = ⟦ α ⟧★ → ⟦ β ⟧★
\end{code}
Here we choose to realize our atomic type as the type of Natural numbers. These
are chosen for being a nontrivial type. The function type is realized
inductively as an Agda function type.

Next, we give semantics to contexts.
\begin{code}
  ⟦_⟧C : Context → Set
  ⟦ [] ⟧C     = ⊤
  ⟦ x ∷ xs ⟧C = ⟦ x ⟧★ × ⟦ xs ⟧C
\end{code}
The empty context can be realized trivially by the unit type. A non-empty
context is realized as the product of the realization of the first element
and, inductively, a realization of the rest of the context.

Now we are ready to give semantics to terms. In order to be able to proceed by
induction with regard to the structure of the term, we must operate on open terms.
\begin{code}
  ⟦_⟧ : ∀ {Γ α} → Γ ⊢ α → ⟦ Γ ⟧C → ⟦ α ⟧★
\end{code}
The second argument is a realization of the context in the term, which we will
need for variables,
\begin{code}
  ⟦ var here ⟧ (x , _)       = x
  ⟦ var (there x) ⟧ (_ , xs) = ⟦ var x ⟧ xs
\end{code}
Here we case-split on the variable, in case it is zero we take the first element
of the context, otherwise we recurse into the context until we hit zero. Note
that the shape of the context Γ is guaranteed here to never be empty, because the
argument to \I{var} is a proof of membership for Γ. Thus, Agda realizes that Γ
can never be empty and we need not bother ourselves with a case-split for the
empty context; indeed, we would be hard-pressed to give it an implementation.
\begin{code}
  ⟦ ƛ x ⟧ γ                  = λ ⟦α⟧ → ⟦ x ⟧ (⟦α⟧ , γ)
\end{code}
The case for lambda abstraction constructs an Agda function which will take as
the argument a value of the corresponding type and compute the semantics for the
lambda's body, after extending the context with the argument.
\begin{code}
  ⟦ f $ x ⟧ γ                = (⟦ f ⟧ γ) (⟦ x ⟧ γ)
\end{code}
Finally, to give semantics to function application, we simply perform Agda
function application on the subexpressions, after having computed their
semantics in the current context.

Thanks to propositional equality, we can embed tests directly into Agda code and
see whether the terms we defined above receive the expected semantics.
\begin{code}
  Iℕ : ℕ → ℕ
  Iℕ x = x

  _ : ⟦ I ⟧ ⋅ ≡ Iℕ
  _ = refl

  Sℕ : (ℕ → ℕ → ℕ) → (ℕ → ℕ) → ℕ → ℕ
  Sℕ x y z = x z (y z)

  _ : ⟦ S ⟧ ⋅ ≡ Sℕ
  _ = refl
\end{code}
Since this thesis can only be rendered if all the Agda code has successfully
type-checked, the fact that the reader is currently reading this paragraph means
the semantics function as expected!
\section{Coinduction}

\label{coinduction}
\parencite{coinduction}

\begin{code}[hide]
open import Size
open import Data.Maybe using (Maybe; just; nothing)
\end{code}
\begin{code}
mutual
  data Stream (A : Set) (i : Size) : Set where
    []ˢ : Stream A i
    _∷ˢ_ : A → ∞Stream A i → Stream A i

  record ∞Stream (A : Set) (i : Size) : Set where
    coinductive
    field
      force : {j : Size< i} → Stream A j
open ∞Stream public
\end{code}
\begin{code}[hide]
module HiddenX where
  open import Data.Nat using (⌊_/2⌋; _+_; _*_)

  takeˢ : ∀ {A} → ℕ → Stream A ∞ → List A
  takeˢ zero xs           = []
  takeˢ (suc n) []ˢ       = []
  takeˢ (suc n) (x ∷ˢ xs) = x ∷ takeˢ n (force xs)

  even? : ℕ → Bool
  even? zero          = tt
  even? (suc zero)    = ff
  even? (suc (suc n)) = even? n
\end{code}
\begin{code}
  step : ℕ → ℕ
  step n with even? n
  … | tt = ⌊ n /2⌋
  … | ff = 3 * n + 1

  collatz : ℕ → Stream ℕ ∞
  collatz 1 = 1 ∷ˢ λ where .force → []ˢ
  collatz n = n ∷ˢ λ where .force → collatz (step n)
  \end{code}
  \begin{code}
  _ : takeˢ 10 (collatz 12)
      ≡ 12 ∷ 6 ∷ 3 ∷ 10 ∷ 5 ∷ 16 ∷ 8 ∷ 4 ∷ 2 ∷ 1 ∷ []
  _ = refl
\end{code}
\subsection{The Delay Monad}
\begin{code}
mutual
  data Delay (A : Set) (i : Size) : Set where
    now   : A → Delay A i
    later : ∞Delay A i → Delay A i

  record ∞Delay (A : Set) (i : Size) : Set where
    coinductive
    field
      force : {j : Size< i} → Delay A j
open ∞Delay public
\end{code}
\begin{code}
never : ∀ {A} → Delay A ∞
never = later λ where .force → never
\end{code}
\begin{code}
runFor : ∀ {A} → ℕ → Delay A ∞ → Maybe A
runFor zero (now x)      = just x
runFor zero (later _)    = nothing
runFor (suc _) (now x)   = just x
runFor (suc n) (later x) = runFor n (x .force)
\end{code}
\begin{code}
_>>=_ : ∀ {A B i} → Delay A i → (A → Delay B i) → Delay B i
now x >>= f   = f x
later x >>= f = later λ where .force → (x .force) >>= f
\end{code}
\begin{code}[hide]
open import Data.Integer using (+_; _+_; _-_; _*_)
\end{code}

\chapter{SECD Machine}
\begin{chapquote}{Christopher Strachey, discussion following \parencite{landin1966next}, 1966}
  Any language which by mere chance of the way it is written makes it extremely
  difficult to write compositions of functions and very easy to write sequences of
  commands will, of course, in an obvious psychological way, hinder people from
  using descriptive rather than imperative features. In the long run, I think the
  effect will delay our understanding of basic similarities, which underlie
  different sorts of programs and different ways of solving problems.
\end{chapquote}
\section{Introduction}
The \textbf{S}tack, \textbf{E}nvironment, \textbf{C}ontrol, \textbf{D}ump
machine is a stack-based, call-by-value abstract execution machine that was
first outlined by Landin in \parencite{landin1964mechanical}. It was regarded as
an underlying model of execution for a family of languages, specifically,
languages based on the abstract formalism of λ calculus.

Other machines have since been proposed, some derived from SECD, others not.
Notable are the Krivine machine\parencite{krivine2007call}, which implements a
call-by-name semantics, and the ZAM (Zinc abstract machine), which serves as a
backend for the OCaml strict functional programming language
\parencite{leroy1990zinc}.

For an overview of different kinds of SECD machines, including a modern
presentation of the standard call-by-value, and also call-by-name and
call-by-need version of the machine, and a more modern version of the machine
which foregoes the dump in favour of using the stack for the purposes of the
dump, see \parencite{danvy2004rational}.

There have also been hardware implementations of this formalism, e.g.
\parencite{graham1989secd, secdchip}, though it is unclear to the author whether
the issue with verifying the garbage collector mentioned in the latter work was
ever fully addressed.

This chapter is meant as an intuitive overview of the formalism. We will present
the machine with the standard call-by-value semantics.
\section{Definition}
Faithful to its name, the machine is made up of four components:
\begin{itemize}
  \item Stack -- stores values operated on. Atomic operations, such as integer
    addition, are performed here;
  \item Environment -- stores immutable assignments, such as function arguments and
    values bound with the \textit{let} construct;
  \item Control -- stores a list of instructions awaiting execution;
  \item Dump -- serves as a baggage place for storing the current context when a
    function call is performed.
\end{itemize}
Regarding the memory model, all four items defined here are meant to be realized
as linked lists.
\section{Execution}
Execution of the machine consists of reading instructions from the Control and
modifying the state of the machine as necessary. The basic instructions are
\begin{itemize}
  \item \texttt{ld x} –- load the value bound to the identifier \texttt{x} from
    the environment and put it on the stack;
  \item \texttt{ldf f} –- load the function -- i.e. a sequence of instructions --
    \texttt{f} in the current environment, constructing a closure, and put it on the
    stack;
  \item \texttt{ap} –- given that a closure and a value are present on the top
    of the stack, perform function application and put the return value on the
    stack;
  \item \texttt{rtn} –- return from a function, restoring control to the caller.
\end{itemize}
In addition, there are instructions for primitive operations, such as integer
addition, list operations such as the head and tail operations, etc. All these
only transform the stack, e.g. integer addition would consume two integers from
the top of the stack and put back the result.

We use the notation $f[e]$ to mean the closure of function $f$ in the
environment $e$ and $∅$ to mean an empty stack, environment, control, or dump.
The notation $e(x)$ refers to the value in environment $e$ bound under the
identifier $x$.

To see how the basic instructions and the addition instruction transform the
machine state, please refer to Figure \ref{secd}.

To see an example of execution of the machine, please refer to Figure
\ref{secdexample}.

It is usual to use De Bruijn indices when referring to identifiers in the
\texttt{ld} instruction. E.g. \texttt{ld 0} loads the topmost value in the
environment and puts it on the stack. Hence, De Bruijn indices are used in the
example in this chapter. They will also be used in the following chapter in the
Agda formalization.

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
  instruction. On the right is the newly mutated state.}
  \label{secd}
\end{figure}
\begin{figure}[h]
  \centering
  \begin{tabular}{L | L | L | L}
    \toprule
    \multicolumn{1}{c}{S} & \multicolumn{1}{c}{E} & \multicolumn{1}{c}{C} & \multicolumn{1}{c}{D} \\
    \midrule
    ∅       & ∅ & \texttt{ldf f, ldc 1, ap, ldc 3, add} & ∅                         \\
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

\chapter{Formalization}
In this chapter, we approach the main topic of this thesis. We will formalize a
SECD machine in Agda, with typed syntax, and then proceed to define the
semantics by way of coinduction. Finally, we will define a typed λ calculus,
corresponding exactly to the capabilities of the SECD machine, and define a
compilation procedure from this calculus to typed SECD programs.

\section{Syntax}
\subsection{Preliminaries}
Before we can proceed, we shall require certain machinery to aid us in
formalizing the type system.

We define the data type \AgdaDatatype{Path}, parametrized by a binary relation,
whose values are finite sequences of values such that each value is in relation
with the next.
\begin{code}
data Path {A : Set} (R : A → A → Set) : A → A → Set where
  ∅    : ∀ {a} → Path R a a
  _>>_ : ∀ {a b c} → R a b → Path R b c → Path R a c
infixr 5 _>>_
\end{code}
The first constructor creates an empty path. The second takes an
already-existing path and prepends to it a value, given a proof that this value
is in relation with the first element of the already-existing path. The reader
may notice a certain similarity to linked lists; indeed if for the relation we
take the universal one for our data type \AgdaDatatype{A}, we stand to obtain a
type that's isomorphic to linked lists.

We can view this type as the type of finite paths through a graph connected
according to the binary relation.

We also define a shorthand for constructing the end of a path out of two edges.
We will use this in examples later on.
\begin{code}
_>|_ : ∀ {A R} {a b c : A} → R a b → R b c → Path R a c
a >| b = a >> b >> ∅
\end{code}
Furthermore, we can also concatenate two paths, given that the end of the first
path connects to the start of the second one.
\begin{code}
_>+>_ : ∀ {A R} {a b c : A} → Path R a b → Path R b c → Path R a c
∅        >+> r = r
(x >> l) >+> r = x >> (l >+> r)
infixr 4 _>+>_
\end{code}
\subsection{Machine types}
\label{secd_types}
We start by defining the atomic constants our machine will recognize. We will
limit ourselves to booleans and integers.
\begin{code}
data Const : Set where
  bool : Bool → Const
  int : ℤ → Const
\end{code}
Next, we define which types our machine recognizes.
\begin{code}
data Type : Set where
  intT boolT : Type
  pairT : Type → Type → Type
  listT : Type → Type
  _⇒_ : Type → Type → Type
infixr 15 _⇒_
\end{code}
Firstly, there are types corresponding to the constants we have already defined
above. Then, we also introduce a product type and a list type. Finally, there is
the function type, \AgdaInductiveConstructor{\_⇒\_}, in infix notation.

Now we define the type assignment of constants.
\begin{code}
typeof : Const → Type
typeof (bool _) = boolT
typeof (int _)  = intT
\end{code}
Next, we define the typed stack, environment, and function dump.
\begin{code}
Stack   = List Type
Env     = List Type
FunDump = List Type
\end{code}
For now, these only store the information regarding the types of the values in
the machine. Later, when defining semantics, we will give realizations to these,
similarly to how we handled contexts in the formalization of Simply Typed λ
Calculus in ?.

Finally, we define the state as a record storing the stack, environment, and the
function dump.
\begin{code}
record State : Set where
  constructor _#_#_
  field
    s : Stack
    e : Env
    f : FunDump
\end{code}
Note that, unlike in the standard presentation of SECD Machines which we saw in
chapter ?, here the state does not include the code. This is because we are
aiming for a version of SECD with typed assembly code. We will define code next
\subsection{Typing relation}
Since we aim to have typed assembly, we have to take a different approach to
defining code. We will define a binary relation which will determine how a state of
a certain shape is mutated following the execution of an instruction.

We will have two versions of this relation: first one is the single-step
relation, the second one is the transitive closure of the first one using
\D{Path}.
\begin{code}
infix 5 ⊢_⊳_
infix 5 ⊢_↝_
\end{code}
Their definitions need to be mutually recursive, because certain instructions —
defined in the single-step relation — need to refer to whole programs, a concept
captured by the multi-step relation.
\begin{code}
mutual
  ⊢_↝_ : State → State → Set
  ⊢ s₁ ↝ s₂ = Path ⊢_⊳_ s₁ s₂
\end{code}
Here there is nothing surprising, we use \D{Path} to define the multi-step
relation.

Next, we define the single-step relation. As mentioned before, this relation
captures how one state might change into another.
\begin{code}
  data ⊢_⊳_ : State → State → Set where
\end{code}
Here we must define all the instructions our machine should handle. We will start
with the simpler ones.
\begin{code}
    ldc  : ∀ {s e f}
         → (const : Const)
         → ⊢ s # e # f ⊳ (typeof const ∷ s) # e # f
\end{code}
Instruction \I{ldc} loads a constant which is embedded in it. It poses no
restrictions on the state of the machine and mutates the state by pushing the
constant on the stack.
\begin{code}
    ld   : ∀ {s e f a}
         → (a ∈ e)
         → ⊢ s # e # f ⊳ (a ∷ s) # e # f
\end{code}
Instruction \I{ld} loads a value of type \A{a} from the environment and puts it
on the stack. It requires a proof that this value is, indeed, in the
environment.
\begin{code}
    ldf  : ∀ {s e f a b}
         → (⊢ [] # (a ∷ e) # (a ⇒ b ∷ f) ↝ [ b ] # (a ∷ e) # (a ⇒ b ∷ f))
         → ⊢ s # e # f ⊳ (a ⇒ b ∷ s) # e # f
\end{code}
The \I{ldf} instruction is considerably more involved. It loads a function of
the type \A{a} \I{⇒} \A{b} and puts it on the stack. Note how we use the multi-step
relation here. In addition, the code we are loading also has to be of a certain
shape to make it a function: the argument it was called with must be put in the
environment, and the function dump is to be extended with the type of the
function to permit recursive calls to itself.

Once a function is loaded, we may apply it,
\begin{code}
    ap   : ∀ {s e f a b}
         → ⊢ (a ∷ a ⇒ b ∷ s) # e # f ⊳ (b ∷ s) # e # f
\end{code}
\I{ap} requires that a function and its argument are on the stack. After it has
run, the returning value from the function will be put on the stack in their
stead. The type of this instruction is fairly simple; the difficult part awaits
us further on in implementation.
\begin{code}
    rtn  : ∀ {s e a b f}
         → ⊢ (b ∷ s) # e # (a ⇒ b ∷ f) ⊳ [ b ] # e # (a ⇒ b ∷ f)
\end{code}
Return is an instruction we are to use at the end of a function in order to get
the machine state into the one required by \I{ldf}. It throws away what is on
the stack, with the exception of the return value.

Next, let us look at recursive calls.
\begin{code}
    ldr  : ∀ {s e f a b}
         → (a ⇒ b ∈ f)
         → ⊢ s # e # f ⊳ (a ⇒ b ∷ s) # e # f
\end{code}
\I{ldr} loads a function for recursive application from the function dump. We
can be many scopes deep in the function and we use a De Bruijn index here to
count the scopes, same as we do with the environment. This is important e.g. for
curried functions where we want to be able to load the topmost function, not one that
was already partially applied.
\begin{code}
    rap  : ∀ {s e f a b}
         → ⊢ (a ∷ a ⇒ b ∷ s) # e # f ⊳ [ b ] # e # f
\end{code}
This instruction looks exactly the same way as \I{ap}. The difference will be in
implementation, as this one will attempt to perform tail call elimination.
\begin{code}
    if   : ∀ {s s' e f}
         → ⊢ s # e # f ↝ s' # e # f
         → ⊢ s # e # f ↝ s' # e # f
         → ⊢ (boolT ∷ s) # e # f ⊳ s' # e # f
\end{code}
The if instruction requires that a boolean value be present on the stack. Based
on this, it decides which branch to execute. Here we hit on one limitation of
the typed presentation: both branches must finish with a stack of the same
shape, otherwise it would be unclear what the stack looks like after this
instruction.

The remaining instructions are fairly simple in that they only manipulate the
stack. Their types are outlined in Figure \ref{instypes}.
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
    types, i.e. their manipulations of the stack.}
  \label{instypes}
\end{figure}
\begin{code}[hide]
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
\end{code}
\subsubsection{Derived instructions}
For the sake of sanity we will also define what amounts to simple programs,
masquerading as instructions, for use in more complex programs later. The chief
limitation here is that since these are members of the multi-step relation, we
have to be mindful when using them and use concatenation of paths, \F{\_>+>\_}, as
necessary.
\begin{code}
nil? : ∀ {s e f a} → ⊢ (listT a ∷ s) # e # f ↝ (boolT ∷ s) # e # f
nil? = nil >| eq?

loadList : ∀ {s e f} → List ℕ → ⊢ s # e # f ↝ (listT intT ∷ s) # e # f
loadList [] = nil >> ∅
loadList (x ∷ xs) = loadList xs >+> ldc (int (+ x)) >| cons
\end{code}
The first one is simply the check for an empty list. The second one is more
interesting, it constructs a sequence of instructions which will load a list of
natural numbers.
\subsection{Examples}
\label{syntax_tests}
In this section we present some examples of SECD programs in our current
formalism. Starting with trivial ones, we will work our way up to using full
capabilities of the machine.

The first example loads two constants and adds them.
\begin{code}
2+3 : ⊢ [] # [] # [] ↝ [ intT ] # [] # []
2+3 =
    ldc (int (+ 2))
 >> ldc (int (+ 3))
 >| add
\end{code}
The second example constructs a function which expects an integer and increases
it by one before returning it.
\begin{code}
inc : ∀ {e f} → ⊢ [] # (intT ∷ e) # (intT ⇒ intT ∷ f)
                ↝ [ intT ] # (intT ∷ e) # (intT ⇒ intT ∷ f)
inc =
    ld 𝟎
 >> ldc (int (+ 1))
 >> add
 >| rtn
\end{code}
Here we can see the type of the expression getting more complicated: we use
polymorphism to make make sure we can load this function in any environment, in
the environment we have to declare that an argument of type \I{intT} is
expected, and lastly the function dump has to be expanded with the type of this
function.

In the next example we load the above function and apply it to the integer 2.
\begin{code}
inc2 : ⊢ [] # [] # [] ↝ [ intT ] # [] # []
inc2 =
    ldf inc
 >> ldc (int (+ 2))
 >| ap
\end{code}
In the next example we test partial application.
\begin{code}
λTest : ⊢ [] # [] # [] ↝ [ intT ] # [] # []
λTest =
     ldf
       (ldf
         (ld 𝟎 >> ld 𝟏 >> add >| rtn) >| rtn)
  >> ldc (int (+ 1))
  >> ap
  >> ldc (int (+ 2))
  >| ap
\end{code}
First we construct a function which constructs a function which adds the two
values in the environment. The types of these two are inferred to be integers by
Agda, as this is what the \I{add} instruction requires. Then, we load an apply
the constant 1. This results in another function, partially applied. Lastly, we
load 2 and apply.

In the example \F{inc} we saw how we could define a function. In the next
example we also construct a function, however this time we embed the instruction
\I{ldf} in our definition directly, as this simplifies the type considerably.
\begin{code}
plus : ∀ {s e f} → ⊢ s # e # f ⊳ ((intT ⇒ intT ⇒ intT) ∷ s) # e # f
plus = ldf (ldf (ld 𝟎 >> ld 𝟏 >> add >| rtn) >| rtn)
\end{code}
The only consideration is that when we wish to use this function in another
program, rather than writing \I{ldf} \F{plus} we must only write \F{plus}.

Lastly, a more involved example: that of a folding function. Here we test all
capabilities of the machine.
\begin{code}
foldl : ∀ {e f a b} → ⊢ [] # e # f
                      ⊳ [ ((b ⇒ a ⇒ b) ⇒ b ⇒ (listT a) ⇒ b) ] # e # f
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
\end{code}
Here is what's going on: to start, we load the list we are folding. We check
whether it is empty: if so, the accumulator \F{𝟏} is loaded and returned. On the other
hand, if the list is not empty, we start with loading the folding function \F{𝟐}.
Next, we load the accumulator \F{𝟏}. We perform partial application. Next, we
load the list \F{𝟎} and obtain it's first element with \I{head}. We apply to the
already partially-applied folding function, yielding the new accumulator on the
top of the stack.

Now we need to make the recursive call: we load ourselves with \I{ldr} \F{𝟐}.
Next we need to apply all three arguments: we start with loading the folding
function \F{𝟐} and applying it. We are now in a state where the partially
applied foldl is on the top of the stack and the new accumulator is right below
it; we flip\footnote{Note we could have reorganized the instructions in a manner
  so that this flip would not be necessary, indeed we will see that there is no
  need for this instruction in section \ref{compilation}} the two and apply.
Lastly, we load the list \F{𝟎}, drop the first element with \I{tail} and perform
recursive application with tail-call elimination.
\section{Semantics}
Having defined the syntax, we can now turn to semantics. In this section, we
will give operational semantics to the SECD machine syntax defined in the
previous section.

\subsection{Types}
We begin, similarly to how we handled the semantics in \ref{lambda_semantics},
by first giving semantics to the types. Here we have to proceed by mutual
induction, as in certain places we will need to make references to the semantics
of other types, and vice versa. The order of the following definitions is
arbitrary from the point of view of correctness and was chosen purely for
improving readability.

We start by giving semantics to the types of our machine,
\begin{code}
mutual
  ⟦_⟧ᵗ : Type → Set
  ⟦ intT ⟧ᵗ        = ℤ
  ⟦ boolT ⟧ᵗ       = Bool
  ⟦ pairT t₁ t₂ ⟧ᵗ = ⟦ t₁ ⟧ᵗ × ⟦ t₂ ⟧ᵗ
  ⟦ a ⇒ b ⟧ᵗ       = Closure a b
  ⟦ listT t ⟧ᵗ     = List ⟦ t ⟧ᵗ
\end{code}
Here we realized the machine types as the corresponding types in Agda. The
exception is the type of functions, which we realize as a closure. The meaning
of \D{Closure} will be defined at a later moment.

We proceed by giving semantics to the environment,
\begin{code}
  ⟦_⟧ᵉ : Env → Set
  ⟦ [] ⟧ᵉ     = ⊤
  ⟦ x ∷ xs ⟧ᵉ = ⟦ x ⟧ᵗ × ⟦ xs ⟧ᵉ
\end{code}
The semantics of environment are fairly straightforward, we make a reference to
the semantic function for types and inductively define the environment as a
product of semantics of each type in it.

Next, we define the semantics of the function dump,
\begin{code}
  ⟦_⟧ᵈ : FunDump → Set
  ⟦ [] ⟧ᵈ              = ⊤
  ⟦ intT ∷ xs ⟧ᵈ       = ⊥
  ⟦ boolT ∷ xs ⟧ᵈ      = ⊥
  ⟦ pairT x x₁ ∷ xs ⟧ᵈ = ⊥
  ⟦ a ⇒ b ∷ xs ⟧ᵈ      = Closure a b × ⟦ xs ⟧ᵈ
  ⟦ listT x ∷ xs ⟧ᵈ    = ⊥
\end{code}
Since the type of the function dump technically permits also non-function types
in it, we have to handle them here by simply saying that they may not be
realized. There is, however, no instruction which would allow putting a
non-function type in the dump.

Now finally for the definition of \D{Closure}, we define it as a record
containing the code of the function, a realization of the starting environment,
and finally a realization of the function dump, containing closures which may be
called recursively from this closure.
\begin{code}
  record Closure (a b : Type) : Set where
    inductive
    constructor ⟦_⟧ᶜ×⟦_⟧ᵉ×⟦_⟧ᵈ
    field
      {e} : Env
      {f} : FunDump
      ⟦c⟧ᶜ : ⊢ [] # (a ∷ e) # (a ⇒ b ∷ f)
             ↝ [ b ] # (a ∷ e) # (a ⇒ b ∷ f)
      ⟦e⟧ᵉ : ⟦ e ⟧ᵉ
      ⟦f⟧ᵈ : ⟦ f ⟧ᵈ
\end{code}
This concludes the mutual block of definitions.

There is one more type we have not handled yet, \D{Stack}, which is not required
to be in the mutual block above,
\begin{code}
⟦_⟧ˢ : Stack → Set
⟦ [] ⟧ˢ     = ⊤
⟦ x ∷ xs ⟧ˢ = ⟦ x ⟧ᵗ × ⟦ xs ⟧ˢ
\end{code}
The stack is realized similarly to the environment, however the environment is
referenced in the definition of \D{Closure}, making it necessary for it to be in
the mutual definition block.

\subsection{Auxiliary functions}
In order to proceed with giving semantics to SECD execution, we will first need
a few auxiliary functions to lookup values from the environment and from the
function dump.

As for the environment, the situation is fairly simple,
\begin{code}
lookupᵉ : ∀ {x xs} → ⟦ xs ⟧ᵉ → x ∈ xs → ⟦ x ⟧ᵗ
lookupᵉ (x , _) here       = x
lookupᵉ (_ , xs) (there w) = lookupᵉ xs w
\end{code}
Looking up values from the function dump is slightly more involved, because Agda
doesn't let us pattern-match on the first argument as we did here. Instead, we
must define an auxiliary function to drop the first element of the product,
\begin{code}
tailᵈ : ∀ {x xs} → ⟦ x ∷ xs ⟧ᵈ → ⟦ xs ⟧ᵈ
tailᵈ {intT} ()
tailᵈ {boolT} ()
tailᵈ {pairT x x₁} ()
tailᵈ {a ⇒ b} (_ , xs) = xs
tailᵈ {listT x} ()
\end{code}
We pattern-match on the type of the value in the environment in order to get
Agda to realize that only a realization of a function may be in the function
dump, at which point we can pattern-match on the product that is the function
dump and drop the first element.

Now we can define the lookup operation for the function dump,
\begin{code}
lookupᵈ : ∀ {a b f} → ⟦ f ⟧ᵈ → a ⇒ b ∈ f → Closure a b
lookupᵈ (x , _) here = x
lookupᵈ f (there w)  = lookupᵈ (tailᵈ f) w
\end{code}
dropping the elements as necessary with \F{tailᵈ} until we get to the desired
closure.

\subsection{Execution}
Now we are finally ready to define the execution of instructions. Let us start
with the type,
\begin{code}
run : ∀ {s s' e e' f f' i} → ⟦ s ⟧ˢ → ⟦ e ⟧ᵉ → ⟦ f ⟧ᵈ
                           → ⊢ s # e # f ↝ s' # e' # f'
                           → Delay ⟦ s' ⟧ˢ i
\end{code}
Here we say that in order to execute the code
\[
  \D {⊢}\ s\ \I{\#}\ e\ \I{\#}\ f\ \D{↝}\ s'\ \I{\#}\ e'\ \I{\#}\ f'
\]
we require realizations of the stack \A{s}, environment \A{e}, and function dump
\A{f}. We will return the stack the code stops execution in, wrapped in the
\D{Delay} monad in order to allow for non-structurally inductive calls that will
be necessary in some cases.

We proceed by structural induction on the last argument, i.e. the code. We start
with the empty run,
\begin{code}
run s e d ∅ = now s
\end{code}
In the case of an empty run, it holds that $s = s'$ and so we simply finish the
execution, returning the current stack.

Next we consider all the cases when the run is not empty. We start with the
instruction \I{ldf},
\begin{code}
run s e d (ldf code >> r) =
  run (⟦ code ⟧ᶜ×⟦ e ⟧ᵉ×⟦ d ⟧ᵈ , s) e d r
\end{code}
Recall that this instruction is supposed to load a function. Since the
semantical meaning of a function is a closure, this is what we must construct.
We do so out of the code, given as an argument to \I{ldf}, and the current
environment and function dump. We put this closure on the stack and proceed with
execution of the rest of the run.
\begin{code}
run s e d (ld at >> r) = run (lookupᵉ e at , s) e d r
\end{code}
This instruction loads a value from the environment with the help of the
auxiliary function \F{lookupᵉ} and puts it on the stack.
\begin{code}
run s e d (ldc const >> r) = run (makeConst const , s) e d r
  where makeConst : (c : Const) → ⟦ typeof c ⟧ᵗ
        makeConst (bool x) = x
        makeConst (int x) = x
\end{code}
In order to load a constant we introduce an auxiliary conversion function for
converting from an embedded constant to a semantical value. The constant is then
put on the stack.
\begin{code}
run s e d (ldr at >> r) =
  run (lookupᵈ d at , s) e d r
\end{code}
This instruction loads a closure from the function dump and puts it on the
stack. Similarly to \I{ld}, we use an auxiliary function, in this case
\F{lookupᵈ}.

Next we handle the instruction for function application,
\begin{code}
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
\end{code}
Here we have to employ coinduction for the first time, as we need to perform a
call to \F{run} which is not structurally recursive. This call is used to
evaluate the closure from the empty stack \I{⋅} in environment \A{fE} extended
with the function argument \A{a}. The function dump also needs to be extended
with the closure being evaluated in order to allow recursive calls. Once the
call to \F{run} has returned, we grab the first item on the stack \A{b} and
resume execution of the rest of the run \A{r} with \A{b} put on the stack.

We will now handle recursive tail calls, i.e. the instruction \I{rap}. We need
to make an additional case split here on the rest of the run \A{r}, as a tail
call can really only occur if \I{rap} is the last instruction in the current
run. However, there is no syntactic restriction which would prevent more
instructions to follow a \I{rap}.
\begin{code}
run (a , ⟦ code ⟧ᶜ×⟦ fE ⟧ᵉ×⟦ dump ⟧ᵈ , s) e d (rap >> ∅) =
  later
    λ where
      .force →
        run ⋅ (a , fE) (⟦ code ⟧ᶜ×⟦ fE ⟧ᵉ×⟦ dump ⟧ᵈ , dump) code
\end{code}
Above is the case when we can perform the tail call. In this case, the types
align: recall that in the type signature of \F{run} we promised to return a
stack of the type \A{s'}. Here, as \I{rap} is the last instruction, this means a
stack containing a single item of some type \A{β}. This is exactly what the
closure on the stack constructs. Hence, we can shift execution to the closure.

If there are more instructions after \I{rap}, we are not so lucky: here we don't
know what \A{s'} is, and we have but one way to obtain a stack of this type:
proceed with evaluating rest of the run \A{r}. As such, we are unable to perform
a tail call. Instead, we convert \I{rap} to \I{ap}, thus performing standard
function application.
\begin{code}
run (a , ⟦ code ⟧ᶜ×⟦ fE ⟧ᵉ×⟦ dump ⟧ᵈ , s) e d (rap >> r) =
  later
    λ where
      .force →
        run (a , ⟦ code ⟧ᶜ×⟦ fE ⟧ᵉ×⟦ dump ⟧ᵈ , ⋅) e d (ap >> r)
\end{code}
Next we have the \I{rtn} instruction which simply drops all items from the stack
but the topmost one. Once again, we have no guarantee that there are no more
instructions after \I{rtn}, hence we make a recursive call to \F{run}. Under
normal circumstances, \A{r} is the empty run \I{∅} and execution returns.      
\begin{code}
run (b , _) e d (rtn >> r) = run (b , ⋅) e d r
\end{code}
The \I{if} instruction follows,
\begin{code}
run (test , s) e d (if c₁ c₂ >> r) with test
… | tt = later λ where .force → run s e d (c₁ >+> r)
… | ff = later λ where .force → run s e d (c₂ >+> r)
\end{code}
This instruction examines the boolean value on top of the stack and prepends the
correct branch to \A{r}.

The instructions that remain are those implementing primitive operations which
only manipulate the stack. We include them here for completeness' sake.
\begin{code}
run s e d (nil >> r)             = run ([] , s) e d r
run (x , y , s) e d (flp >> r)   = run (y , x , s) e d r
run (x , xs , s) e d (cons >> r) = run (x ∷ xs , s) e d r
run ([] , s) e d (head >> r)     = never
run (x ∷ _ , s) e d (head >> r)  = run (x , s) e d r
run ([] , s) e d (tail >> r)     = never
run (_ ∷ xs , s) e d (tail >> r) = run (xs , s) e d r
run (x , y , s) e d (pair >> r)  = run ((x , y) , s) e d r
run ((x , _) , s) e d (fst >> r) = run (x , s) e d r
run ((_ , y) , s) e d (snd >> r) = run (y , s) e d r
run (x , y , s) e d (add >> r)   = run (x + y , s) e d r
run (x , y , s) e d (sub >> r)   = run (x - y , s) e d r
run (x , y , s) e d (mul >> r)   = run (x * y , s) e d r
run (a , b , s) e d (eq? >> r)   = run (compare a b , s) e d r
  where compare : {t : Type} → ⟦ t ⟧ᵗ → ⟦ t ⟧ᵗ → ⟦ boolT ⟧ᵗ
        compare {intT} a b  = ⌊ a ≟ℤ b ⌋
        compare {boolT} a b = ⌊ a ≟B b ⌋
        compare {pairT _ _} (a₁ , a₂) (b₁ , b₂) =
          (compare a₁ b₁) ∧ (compare a₂ b₂)
        compare {listT xs}  a b = ⌊ length a ≟ℕ length b ⌋ -- TDO
        compare {_ ⇒ _} _ _     = ff
run (x , s) e d (nt >> r)       = run (not x , s) e d r
\end{code}
The only interesting cases here are \I{head} and \I{tail} when called on an
empty list. In this case, we signal an error by terminating the execution,
returning instead an infinitely delayed value.

\subsubsection{Tests}
Being done with the trickiest part, we now define an auxiliary function for use
in tests. It takes some code which starts from an empty initial state and another
argument, which signifies an upper bound on the number of indirections that may
be encountered during execution. If this bound is exceeded, \I{nothing} is returned.
\begin{code}
runℕ : ∀ {x s} → ⊢ [] # [] # [] ↝ (x ∷ s) # [] # []
               → ℕ
               → Maybe ⟦ x ⟧ᵗ
runℕ c n = runFor n
  do
    (x , _) ← run ⋅ ⋅ ⋅ c
    now x
\end{code}
Now for the promised tests, we will evaluate the examples from \ref{syntax_tests}.
\begin{code}
_ : runℕ 2+3 0 ≡ just (+ 5)
_ = refl

_ : runℕ inc2 1 ≡ just (+ 3)
_ = refl

_ : runℕ λTest 2 ≡ just (+ 3)
_ = refl
\end{code}
So far so good! Now for something more complicated, we will \F{foldl} the list
$[1,2,3,4]$ with \F{plus}. Below we have the code to achieve this,
\begin{code}
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
\end{code}
And indeed,
\begin{code}
_ : runℕ foldTest 28 ≡ just (+ 10)
_ = refl
\end{code}
\section{Compilation from a higher-level language}
\label{compilation}
As a final step, we will define a typed (though inconsistent) λ calculus and
implement compilation to typed SECD instructions from previous sections.

We will reuse the types defined in Section \ref{secd_types}, which will not only
make compilation cleaner, but also makes sense from a moral standpoint, as we
want our λ calculus to model the capabilities of our SECD machine. Hence, a
context is a list of (SECD) types,
\begin{code}
Ctx = List Type
\end{code}
As for the typing relation, we use a similar trick as with SECD to allow
recursive calls. We keep two contexts, \A{Γ} for tracking assumptions, as in
\ref{lambda_syntax}, and \A{Ψ} for tracking types of functions we can call
recursively.
\begin{code}
infix 2 _×_⊢_
data _×_⊢_ : Ctx → Ctx → Type → Set where
  var : ∀ {Ψ Γ x} → x ∈ Γ → Ψ × Γ ⊢ x
  ƛ_  : ∀ {Ψ Γ α β} → (α ⇒ β ∷ Ψ) × α ∷ Γ ⊢ β → Ψ × Γ ⊢ α ⇒ β
  _$_ : ∀ {Ψ Γ α β} → Ψ × Γ ⊢ α ⇒ β → Ψ × Γ ⊢ α → Ψ × Γ ⊢ β
\end{code}
The first three typing rules model closely the ones from \ref{lambda_syntax},
with the addition of the function context \A{Ψ}.

Next, we have a variation of \I{var} for loading functions from \A{Ψ},
\begin{code}
  rec : ∀ {Ψ Γ α β} → (α ⇒ β) ∈ Ψ → Ψ × Γ ⊢ α ⇒ β
\end{code}
We also have an if-then-else construct and a polymorphic comparison operator,
\begin{code}
  if_then_else_ : ∀ {Ψ Γ α} → Ψ × Γ ⊢ boolT
                            → Ψ × Γ ⊢ α → Ψ × Γ ⊢ α
                            → Ψ × Γ ⊢ α
  _==_ : ∀ {Ψ Γ α} → Ψ × Γ ⊢ α → Ψ × Γ ⊢ α → Ψ × Γ ⊢ boolT
\end{code}
Finally, we have the integers and some primitive operations on them,
\begin{code}
  #_ : ∀ {Ψ Γ} → ℤ → Ψ × Γ ⊢ intT
  mul : ∀ {Ψ Γ} → Ψ × Γ ⊢ intT ⇒ intT ⇒ intT
  sub : ∀ {Ψ Γ} → Ψ × Γ ⊢ intT ⇒ intT ⇒ intT

infixr 2 ƛ_
infixl 3 _$_
infix 5 _==_

#⁺_ : ∀ {Ψ Γ} → ℕ → Ψ × Γ ⊢ intT
#⁺ n = # (+ n)
\end{code}
As an example, consider the factorial function in this formalism,
\begin{code}
fac : [] × [] ⊢ (intT ⇒ intT)
fac = ƛ if (var 𝟎 == #⁺ 1)
          then #⁺ 1
          else (mul $ (rec 𝟎 $ (sub $ var 𝟎 $ #⁺ 1))
                    $ var 𝟎)
\end{code}
For the compilation, we use a scheme of two mutually recursive functions
adapted from \parencite{modernsecd}. The first function, \F{compileT}, is used
to compile expressions in the tail position, whereas \F{compile} is used for the
other cases.
\begin{code}
mutual
  compileT : ∀ {Ψ Γ α β} → (α ⇒ β ∷ Ψ) × (α ∷ Γ) ⊢ β
                         → ⊢ [] # (α ∷ Γ) # (α ⇒ β ∷ Ψ)
                           ↝ [ β ] # (α ∷ Γ) # (α ⇒ β ∷ Ψ)
  compileT (f $ x) =
    compile f >+> compile x >+> rap >> ∅
  compileT (if t then a else b) =
    compile t >+> if (compileT a) (compileT b) >> ∅
  compileT t = compile t >+> rtn >> ∅

  compile : ∀ {Ψ Γ α s} → Ψ × Γ ⊢ α
                        → ⊢ s # Γ # Ψ ↝ (α ∷ s) # Γ # Ψ
  compile (var x)              = ld x >> ∅
  compile (ƛ t)                = ldf (compileT t) >> ∅
  compile (f $ x)              = compile f >+> compile x >+> ap >> ∅
  compile (rec x)              = ldr x >> ∅
  compile (if t then a else b) =
    compile t >+> if (compile a) (compile b) >> ∅
  compile (a == b)             = compile b >+> compile a >+> eq? >> ∅
  compile (# x)                = ldc (int x) >> ∅
  compile mul                  = ldf (ldf (ld 𝟎 >> ld 𝟏 >| mul) >| rtn) >> ∅
  compile sub                  = ldf (ldf (ld 𝟎 >> ld 𝟏 >| sub) >| rtn) >> ∅
\end{code}
As a final test, we can apply the function \F{fac} to the number 5, compile the
expression, and evaluate it on the SECD,
\begin{code}
_ : runℕ (compile (fac $ #⁺ 5)) 27 ≡ just (+ 120)
_ = refl
\end{code}

\chapter{Epilogue}

\end{document}
