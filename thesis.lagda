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
    advisor       = {prof. RNDr. Luboš Brim, CSc.},
    title         = {Distributed-memory model checker for Hybrid LTL},
    TeXtitle      = {Distributed-memory model checker for Hybrid LTL},
    keywords      = {hybrid, LTL, model, checker, distributed, Haskell},
    TeXkeywords   = {hybrid, LTL, model, checker, distributed, Haskell},
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
\newunicodechar{ℕ}{\ensuremath{\mathnormal\mathbb{N}}}
\newunicodechar{ℤ}{\ensuremath{\mathnormal\mathbb{Z}}}
\newunicodechar{↝}{\ensuremath{\mathnormal\leadsto}}
\newunicodechar{ᵈ}{\ensuremath{^d}}
\newunicodechar{ᶜ}{\ensuremath{^c}}
\newcommand{\A}{\AgdaArgument}
\newcommand{\D}{\AgdaDatatype}
\newcommand{\I}{\AgdaInductiveConstructor}

\makeatletter
\renewcommand{\@chapapp}{}% Not necessary...
\newenvironment{chapquote}[2][2em]
  {\setlength{\@tempdima}{#1}%
   \def\chapquote@author{#2}%
   \parshape 1 \@tempdima \dimexpr\textwidth-2\@tempdima\relax%
   \itshape}
  {\par\normalfont\hfill---\ \chapquote@author\hspace*{\@tempdima}\par\bigskip}
\makeatother

\begin{document}
\chapter{Introduction}

\chapter{Intuitionistic logic}
\begin{chapquote}{R. Feynman}
  What I cannot create, I do not understand.
\end{chapquote}

\chapter{Agda}
\begin{chapquote}{From the topic of the official Agda IRC channel}
  Agda: is it a dependently-typed programming language? Is it a proof-assistant
  based on intuitionistic type theory?

  \verb|¯\(°_0)/¯| Dunno, lol.
\end{chapquote}
Agda\parencite{norell2007towards} is a
\section{Basics}
In this section, we present a few simple types in order to get accustomed to the
syntax of Agda by way of example.
\subsection{Trivial Types}
The simples type is a type which is trivially inhabited by a single value. This
type is often refered to as \textit{Top} or \textit{Unit}. In Agda,
\begin{code}
data ⊤ : Set where
  ⋅ : ⊤
\end{code}
declares the new data type \AgdaDatatype{⊤} which is itself of type
\AgdaPrimitiveType{Set}\footnote{For the reader familiar with the Haskell type
  system, the Agda type Set is akin to the Haskell kind \textit{Star}.}. The
second line declared a constructor for this type, here called simply
\AgdaInductiveConstructor{⋅}, which constructs a value of type
\AgdaDatatype{⊤}\footnote{Again for the Haskell-able, note how the syntax here
  resembles that of Haskell with the extension \texttt{GADTs}.}.

The dual of \AgdaDatatype{⊤} is the trivially uninhabited type, often called
\textit{Bottom} or \textit{Empty}. Complete definition in Agda follows.
\begin{code}
data ⊥ : Set where
\end{code}
Note how there are no constructors declared for this type, therefore it is
clearly uninhabited.
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
¬_ : Bool → Bool
¬ tt = ff
¬ ff = tt
\end{code}
Here we utilized pattern matching to split on the argument and
flipped one into the other. Note the underscore \texttt{\_} in the name declaration of this
function: it symbolizes where the argument is to be
expected. Agda has a strong support for mixfix operators and we will see more
examples of this later.

Another function we can define is the conjunction of two boolean values, using a
similar approach.
\begin{code}
_∧_ : Bool → Bool → Bool
tt ∧ b = b
ff ∧ b = ff
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
concept of \textit{equal} here is that both of the values are convertible to the
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
open import Data.Nat using (ℕ; zero; suc) renaming (_≟_ to _≟ℕ_)
\end{code}
The equality type is polymorhic in some other underlying type, \AgdaArgument{A}.
The only way we have to construct values of this type is by the constructor
\AgdaInductiveConstructor{refl}, which says that each value is propositionaly
equal to itself. Symmetry and transitivity of \AgdaDatatype{\_≡\_} are theorems
in Agda.
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
  open import Data.Nat using (_+_)
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
\section{Decidable Equality}
\begin{code}
open import Relation.Binary.Core using (Decidable)
open import Relation.Nullary using (Dec; yes; no)

_≟B_ : Decidable {A = Bool} _≡_
tt  ≟B tt = yes refl
ff ≟B ff  = yes refl
tt  ≟B ff = no λ()
ff ≟B tt  = no λ()

⌊_⌋ : {A : Set} {a b : A} → Dec (a ≡ b) → Bool
⌊ yes p ⌋ = tt
⌊ no ¬p ⌋ = ff
\end{code}
\section{Formalizing Type Systems}
In what follows, we will take a look at how we can use Agda to formalize
deductive systems. We will take the simplest example there is, the Simply Typed
λ Calculus. Some surface-level knowledge of this calculus is assumed.
\subsection{De Bruijn Indices}
Firstly, we shall need some machinery to make our lives easier. We could use
string literals as variable names in our system, however this would lead to
certain difficulties further on. Instead, we shall use the concept commonly
referred to as De Bruijn indices\parencite{de1972lambda}. These replace variable
names with natural numbers, where each number $n$ refers to the variable bound
by the binder $n$ positions above the current scope in the syntactical tree. Some
examples of this naming schema are shown in Figure \ref{debruijn}.
\begin{figure}[h]
  \centering
  \begin{tabular}{ l l }
    \multicolumn{1}{c}{Literal syntax} & \multicolumn{1}{c}{De Bruijn syntax} \\
    \midrule
    \verb|λx.x| & \verb|λ 0| \\
    \verb|λx.λy.x| & \verb|λλ 1| \\
    \verb|λx.λy.λz.x z (y z)| & \verb|λλλ 2 0 (1 0)| \\
    \verb|λf.(λx.f(x x)) (λx.f(x x))| & \verb|λ(λ 1 (0 0) (λ 1 (0 0)| \\
  \end{tabular}
  \caption{Examples of λ terms using standard naming scheme on the left and
    using De Bruijn indices on the right.}
  \label{debruijn}
\end{figure}

    
\subsection{Example: Simply Typed λ Calculus}
\subsubsection{Syntax}
\subsubsection{Semantics by Embedding into Agda}
\section{Coinduction}
\subsection{Examples of coinductive types}
\subsubsection{Coproducts}
\subsubsection{Streams}
\subsection{Bisimilarity}
\subsection{The Delay Monad}

\begin{code}
open import Data.Integer using (ℤ; +_; _+_; _-_; _*_)
open import Data.Maybe using (Maybe; nothing; just; maybe)
open import Data.Product using (Σ; ∃; ∃-syntax)
open import Data.List using (List; []; [_]; _∷_; null; map; all; length)
open import Data.Integer.Properties renaming (_≟_ to _≟ℤ_)
open import Codata.Thunk using (force)
open import Codata.Delay using (Delay; now; later; never; runFor) renaming (bind to _>>=_)

data _∈_ {A : Set} : A → List A → Set where
  here : ∀ {x xs} → x ∈ (x ∷ xs)
  there : ∀ {x a xs} → x ∈ xs → x ∈ (a ∷ xs)
infix 10 _∈_

lookup : ∀ {A x xs} → x ∈ xs → A
lookup {x = x} here = x
lookup (there w) = lookup w

\end{code}

\chapter{SECD Machine}
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
take the universal one for our data type \AgdaDatatype{A}, then we obtain a type
that's isomorphic to linked lists.

We also define a shorthand for constructing the end of a path.
\begin{code}
_>|_ : ∀ {A R} {a b c : A} → R a b → R b c → Path R a c
a >| b = a >> b >> ∅
\end{code}
Furthermore, we can also append two paths, given that the end of the first path
matches the start of the second one.
\begin{code}
_>+>_ : ∀ {A R} {a b c : A} → Path R a b → Path R b c → Path R a c
∅ >+> r = r
(x >> l) >+> r = x >> (l >+> r)
infixr 4 _>+>_
\end{code}
\subsection{Machine types}
We start by defining the type of constants our machine will recognize. We will
limit ourselves to booleans and integers.
\begin{code}
data Const : Set where
  true false : Const
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

Now we can define the type assignment of constants.
\begin{code}
-- Assignment of types b constants.
typeof : Const → Type
typeof true    = boolT
typeof false   = boolT
typeof (int x) = intT
\end{code}
Next, we define the typed stack, environment, and function dump.
\begin{code}
Stack   = List Type
Env     = List Type
FunDump = List Type
\end{code}

\begin{code}
record State : Set where
  constructor _#_#_
  field
    s : Stack
    e : Env
    f : FunDump
\end{code}
\subsection{Typing relation}
\begin{code}
infix 5 ⊢_↝_
infix 5 ⊢_⊳_
mutual
  ⊢_↝_ : State → State → Set
  ⊢ s₁ ↝ s₂ = Path ⊢_⊳_ s₁ s₂

  data ⊢_⊳_ : State → State → Set where
    ldf  : ∀ {s e f a b}
         → (⊢ [] # (a ∷ e) # (a ⇒ b ∷ f) ↝ [ b ] # (a ∷ e) # (a ⇒ b ∷ f))
         → ⊢ s # e # f ⊳ (a ⇒ b ∷ s) # e # f
\end{code}
\begin{code}
    lett : ∀ {s e f x}
         → ⊢ (x ∷ s) # e # f ⊳ s # (x ∷ e) # f
    ap   : ∀ {s e f a b}
         → ⊢ (a ∷ a ⇒ b ∷ s) # e # f ⊳ (b ∷ s) # e # f
    rap  : ∀ {s e f a b}
         → ⊢ (a ∷ a ⇒ b ∷ s) # e # f ⊳ [ b ] # e # f
    ldr  : ∀ {s e f a b}
         → (a ⇒ b ∈ f)
         → ⊢ s # e # f ⊳ (a ⇒ b ∷ s) # e # f
    rtn  : ∀ {s e a b f}
         → ⊢ (b ∷ s) # e # (a ⇒ b ∷ f) ⊳ [ b ] # e # (a ⇒ b ∷ f)
    nil  : ∀ {s e f a}
         → ⊢ s # e # f ⊳ (listT a ∷ s) # e # f
    ldc  : ∀ {s e f}
         → (const : Const)
         → ⊢ s # e # f ⊳ (typeof const ∷ s) # e # f
    ld   : ∀ {s e f val}
         → (val ∈ e)
         → ⊢ s # e # f ⊳ (val ∷ s) # e # f
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
    not  : ∀ {s e f}
         → ⊢ (boolT ∷ s) # e # f ⊳ (boolT ∷ s) # e # f
    if   : ∀ {s s' e e' f f'}
         → ⊢ s # e # f ↝ s' # e' # f'
         → ⊢ s # e # f ↝ s' # e' # f'
         → ⊢ (boolT ∷ s) # e # f ⊳ s' # e' # f'

nil? : ∀ {s e f a} → ⊢ (listT a ∷ s) # e # f ↝ (boolT ∷ s) # e # f
nil? = nil >| eq?

loadList : ∀ {s e f} → List ℕ → ⊢ s # e # f ↝ (listT intT ∷ s) # e # f
loadList [] = nil >> ∅
loadList (x ∷ xs) = (loadList xs) >+> (ldc (int (+ x)) >| cons)

-- This syntactic sugar makes writing out SECD types easier.
-- Doesn't play nice with Agda polymorphism?
--withEnv : Env → Type → Type
--withEnv e (pairT t u)       = pairT (withEnv e t) (withEnv e u)
--withEnv e (funT a b)        = let aWithE = (withEnv e a) in closureT aWithE (withEnv (aWithE ∷ e) b) e
--withEnv e (listT t)         = listT (withEnv e t)
--withEnv e intT              = intT
--withEnv e boolT             = boolT
--withEnv e (closureT a b e') = closureT a b e'

-- 2 + 3
2+3 : ⊢ [] # [] # [] ↝ [ intT ] # [] # []
2+3 =
    ldc (int (+ 2))
 >> ldc (int (+ 3))
 >| add

-- λx.x + 1
inc : ∀ {e f} → ⊢ [] # (intT ∷ e) # (intT ⇒ intT ∷ f) ↝ [ intT ] # (intT ∷ e) # (intT ⇒ intT ∷ f)
inc =
    ld here
 >> ldc (int (+ 1))
 >> add
 >| rtn

-- Apply 2 b the above.
inc2 : ⊢ [] # [] # [] ↝ [ intT ] # [] # []
inc2 =
    ldf inc
 >> ldc (int (+ 2))
 >| ap

-- Partial application test.
λTest : ⊢ [] # [] # [] ↝ [ intT ] # [] # []
λTest =
     ldf -- First, we construct the curried function.
       (ldf
         (ld here >> ld (there here) >> add >| rtn) >| rtn)
  >> ldc (int (+ 1)) -- Load first argument.
  >> ap              -- Apply b curried function. Results in a closure.
  >> ldc (int (+ 2)) -- Load second argument.
  >| ap              -- Apply b closure.

-- λa.λb.a+b
-- withEnv test. Below is what withEnv desugars b.
-- plus : ∀ {e f} → ⊢ [] # e # f ↝ [ closureT intT (closureT intT intT (intT ∷ e)) e ] # e # f
plus : ∀ {s e f} → ⊢ s # e # f ⊳ ((intT ⇒ intT ⇒ intT) ∷ s) # e # f
plus = ldf (ldf (ld here >> ld (there here) >> add >| rtn) >| rtn)

-- Shit getting real.
foldl : ∀ {e f} → ⊢ [] # e # f ⊳ [ ((intT ⇒ intT ⇒ intT) ⇒ intT ⇒ (listT intT) ⇒ intT) ] # e # f
-- Below is the Agda-polymorphic version which does not typecheck. Something b do with how `withEnv e b` does not normalize further.
-- foldl : ∀ {a b e f} → ⊢ [] # e # f ↝ [ withEnv e ((b ⇒ a ⇒ b) ⇒ b ⇒ (listT a) ⇒ b)] # e # f
-- Explicitly typing out the polymorhic version, however, works:
--foldl : ∀ {a b e f} → ⊢ [] # e # f ⊳ [
--         closureT                            -- We construct a function,
--             (closureT b (closureT a b (b ∷ e)) e) -- which takes the folding function,
--             (closureT b                     -- returning a function which takes acc,
--               (closureT (listT a)           -- returning a function which takes the list,
--                 b                           -- and returns the acc.
--                 (b ∷ (closureT b (closureT a b (b ∷ e)) e) ∷ e))
--               ((closureT b (closureT a b (b ∷ e)) e) ∷ e))
--             e
--         ] # e # f
-- BDO: figure out what's going on here if has time.
foldl = ldf (ldf (ldf body >| rtn) >| rtn)
  where
    body =
         ld here                   -- Load list.
      >> nil?                      -- Is it empty?
      >+> if (ld (there here) >| rtn) -- If so, load & return acc.
          (ld (there (there here))     -- If not, load folding function.
        >> ld (there here)           -- Load previous acc.
        >> ap                      -- Partially apply folding function.
        >> ld here                 -- Load list.
        >> head                    -- Get the first element.
        >> ap                      -- Apply, yielding new acc.
        >> ldr (there (there here))     -- Partially-tail apply the folding function b us.
        >> ld (there (there here))     -- Load the folding function.
        >> ap >> flp >> ap >> ld here >> tail >| rap) >> ∅                      -- Apply acc, result in another closure.
--        >> ap                      -- Apply acc, result in another closure.
--        >> ld here                 -- Load list.
--        >> tail                    -- Drop the first element we just processed.
--        >| rap)                      -- Finally apply the last argument, that rest of the list.

mutual
  ⟦_⟧ᵉ : Env → Set
  ⟦ [] ⟧ᵉ     = ⊤
  ⟦ x ∷ xs ⟧ᵉ = ⟦ x ⟧ᵗ × ⟦ xs ⟧ᵉ

  ⟦_⟧ᵈ : FunDump → Set
  ⟦ [] ⟧ᵈ                    = ⊤
  ⟦ intT ∷ xs ⟧ᵈ = ⊥
  ⟦ boolT ∷ xs ⟧ᵈ = ⊥
  ⟦ pairT x x₁ ∷ xs ⟧ᵈ = ⊥
  ⟦ a ⇒ b ∷ xs ⟧ᵈ = Closure a b × ⟦ xs ⟧ᵈ
  ⟦ listT x ∷ xs ⟧ᵈ = ⊥

  record Closure (a b : Type) : Set where
    inductive
    constructor ⟦_⟧ᶜ×⟦_⟧ᵉ×⟦_⟧ᵈ
    field
      {e} : Env
      {f} : FunDump
      ⟦c⟧ᶜ : ⊢ [] # (a ∷ e) # (a ⇒ b ∷ f) ↝ [ b ] # (a ∷ e) # (a ⇒ b ∷ f)
      ⟦e⟧ᵉ : ⟦ e ⟧ᵉ
      ⟦f⟧ᵈ : ⟦ f ⟧ᵈ

  ⟦_⟧ᵗ : Type → Set
  ⟦ intT ⟧ᵗ           = ℤ
  ⟦ boolT ⟧ᵗ          = Bool
  ⟦ pairT t₁ t₂ ⟧ᵗ    = ⟦ t₁ ⟧ᵗ × ⟦ t₂ ⟧ᵗ
  ⟦ a ⇒ b ⟧ᵗ       = Closure a b
  ⟦ listT t ⟧ᵗ        = List ⟦ t ⟧ᵗ

⟦_⟧ˢ : Stack → Set
⟦ [] ⟧ˢ     = ⊤
⟦ x ∷ xs ⟧ˢ = ⟦ x ⟧ᵗ × ⟦ xs ⟧ˢ

lookupᵉ : ∀ {x xs} → ⟦ xs ⟧ᵉ → x ∈ xs → ⟦ x ⟧ᵗ
lookupᵉ (x , _) here       = x
lookupᵉ (_ , xs) (there w) = lookupᵉ xs w

tailᵈ : ∀ {x xs} → ⟦ x ∷ xs ⟧ᵈ → ⟦ xs ⟧ᵈ
tailᵈ {intT} ()
tailᵈ {boolT} ()
tailᵈ {pairT x x₁} ()
tailᵈ {a ⇒ b} (_ , xs) = xs
tailᵈ {listT x} ()

--lookupᵈ : ∀ {x xs} → ⟦ xs ⟧ᵈ → x ∈ xs → ⟦ x ⟧ᶜˡ
--lookupᵈ {mkClosureT _ _ _} (x , _) here = x
--lookupᵈ {mkClosureT _ _ _} list (there at) = lookupᵈ (tailᵈ list) at

lookupᵈ : ∀ {a b f} → ⟦ f ⟧ᵈ → a ⇒ b ∈ f → Closure a b
lookupᵈ (x , _) here = x
lookupᵈ f (there w) = lookupᵈ (tailᵈ f) w

run : ∀ {s s' e e' f f' i} → ⟦ s ⟧ˢ → ⟦ e ⟧ᵉ → ⟦ f ⟧ᵈ → ⊢ s # e # f ↝ s' # e' # f'
                           → Delay ⟦ s' ⟧ˢ i
run s e d ∅ = now s
run s e d (ldf code >> r) = run (⟦ code ⟧ᶜ×⟦ e ⟧ᵉ×⟦ d ⟧ᵈ , s) e d r
run s e d (ldr at >> r) = run (lookupᵈ d at , s) e d r
run (a , ⟦ code ⟧ᶜ×⟦ fE ⟧ᵉ×⟦ dump ⟧ᵈ , s) e d (ap >> r) =
  later λ where .force → do
                           (b , _) ← run ⋅ (a , fE) (⟦ code ⟧ᶜ×⟦ fE ⟧ᵉ×⟦ dump ⟧ᵈ , dump) code
                           run (b , s) e d r
run (a , ⟦ code ⟧ᶜ×⟦ fE ⟧ᵉ×⟦ dump ⟧ᵈ , s) e d (rap >> ∅) =
  later λ where .force → run ⋅ (a , fE) (⟦ code ⟧ᶜ×⟦ fE ⟧ᵉ×⟦ dump ⟧ᵈ , dump) code
run (a , ⟦ code ⟧ᶜ×⟦ fE ⟧ᵉ×⟦ dump ⟧ᵈ , s) e d (rap >> x >> r) =
  later λ where .force → run (a , ⟦ code ⟧ᶜ×⟦ fE ⟧ᵉ×⟦ dump ⟧ᵈ , ⋅) e d (ap >> x >> r)
run (b , _) e d (rtn >> r) = run (b , ⋅) e d r
run (x , s) e d (lett >> r)      = run s (x , e) d r
run s e d (nil >> r)             = run ([] , s) e d r
run s e d (ldc const >> r)       = run (makeConst const , s) e d r
  where makeConst : (c : Const) → ⟦ typeof c ⟧ᵗ
        makeConst true    = tt
        makeConst false   = ff
        makeConst (int x) = x
run s e d (ld at >> r)           = run (lookupᵉ e at , s) e d r
run (x , y , s) e d (flp >> r)   = run (y , x , s) e d r
run (x , xs , s) e d (cons >> r) = run (x ∷ xs , s) e d r
run ([] , s) e d (head >> r)     = never
run (x ∷ _ , s) e d (head >> r)  = run (x , s) e d r
run ([] , s) e d (tail >> r)     = never
run (x ∷ xs , s) e d (tail >> r) = run (xs , s) e d r
run (x , y , s) e d (pair >> r)  = run ((x , y) , s) e d r
run ((x , _) , s) e d (fst >> r) = run (x , s) e d r
run ((_ , y) , s) e d (snd >> r) = run (y , s) e d r
run (x , y , s) e d (add >> r)   = run (x + y , s) e d r
run (x , y , s) e d (sub >> r)   = run (x - y , s) e d r
run (x , y , s) e d (mul >> r)   = run (x * y , s) e d r
run (a , b , s) e d (eq? >> r)   = run (compare a b , s) e d r
  where compare : {t₁ t₂ : Type} → ⟦ t₁ ⟧ᵗ → ⟦ t₂ ⟧ᵗ → ⟦ boolT ⟧ᵗ
        compare {intT} {intT} a b   = ⌊ a ≟ℤ b ⌋
        compare {boolT} {boolT} a b = ⌊ a ≟B b ⌋
        compare {pairT _ _} {pairT _ _} (a₁ , a₂) (b₁ , b₂) = (compare a₁ b₁) ∧ (compare a₂ b₂)
        compare {listT xs} {listT ys} a b = ⌊ length a ≟ℕ length b ⌋ -- BDO
        compare {_} {_} _ _ = ff
run (x , s) e d (not >> r)       = run (¬ x , s) e d r
run (bool , s) e d (if c₁ c₂ >> r) with bool
… | tt = later λ where .force → run s e d (c₁ >+> r)
… | ff = later λ where .force → run s e d (c₂ >+> r)

runℕ : ∀ {x s} → ⊢ [] # [] # [] ↝ (x ∷ s) # [] # [] → ℕ → Maybe ⟦ x ⟧ᵗ
runℕ c n = runFor n
  do
    (x , _) ← run ⋅ ⋅ ⋅ c
    now x


_ : runℕ 2+3 1 ≡ just (+ 5)
_ = refl

_ : runℕ inc2 2 ≡ just (+ 3)
_ = refl

_ : runℕ λTest 3 ≡ just (+ 3)
_ = refl

foldTest : ⊢ [] # [] # [] ↝ [ intT ] # [] # []
foldTest =
     foldl
  >> plus
  >> ap
  >> ldc (int (+ 0))
  >> ap
  >> (loadList (1 ∷ 2 ∷ 3 ∷ 4 ∷ []))
  >+> ap
  >> ∅

_ : runℕ foldTest 29 ≡ just (+ 10)
_ = refl


Ctx = List Type

infix 2 _×_⊢_
data _×_⊢_ : Ctx → Ctx → Type → Set where
  var : ∀ {Ψ Γ x} → x ∈ Γ → Ψ × Γ ⊢ x
  ƛ_  : ∀ {Ψ Γ α β} → (α ⇒ β ∷ Ψ) × α ∷ Γ ⊢ β → Ψ × Γ ⊢ α ⇒ β
  _$_ : ∀ {Ψ Γ α β} → Ψ × Γ ⊢ α ⇒ β → Ψ × Γ ⊢ α → Ψ × Γ ⊢ β
  rec : ∀ {Ψ Γ α β} → (α ⇒ β) ∈ Ψ → Ψ × Γ ⊢ α ⇒ β
  if_then_else_ : ∀ {Ψ Γ α} → Ψ × Γ ⊢ boolT → Ψ × Γ ⊢ α → Ψ × Γ ⊢ α → Ψ × Γ ⊢ α
  _==_ : ∀ {Ψ Γ} → Ψ × Γ ⊢ intT → Ψ × Γ ⊢ intT → Ψ × Γ ⊢ boolT
  #_ : ∀ {Ψ Γ} → ℤ → Ψ × Γ ⊢ intT
  #⁺_ : ∀ {Ψ Γ} → ℕ → Ψ × Γ ⊢ intT
  mul : ∀ {Ψ Γ} → Ψ × Γ ⊢ intT ⇒ intT ⇒ intT
  sub : ∀ {Ψ Γ} → Ψ × Γ ⊢ intT ⇒ intT ⇒ intT
infixr 2 ƛ_
infixl 3 _$_
infix 5 _==_


fac : [] × [] ⊢ (intT ⇒ intT)
fac = ƛ if (var here == #⁺ 1)
          then #⁺ 1
          else (mul $ (rec here $ (sub $ var here $ #⁺ 1))
                    $ var here)

mutual
  compileT : ∀ {Ψ Γ α β} → (α ⇒ β ∷ Ψ) × (α ∷ Γ) ⊢ β → ⊢ [] # (α ∷ Γ) # (α ⇒ β ∷ Ψ) ↝ [ β ] # (α ∷ Γ) # (α ⇒ β ∷ Ψ)
  compileT (f $ x) = compile f >+> compile x >+> rap >> ∅
  compileT (if t then a else b) = compile t >+> if (compileT a) (compileT b) >> ∅
  compileT t = compile t >+> rtn >> ∅

  compile : ∀ {Ψ Γ α s} → Ψ × Γ ⊢ α → ⊢ s # Γ # Ψ ↝ (α ∷ s) # Γ # Ψ
  compile (var x) = ld x >> ∅
  compile (ƛ t) = ldf (compileT t) >> ∅
  compile (f $ x) = compile f >+> compile x >+> ap >> ∅
  compile (rec x) = ldr x >> ∅
  compile (if t then a else b) = compile t >+> if (compile a) (compile b) >> ∅
  compile (a == b) = compile b >+> compile a >+> eq? >> ∅
  compile (# x) = ldc (int x) >> ∅
  compile (#⁺ x) = ldc (int (+ x)) >> ∅
  compile mul = ldf (ldf (ld here >> ld (there here) >| mul) >| rtn) >> ∅
  compile sub = ldf (ldf (ld here >> ld (there here) >| sub) >| rtn) >> ∅

_ : runℕ (compile (fac $ #⁺ 5)) 27 ≡ just (+ 120)
_ = refl

\end{code}

\chapter{Epilogue}

\end{document}
