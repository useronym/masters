\documenldrlass[
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
  table,   %% This option causes the coloring of tables. Replace
           %% with `notable` to restore plain LaTeX tables.
  nolof    %% This option prints the List of Figures. Replace with
           %% `nolof` to hide the List of Figures.
  %% More options are listed in the user guide at
  %% <http://mirrors.ctan.org/macros/latex/contrib/fithesis/guide/mu/fi.pdf>.
]{fithesis3}

\usepackage{fontspec}
\usepackage{yfonts}
\usepackage{unicode-math}
\usepackage{xunicode}
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
    bib           = bibliography.bib,
}

%% \usepackage{makeidx}      %% The `makeidx` package contains
%%\makeindex                %% helper commands for index typesetting.
%% These additional packages are used within the document:
\usepackage{amsmath}  %% Mathematics
\usepackage{mathtools}  %% Mathematics
\usepackage{amsthm}
\usepackage{amsfonts}
\usepackage{url}      %% Hyperlinks
\usepackage{epigraph}
\setlength{\epigraphwidth}{3in}

\theoremstyle{definition}
\newtheorem{theorem}{Theorem}
\newtheorem{definition}{Definition}
\newtheorem{notation}{Notation}


\usepackage{agda}

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
\chapter{SECD Machine}
\chapter{Formalization}

\begin{code}
open import Function using (flip)
open import Data.Unit using (⊤) renaming (tt to ⋅)
open import Data.Bool using (Bool) renaming (not to ¬_; true to tt; false to ff)
open import Data.Integer using (ℤ; +_; _+_)
open import Data.Maybe using (Maybe; nothing; just; maybe)
open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ; ∃; ∃-syntax)
open import Data.List using (List; []; [_]; _∷_; map; length)
open import Size
open import Codata.Thunk using (force)
open import Codata.Delay using (Delay; now; later) renaming (bind to _>>=_)


data Path {A : Set} (R : A → A → Set) : A → A → Set where
  ∅    : ∀ {a} → Path R a a
  _>>_ : ∀ {a b c} → R a b → Path R b c → Path R a c
infixr 5 _>>_

_>|_ : ∀ {A R} {a b c : A} → R a b → R b c → Path R a c
a >| b = a >> b >> ∅

concatenate : ∀ {A R} {a b c : A} → Path R a b → Path R b c → Path R a c
concatenate ∅ r = r
concatenate (x >> l) r = x >> (concatenate l r)

snoc : ∀ {A R} {a b c : A} → Path R a b → R b c → Path R a c
snoc ∅ e = e >> ∅
snoc (x >> p) e = x >> (snoc p e)

reverse : ∀ {A R} {a b : A} → Path R a b → Path (flip R) b a
reverse ∅ = ∅
reverse (x >> p) = snoc (reverse p) x

data ListD {I : Set} (T : I → Set) : List I → Set where
  nilD  : ListD T []
  consD : ∀ {x xs} → (elem : T x) → (rest : ListD T xs) → ListD T (x ∷ xs)

data _∈_ {A : Set} : A → List A → Set where
  here : ∀ {x xs} → x ∈ (x ∷ xs)
  there : ∀ {x a xs} → x ∈ xs → x ∈ (a ∷ xs)

lookup : ∀ {A x xs} → x ∈ xs → A
lookup {x = x} here = x
lookup (there w) = lookup w

--lookupD : {I : Set} {T : I → Set} {xs : List I} → ListD T xs → (at : Fin (length xs)) → T (lookup xs at)
--lookupD nilD ()
--lookupD (consD elem xs) zero     = elem
--lookupD (consD elem xs) (suc at) = lookupD xs at

record Stream (A : Set) : Set where
  coinductive
  field
    cohead : A
    cotail : Stream A
open Stream public

repeat : ∀ {A} → A → Stream A
cohead (repeat a) = a
cotail (repeat a) = repeat a

-- Type of atomic constants. These can be loaded directly from a single instruction.
data Const : Set where
  true false : Const
  int : ℤ → Const

mutual
  -- Environment stores the types of bound variables.
  Env = List Type

  -- Types that our machine recognizes.
  data Type : Set where
    intT boolT : Type
    pairT : Type → Type → Type
    funT : Type → Type → Type
    closureT : Type → Type → Env → Type
    envT : Env → Type
    listT : Type → Type

_⇒_ : Type → Type → Type
_⇒_ = funT
infixr 15 _⇒_

-- Assignment of types to constants.
typeof : Const → Type
typeof true    = boolT
typeof false   = boolT
typeof (int x) = intT

-- Stack stores the types of values on the machine's stack.
Stack = List Type

-- Special kind of closure we use to allow recursive calls.
data ClosureT : Set where
  mkClosureT : Type → Type → Env → ClosureT

-- Boilerplate.
mkFrom : ClosureT → Type
mkFrom (mkClosureT from _ _) = from
mkTo : ClosureT → Type
mkTo (mkClosureT _ to _) = to
mkEnv : ClosureT → Env
mkEnv (mkClosureT _ _ env) = env

-- This is pretty much the call stack, allowing us to make recursive calls.
FunDump = List ClosureT

data StateKind : Set where
  running stopped : StateKind

-- A state of our machine.
record State : Set where
  constructor _#_#_
  field
    s : Stack
    e : Env
    f : FunDump

-- The typing relation.
infix 5 ⊢_↝_
infix 5 ⊢_⊳_
mutual
  ⊢_↝_ : State → State → Set
  ⊢ s₁ ↝ s₂ = Path ⊢_⊳_ s₁ s₂

  data ⊢_⊳_ : State → State → Set where
    ldf  : ∀ {s e f from to}
         → (⊢ [] # (from ∷ e) # (mkClosureT from to e ∷ f) ↝ [ to ] # [] # f)
         → ⊢ s # e # f ⊳ (closureT from to e ∷ s) # e # f
    lett : ∀ {s e f x}
         → ⊢ (x ∷ s) # e # f ⊳ s # (x ∷ e) # f
    ap   : ∀ {s e e' f from to}
         → ⊢ (from ∷ closureT from to e' ∷ s) # e # f ⊳ (to ∷ s) # e # f
    rap  : ∀ {s e e' f from to}
         → ⊢ (from ∷ closureT from to e' ∷ s) # e # f ⊳ [ to ] # [] # f
    ldr  : ∀ {s e f a b e'}
         → (mkClosureT a b e' ∈ f)
         → ⊢ s # e # f ⊳ (closureT a b e' ∷ s) # e # f
    rtn  : ∀ {s e e' a b f}
         → ⊢ (b ∷ s) # e # (mkClosureT a b e' ∷ f) ⊳ [ b ] # [] # f
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
    nil? : ∀ {s e f a}
         → ⊢ (listT a ∷ s) # e # f ⊳ (boolT ∷ s) # e # f
    not  : ∀ {s e f}
         → ⊢ (boolT ∷ s) # e # f ⊳ (boolT ∷ s) # e # f
    if   : ∀ {s s' e e' f f'}
         → ⊢ s # e # f ↝ s' # e' # f'
         → ⊢ s # e # f ↝ s' # e' # f'
         → ⊢ (boolT ∷ s) # e # f ⊳ s' # e' # f'

-- This syntactic sugar makes writing out SECD types easier.
-- Doesn't play nice with Agda polymorphism?
withEnv : Env → Type → Type
withEnv e (pairT t u)       = pairT (withEnv e t) (withEnv e u)
withEnv e (funT a b)        = let aWithE = (withEnv e a) in closureT aWithE (withEnv (aWithE ∷ e) b) e
withEnv e (listT t)         = listT (withEnv e t)
withEnv e intT              = intT
withEnv e boolT             = boolT
withEnv e (closureT a b e') = closureT a b e'
withEnv e (envT x)          = envT x

-- 2 + 3
_ : ⊢ [] # [] # [] ↝ [ intT ] # [] # []
_ =
    ldc (int (+ 2))
 >> ldc (int (+ 3))
 >| add

-- λx.x + 1
inc : ∀ {e f} → ⊢ [] # (intT ∷ e) # (mkClosureT intT intT [] ∷ f) ↝ [ intT ] # [] # f
inc =
    ld here
 >> ldc (int (+ 1))
 >> add
 >| rtn

-- Apply 2 to the above.
_ : ⊢ [] # [] # [] ↝ [ intT ] # _ # []
_ =
    ldf inc
 >> ldc (int (+ 2))
 >| ap

-- Partial application test.
_ : ⊢ [] # [] # [] ↝ [ intT ] # [] # []
_ =
     ldf -- First, we construct the curried function.
       (ldf
         (ld here >> ld (there here) >> add >| rtn) >| rtn)
  >> ldc (int (+ 1)) -- Load first argument.
  >> ap              -- Apply to curried function. Results in a closure.
  >> ldc (int (+ 2)) -- Load second argument.
  >| ap              -- Apply to closure.

-- λa.λb.a+b
-- withEnv test. Below is what withEnv desugars to.
-- plus : ∀ {e f} → ⊢ [] # e # f ↝ [ closureT intT (closureT intT intT (intT ∷ e)) e ] # e # f
plus : ∀ {s e f} → ⊢ s # e # f ⊳ (withEnv e (intT ⇒ intT ⇒ intT) ∷ s) # e # f
plus = ldf (ldf (ld here >> ld (there here) >> add >| rtn) >| rtn)

-- Shit getting real.
--foldl : ∀ {e f} → ⊢ [] # e # f ⊳ [ withEnv e ((intT ⇒ intT ⇒ intT) ⇒ intT ⇒ (listT intT) ⇒ intT) ] # e # f
-- Below is the Agda-polymorphic version which does not typecheck. Something to do with how `withEnv e b` does not normalize further.
-- foldl : ∀ {a b e f} → ⊢ [] # e # f ↝ [ withEnv e ((b ⇒ a ⇒ b) ⇒ b ⇒ (listT a) ⇒ b)] # e # f
-- Explicitly typing out the polymorhic version, however, works:
foldl : ∀ {a b e f} → ⊢ [] # e # f ⊳ [
         closureT                            -- We construct a function,
             (closureT b (closureT a b (b ∷ e)) e) -- which takes the folding function,
             (closureT b                     -- returning a function which takes acc,
               (closureT (listT a)           -- returning a function which takes the list,
                 b                           -- and returns the acc.
                 (b ∷ (closureT b (closureT a b (b ∷ e)) e) ∷ e))
               ((closureT b (closureT a b (b ∷ e)) e) ∷ e))
             e
         ] # e # f
-- TODO: figure out what's going on here if has time.
foldl = ldf (ldf (ldf body >| rtn) >| rtn)
  where
    body =
         ld here                   -- Load list.
      >> nil?                      -- Is it empty?
      >| if (ld (there here) >| rtn) -- If so, load & return acc.
          (ld (there (there here))     -- If not, load folding function.
        >> ld (there here)           -- Load previous acc.
        >> ap                      -- Partially apply folding function.
        >> ld here                 -- Load list.
        >> head                    -- Get the first element.
        >> ap                      -- Apply, yielding new acc.
        >> ldr (there (there here))     -- Partially-tail apply the folding function to us.
        >> ld (there (there here))     -- Load the folding function.
        >> flp                      -- Apply acc, result in another closure.
        >> ap                      -- Apply acc, result in another closure.
        >> ld here                 -- Load list.
        >> tail                    -- Drop the first element we just processed.
        >| rap)                      -- Finally apply the last argument, that rest of the list.
mutual
  ⟦_⟧ᵉ : Env → Set
  ⟦ [] ⟧ᵉ     = ⊤
  ⟦ x ∷ xs ⟧ᵉ = ⟦ x ⟧ᵗ × ⟦ xs ⟧ᵉ

  ⟦_⟧ᵈ : List ClosureT → Set
  ⟦ [] ⟧ᵈ                    = ⊤
  ⟦ mkClosureT a b e ∷ xs ⟧ᵈ = (Closure a b e) × ⟦ xs ⟧ᵈ

  record Closure (a b : Type) (e : Env) : Set where
    inductive
    constructor ⟦_⟧ᶜ×⟦_⟧ᵉ×⟦_⟧ᵈ
    field
      {f} : FunDump
      ⟦c⟧ᶜ : ⊢ [] # (a ∷ e) # (mkClosureT a b e ∷ f) ↝ [ b ] # [] # f
      ⟦e⟧ᵉ : ⟦ e ⟧ᵉ
      ⟦f⟧ᵈ : ⟦ f ⟧ᵈ

  ⟦_⟧ᵗ : Type → Set
  ⟦ intT ⟧ᵗ           = ℤ
  ⟦ boolT ⟧ᵗ          = Bool
  ⟦ pairT t₁ t₂ ⟧ᵗ    = ⟦ t₁ ⟧ᵗ × ⟦ t₂ ⟧ᵗ
  ⟦ funT a b ⟧ᵗ       = ⊤
  ⟦ closureT a b e ⟧ᵗ = Closure a b e
  ⟦ envT e ⟧ᵗ         = ⟦ e ⟧ᵉ
  ⟦ listT t ⟧ᵗ        = List ⟦ t ⟧ᵗ

⟦_⟧ˢ : Stack → Set
⟦ [] ⟧ˢ     = ⊤
⟦ x ∷ xs ⟧ˢ = ⟦ x ⟧ᵗ × ⟦ xs ⟧ˢ

⟦_⟧ᶜˡ : ClosureT → Set
⟦ mkClosureT a b e ⟧ᶜˡ = Closure a b e

lookupᵉ : ∀ {x xs} → ⟦ xs ⟧ᵉ → x ∈ xs → ⟦ x ⟧ᵗ
lookupᵉ (x , _) here       = x
lookupᵉ (_ , xs) (there w) = lookupᵉ xs w

tailᵈ : ∀ {x xs} → ⟦ x ∷ xs ⟧ᵈ → ⟦ xs ⟧ᵈ
tailᵈ {mkClosureT _ _ _} {[]} list       = ⋅
tailᵈ {mkClosureT _ _ _} {_ ∷ _} (_ , t) = t

lookupᵈ : ∀ {x xs} → ⟦ xs ⟧ᵈ → x ∈ xs → ⟦ x ⟧ᶜˡ
lookupᵈ {mkClosureT _ _ _} (x , _) here = x
lookupᵈ {mkClosureT _ _ _} list (there at) = lookupᵈ (tailᵈ list) at


run : ∀ {s s' e e' f f' i} → ⟦ s ⟧ˢ → ⟦ e ⟧ᵉ → ⟦ f ⟧ᵈ → ⊢ s # e # f ↝ s' # e' # f'
                           → Delay ⟦ s' ⟧ˢ i
run s e d ∅        = now s
run s e d (ldf code >> r) = run (⟦ code ⟧ᶜ×⟦ e ⟧ᵉ×⟦ d ⟧ᵈ , s) e d r
run s e d (ldr at >> r) = run (lookupᵈ d at , s) e d r
run (from , ⟦ code ⟧ᶜ×⟦ fE ⟧ᵉ×⟦ dump ⟧ᵈ , s) e d (ap >> r) =
  later
    λ where
      .force →
        do
          (to , _) ← run ⋅ (from , fE) (⟦ code ⟧ᶜ×⟦ fE ⟧ᵉ×⟦ dump ⟧ᵈ , dump) code
          run (to , s) e d r
run (from , ⟦ code ⟧ᶜ×⟦ fE ⟧ᵉ×⟦ dump ⟧ᵈ , s) e d (rap >> ∅) = later λ where .force → run ⋅ (from , fE) (⟦ code ⟧ᶜ×⟦ fE ⟧ᵉ×⟦ dump ⟧ᵈ , dump) code
run (from , cl , s) e d (rap >> r) = later λ where .force → run (from , cl , ⋅) ⋅ d (ap >> r)
run (b , _) _ (_ , d) (rtn >> r) = run (b , ⋅) ⋅ d r
run s e d (lett >> r) = {!!}
run s e d (nil >> r) = {!!}
run s e d (ldc const >> r) = {!!}
run s e d (ld at >> r) = {!!}
run s e d (flp >> r) = {!!}
run s e d (cons >> r) = {!!}
run s e d (head >> r) = {!!}
run s e d (tail >> r) = {!!}
run s e d (pair >> r) = {!!}
run s e d (fst >> r) = {!!}
run s e d (snd >> r) = {!!}
run s e d (add >> r) = {!!}
run s e d (nil? >> r) = {!!}
run s e d (not >> r) = {!!}
run (bool , s) e d (if c₁ c₂ >> r) with bool
… | tt = later λ where .force → run s e d (concatenate c₁ r)
… | ff = later λ where .force → run s e d (concatenate c₂ r)

\end{code}

\chapter{Epilogue}

\end{document}
