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
  {\par\normalfont\hfill--\ \chapquote@author\hspace*{\@tempdima}\par\bigskip}
\makeatother

\begin{document}
\chapter{Introduction}

\chapter{Intuitionistic logic}
\begin{chapquote}{R. Feynman}
  What I cannot create, I do not understand.
\end{chapquote}

\begin{code}
open import Function using (flip)
open import Data.Unit using (⊤; tt)
open import Data.Bool using (Bool) renaming (not to ¬_)
open import Data.Integer using (ℤ; +_; _+_)
open import Data.Maybe using (Maybe; nothing; just; maybe)
open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ; ∃; ∃-syntax)
open import Data.List using (List; []; [_]; _∷_; map; length; lookup)
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

record Stream (A : Set) : Set where
  coinductive
  field
    cohead : A
    cotail : Stream A
open Stream public

repeat : ∀ {A} → A → Stream A
cohead (repeat a) = a
cotail (repeat a) = repeat a
\end{code}

\end{document}
