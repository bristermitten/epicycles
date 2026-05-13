\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{dissertation}[2012/05/04, Daniel Page <Daniel.Page@bristol.ac.uk>]

% =============================================================================

% parse class options

\RequirePackage{pgfkeys}
\RequirePackage{pgfopts}

\pgfkeys{/dissertation/.cd,
%     author = string
      author/.store in = \dissertation@author,
      author           = {},
% supervisor = string
  supervisor/.store in = \dissertation@supervisor, 
  supervisor           = {},
%     degree = [BSc|MEng|MSci|MSc|PhD]
      degree/.store in = \dissertation@degree,
      degree           = {MEng},
%     unit = [COMS30044|COMS30045|COMSM0052|COMSM0142]
      unit/.store in = \dissertation@unit,
      unit           = {COMS30045},
%      title = string
       title/.store in = \dissertation@title@major,
       title           = {},
%   subtitle = string
    subtitle/.store in = \dissertation@title@minor,
    subtitle           = {},
%       type = string
        type/.store in = \dissertation@type,
        type           = {},
%       type = string
        year/.store in = \dissertation@year,
        year           = {\the\year}
}

\ProcessPgfOptions{/dissertation}

% load base class, then general-purpose packages

\LoadClass[10pt,a4paper,oneside]{book}

% http://www.ctan.org/tex-archive/macros/latex/required/graphics
\RequirePackage{graphicx}
% http://www.ctan.org/tex-archive/macros/latex/required/amslatex
\RequirePackage{amsmath}
\RequirePackage{amssymb}
% http://www.ctan.org/tex-archive/macros/latex/contrib/adjustbox
\RequirePackage{adjustbox}
% http://www.ctan.org/tex-archive/macros/latex/contrib/etoolbox
\RequirePackage{etoolbox}
% http://www.ctan.org/tex-archive/macros/latex/contrib/fancyhdr
\RequirePackage{fancyhdr}
% http://www.ctan.org/tex-archive/macros/latex/contrib/geometry
\RequirePackage{geometry}
% http://www.ctan.org/tex-archive/macros/latex/contrib/datetime
\RequirePackage{datetime}
% http://www.ctan.org/tex-archive/macros/latex/contrib/algorithm2e
\RequirePackage[algochapter]{algorithm2e}
% http://www.ctan.org/tex-archive/macros/latex/contrib/listings
\RequirePackage{listings}
% http://www.ctan.org/tex-archive/macros/latex/contrib/xstring
\RequirePackage{xstring}
% http://www.ctan.org/tex-archive/macros/latex/contrib/url
\RequirePackage{url}
% http://www.ctan.org/tex-archive/macros/latex/contrib/hyperref
\RequirePackage{hyperref}[colorlinks=true,citecolor=blue]
% http://www.ctan.org/tex-archive/macros/latex/contrib/lipsum
\RequirePackage{lipsum}
% http://www.ctan.org/tex-archive/usergrps/dante/dtk
\RequirePackage{dtklogos}

% =============================================================================

\makeatletter

% -----------------------------------------------------------------------------

% configure hyperref

\hypersetup{colorlinks=true,bookmarks=false,urlcolor=red}

% configure algorithm2e

\DontPrintSemicolon

% configure listings

\lstset{basicstyle=\ttfamily,captionpos=b}
\renewcommand{\lstlistlistingname}{List of Listings}

% -----------------------------------------------------------------------------

% configure style of table of contents

\setcounter{tocdepth}{1}

% configure style of bibliography

\bibliographystyle{plainurl}

% configure style of pages

\geometry{a4paper,lmargin=2.5cm,rmargin=2.5cm,tmargin=2.5cm,bmargin=2.5cm}

\fancypagestyle{plain}{
  \fancyhf{}

  \renewcommand{\headrulewidth}{0.5pt}
  \renewcommand{\footrulewidth}{0.5pt}

  \fancyfoot[C]{\thepage}
}

\fancypagestyle{marked}{
  \fancyhf{}

  \renewcommand{\headrulewidth}{0.5pt}
  \renewcommand{\footrulewidth}{0.5pt}

  \fancyhead[LO]{\slshape \rightmark}
  \fancyhead[RE]{\slshape  \leftmark}

  \fancyfoot[C]{\thepage}
}

\pagestyle{plain}

% -----------------------------------------------------------------------------

% define macro to generate UoB title page

\renewcommand{\maketitle}{
  \newpage
  \thispagestyle{empty}


%  \IfEq{\dissertation@type}{}{}{
%    \adjustbox{padding={5pt},frame={1pt},right}{Dissertation Type: {\dissertation@type}}
%  }

  
  \begin{center}
                \includegraphics[scale=0.3]{logo_2024/PDF/UoB_CMYK_24}                \\
                              \vspace*{1.0cm}
                          SCHOOL OF COMPUTER SCIENCE                        \\
                              \vspace*{2.0cm}
                              \end{center}
  {\LARGE \parbox{\textwidth}{\IfEq{\dissertation@title@major}{}{}{\centering \dissertation@title@major \par}}} \par
                              \vspace*{1cm}\noindent
    {\Large \parbox{\textwidth}{\IfEq{\dissertation@title@minor}{}{}{\centering \dissertation@title@minor \par}}} \par
                              \vspace*{1.0cm}\noindent
                              \begin{center}
                          {\Large \dissertation@author}                         \\

                              \vspace*{1.0cm}
                          \rule{0.5\textwidth}{0.5pt}
                              \vspace*{1.0cm}

            A dissertation submitted to the University of Bristol
            in accordance with the requirements of the degree of
                    \IfEqCase*{\dissertation@degree}{
                      {BSc} {Bachelor of     Science}
                      {MEng}{Master   of Engineering}
                      {MSci}{Master   of     Science}
                      {MSc} {Master   of     Science}
                      {PhD} {Doctor   of Philosophy}
                    }~in the Faculty of Engineering \textbf{worth
                    \IfEqCase*{\dissertation@unit}{
                      {COMS30044}{20CP}
                      {COMS30045}{40CP}
                      {COMSM0052}{40CP}
                      {COMSM0142}{40CP}
                    }}.                                

                              \vspace*{1.0cm}
                          \rule{0.5\textwidth}{0.5pt}
                              \vspace*{1.0cm}

                                  \today
  \end{center}
  \vspace*{\fill}
}

% define macro to generate UoB declaration

\newcommand{\makedecl}{
  \newpage
  \thispagestyle{plain}

  \chapter*{Declaration}
  
I declare that the work in this dissertation was carried out in accordance with the requirements of the University’s Regulations and Code of Practice for Taught Programmes and that it has not been submitted for any other academic award. Except where indicated by specific reference in the text, this work is my own work. Work done in collaboration with, or with the assistance of others including AI methods, is indicated as such. I have identified all material in this dissertation which is not my own work through appropriate referencing and acknowledgement. Where I have quoted or otherwise incorporated material which is the work of others, I have included the source in the references. Any views expressed in the dissertation, other than referenced material, are those of the author.

  
% A dissertation submitted to the University of Bristol in accordance with the requirements of the degree of {\dissertation@degree} in the Faculty of Engineering. School of Computer Science, {\today}.

  %This dissertation is submitted to the University of Bristol in accordance 
  %with the requirements of the degree of {\dissertation@degree} in the Faculty 
  %of Engineering.  It has not been submitted for any other degree or diploma 
%  of any examining body.  Except where specifically acknowledged, it is all 
%  the work of the Author. 

  \vspace{3cm}

  \noindent {\dissertation@author}, \today
}

% define macro to generate AI declaration

\newcommand{\makeaidecl}{
  \newpage
  \thispagestyle{plain}

  \chapter*{AI Declaration}
  
I declare that any and all AI usage within the project has been recorded and
noted within Appendix A or within the main body of the text itself. This
includes (but is not limited to) usage of text generation methods incl. LLMs,
text summarisation methods, or image generation methods. \

I understand that failing to divulge use of AI within my
work counts as contract cheating and can result in a zero mark for the
dissertation or even requiring me to withdraw
from the University.
  

  \vspace{3cm}

  \noindent {\dissertation@author}, \today
}


% define macros to mark front, main and back matter

\renewcommand{\frontmatter}{
  \cleardoublepage
  \pagestyle{plain}
  \pagenumbering{roman}
}
\renewcommand{\mainmatter}{
  \cleardoublepage
  \pagestyle{marked}
  \pagenumbering{arabic}
}
\renewcommand{\backmatter}{
  \cleardoublepage
  \pagestyle{marked}
}

% -----------------------------------------------------------------------------

\makeatother

% =============================================================================


