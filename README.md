mydotvim
========

[![I Love Vim](https://img.shields.io/badge/I%20Love-Vim-red.svg)](http://vim.org)

My dot vim folder

## Install

1. Get my dotvim

```shell
    git clone https://kinghom@github.com/kinghom/mydotvim.git ~/.vim
    cd ~/.vim
    git submodule init
    git submodule update
```

2. Add a submodule

```shell
    git submodule add URL bundle/NAME
    git add .
    git ci -m "some comment"
    git push
```

3. Update submodule

```shell
    git submodule foreach git pull origin master
```

4. Remove a submodule

```shell
    git submodule deinit --force [path to submodule]
    git rm --cached [path to submodule]
```
    Delete the relevant line from the '.gitmodules' file.
    Commit the superproject.

    OR

    Delete the relevant line from the '.gitmodules' and .git/config file.
    git rm --cached [path to submodule]
    Commit the superproject.


## Note

### Windows

We need the following tools:

- [Universal Ctags](https://github.com/universal-ctags/ctags-win32)

- [Gow](https://github.com/bmatzelle/gow)

  Gow (Gnu On Windows) is the lightweight alternative to Cygwin. It uses a convenient Windows installer that installs about 130 extremely useful open source UNIX applications compiled as native win32 binaries.


## List of plugins

- AnsiEsc
- anzu: display matching pattern in command line

- c: support for c/c++
- CamelCaseMotion
- Conque-Shell
- calendar.vim: nice calendar
- cscope_macros

- delimitMate: auto insert brackets
- DrawIt
- easy-align
- easymotion
    bit weird at first, but my flow has now gone to /[Class] || [Method] --> ,w --> char. Super fast. Hint: stare down where you want to go, then ,w
- expand-region
- FencView
- file-line
- FuzzyFinder
    I use it mostly for switching buffer, it can do a lot more
- genutils
- gitv
- gundo
    undo history and more
- indent-guides: use colorful block to display indent
- L9
- lion
- lookupfile
- mark
- markdown
    for markdown
- minibufexpl
- multiple-cursors
    can come in really handy... some learning curve here
- neocomplcache
- neosnippet : snippet plugin with auto completion.
- nerdcommenter
    (un)coment easily
- nerdtree
- nerdtree-tabs

- over
- Pathogen: allows me to install plugins in a cleaner manner.
- rainbow_parentheses
- repeat
- seek
- ShowMarks
- sneak
- speeddating
- SrcExpl
- surround
    adds/changes/deletes pairs like ""''(){}[] and html tags
- syntastic
    gives me syntax checking for many languages.
- systemc
- table-mode
- Tabular: allows me to align blocks of code.
- tagbar: better than taglist
- taglist
- unimpaired
- unite.vim : creates new interface with your customization.
- utl
- uvm_gen
- vcscommand
- verilog_systemverilog
- vim-addon-mw-utils
- vim-cycle
- vim-fugitive
- vim-perl
- vim-snippets
- vim-vertical-move
- vimwiki
- vis
- yankring
- Statusline
    * airline
    * lightline: sometimes I'm using Vim 7.2, use this to subsitute airline
    * lightline-powerful: powerful setting for lightline


#### [By topic](#by-topic-1)

- [Alignment](#alignment)
- [Building and linting](#building-and-linting)
- [Code completion](#code-completion)
- [Cycle](#cycle)
- [Commenters](#commenters)
- [Delimiter](#delimiter)
- [Fuzzy finders](#fuzzy-finders)
- [Grep tools](#grep-tools)
- [Indent](#indent)
- [Navigation](#navigation)
- [Snippets](#snippets)
- [Statusline](#statusline)
- [Surround](#surround)
- [Taking notes](#taking-notes)
- [Text objects](#text-objects)
- [Tmux](#tmux)
- [Undo history](#undo-history)
- [Version control](#version-control)
- [Writing](#writing)
- [Buffer](#buffer)
- [Misc](#misc)

#### [By filetype](#by-filetype-1)

- [C and C++](#c-and-c)
- [Clojure](#clojure)
- [HTML](#html)
- [Java](#java)
- [Javascript](#javascript)
- [Lua](#lua)
- [Python](#python)
- [TeX](#tex)
- [VimL](#viml)

### By topic

#### Plugin Management:
- [Pathogen]()
- [Vundle]()
- [NeoBundle]()
- [dein](https://github.com/Shougo/dein.vim)


#### Alignment

- [easy-align](https://github.com/junegunn/vim-easy-align)
- [tabular](https://github.com/godlygeek/tabular)
- [align]()
- [alignta]()
- [vim-lion]() : use `gl` and `gL` to insert space

#### Building and linting

- [ale](https://github.com/w0rp/ale)
- [neomake](https://github.com/neomake/neomake)
- [syntastic](https://github.com/scrooloose/syntastic)

#### Code completion

- [completor](https://github.com/maralla/completor.vim)
- [deoplete](https://github.com/Shougo/deoplete.nvim)
- [neocomplete](https://github.com/Shougo/neocomplete.vim) : need lua
- [neocomplcache](https://github.com/Shougo/neocomplcache.git)
- [supertab](https://github.com/ervandew/supertab) Do all your insert-mode completion with Tab.
- [VimCompletesMe](https://github.com/ajh17/VimCompletesMe)
- [youcompleteme](https://github.com/Valloric/YouCompleteMe)
- [mucomplete](https://github.com/lifepillar/vim-mucomplete)
- [AutoComplPop]()

#### mark

- [ShowMarks](https://github.com/bootleq/ShowMarks.git)


#### Cycle

- [speeddating](https://github.com/tpope/vim-speeddating) Ctrl+A and Ctrl+X for dates
- [switch](https://github.com/AndrewRadev/switch.vim)
- [vim-cycle](https://github.com/bootleq/vim-cycle.git)

#### Commenters

- [commentary](https://github.com/tpope/vim-commentary)
- [NerdCommenter](https://github.com/scrooloose/nerdcommenter) easy commenting of code for many filetypes.
- [tcomment](https://github.com/tomtom/tcomment_vim)
- [EnhCommentify]()


#### Delimiter

- [auto-pairs](https://github.com/jiangmiao/auto-pairs)
- [delimitmate](https://github.com/Raimondi/delimitMate) : automagically adds closing quotes and braces
- [endwise](https://github.com/tpope/vim-endwise)
- [rainbow_parentheses](https://github.com/kien/rainbow_parentheses.vim.git) : colorful parentheses

#### Fuzzy finders

- [command-t](https://github.com/wincent/Command-T) (_requires +ruby_)
- [ctrlp](https://github.com/ctrlpvim/ctrlp.vim.git) pure vimL

    provides a uniform fuzzy matching interface for files, buffers, tags, quickfix entries, recent files, changes

- [denite](https://github.com/Shougo/denite.nvim) (_requires +python3_)
- [fzf](https://github.com/junegunn/fzf) General purpose command-line fuzzy file finder that integrates with Vim.
- [unite](https://github.com/Shougo/unite.vim) : search and display information from arbitrary sources, like files, buffers, recently used files or registers
- [FuzzyFinder](https://github.com/vim-scripts/FuzzyFinder.git)


#### Grep tools

- [ctrlsf](https://github.com/dyng/ctrlsf.vim)
- [ferret](https://github.com/wincent/ferret)
- [grepper](https://github.com/mhinz/vim-grepper)

#### Indent

- [indent-guides](https://github.com/nathanaelkane/vim-indent-guides) visually displaying indent levels in Vim
- [indentline](https://github.com/Yggdroot/indentLine)

#### Navigation

- [dirvish](https://github.com/justinmk/vim-dirvish)
- [easymotion](https://github.com/easymotion/vim-easymotion)
- [sneak](https://github.com/justinmk/vim-sneak)
- [vinegar](https://github.com/tpope/vim-vinegar)
- [CamelCaseMotion](https://github.com/bkad/CamelCaseMotion.git)
- [seek]()
- [vim-vertical-move](https://github.com/bruno-/vim-vertical-move.git) : `,[`, `,]` for visual up and down select
- [file-line](https://github.com/vim-scripts/file-line.git)

Also see [fuzzy finders](#fuzzy-finders).

#### File Browser:
- [nerdtree](https://github.com/scrooloose/nerdtree)
- [nerdtree-tabs](https://github.com/jistr/vim-nerdtree-tabs.git)
- [vimfiler](https://github.com/Shougo/vimfiler.vim) (_depends on other plugins_)
- [SrcExpl](https://github.com/wesleyche/SrcExpl)


#### tag:

- [taglist](https://github.com/vim-scripts/taglist.vim.git)
- [tagbar](https://github.com/majutsushi/tagbar)
- [Gutentags](https://github.com/ludovicchabant/vim-gutentags) Tags file manager for your code references.


#### Snippets

- [neosnippet](https://github.com/Shougo/neosnippet.vim) (_depends on other plugins_)
- [snipmate](https://github.com/garbas/vim-snipmate) (_depends on other plugins_) TextMate-style snippets for Vim.
- [ultisnips](https://github.com/SirVer/ultisnips) Code snippets for boilerplate code.
- [xptemplate](https://github.com/drmingdrmer/xptemplate)
- [vim-snippets](https://github.com/honza/vim-snippets) : snippets collection


#### Statusline

- [airline](https://github.com/vim-airline/vim-airline)
- [flagship](https://github.com/tpope/vim-flagship)
- [lightline](https://github.com/itchyny/lightline.vim)
- [powerline](https://github.com/powerline/powerline)


#### Surround

- [operator-surround](https://github.com/rhysd/vim-operator-surround)
- [sandwich](https://github.com/machakann/vim-sandwich)
- [surround](https://github.com/tpope/vim-surround) Delete/change/add parentheses/quotes/XML-tags/much more with ease

#### Taking notes

- [dotoo](https://github.com/dhruvasagar/vim-dotoo)
- [journal](https://github.com/junegunn/vim-journal)
- [notes](https://github.com/xolox/vim-notes)
- [orgmode](https://github.com/jceb/vim-orgmode)
- [pad](https://github.com/fmoralesc/vim-pad)
- [vimwiki](https://github.com/vimwiki/vimwiki)

#### Text objects

- [exchange](https://github.com/tommcdo/vim-exchange)
- [targets](https://github.com/wellle/targets.vim)
- [textobj-user](https://github.com/kana/vim-textobj-user)

#### Tmux

- [dispatch](https://github.com/tpope/vim-dispatch)
- [tmux-complete](https://github.com/wellle/tmux-complete.vim)
- [tmux-navigator](https://github.com/christoomey/vim-tmux-navigator)
- [vitality](https://github.com/sjl/vitality.vim)

#### Undo history

- [gundo](https://github.com/sjl/gundo.vim)
- [undotree](https://github.com/mbbill/undotree)
- [yankring](https://github.com/vim-scripts/YankRing.vim.git)

#### Version control

- [agit](https://github.com/cohama/agit.vim)
- [committia](rhysd/committia.vim)
- [fugitive](https://github.com/tpope/vim-fugitive)
- [gist-vim](https://github.com/mattn/gist-vim)
- [gitgutter](https://github.com/airblade/vim-gitgutter)
- [github-dashboard](https://github.com/junegunn/vim-github-dashboard)
- [github-issues](https://github.com/jaxbot/github-issues.vim)
- [gitv](https://github.com/gregsexton/gitv)
- [gv](https://github.com/junegunn/gv.vim)
- [lawrencium](https://bitbucket.org/ludovicchabant/vim-lawrencium)
- [nerdtree-git-plugin](https://github.com/Xuyuanp/nerdtree-git-plugin)
- [signify](https://github.com/mhinz/vim-signify)
- [vimagit](https://github.com/jreybert/vimagit)
- [vcscommand]()
- [svnj](https://github.com/juneedahamed/svnj.vim)

#### Writing

- [grammarous](https://github.com/rhysd/vim-grammarous)
- [online-thesaurus](https://github.com/beloglazov/vim-online-thesaurus)

#### Buffer

- minibufexpl
- eunuch
    Delete or rename a buffer
- bufferline
    display buffer name in command line

#### Search and Replace:

- [multiple-cursors](https://github.com/terryma/vim-multiple-cursors) :  select all matching words and lets you concurrently change all matches at the same time
- [over](https://github.com/osyo-manga/vim-over) : substitute preview
- [abolish](https://github.com/tpope/vim-abolish) easily search for, substitute, and abbreviate multiple variants of a word.


#### library:

- tlib_vim


#### Misc

- [anzu]()
- [bracketed-paste](https://github.com/ConradIrwin/vim-bracketed-paste)
- [calendar](https://github.com/itchyny/calendar.vim)
- [covim](https://github.com/FredKSchott/CoVim)
- [devicons](https://github.com/ryanoasis/vim-devicons)
- [diminactive](https://github.com/blueyed/vim-diminactive)
- [fastfold](https://github.com/Konfekt/FastFold)
- [fixkey](https://github.com/drmikehenry/vim-fixkey)
- [gnupg](https://github.com/jamessan/vim-gnupg)
- [goyo](https://github.com/junegunn/goyo.vim)
- [hackernews](https://github.com/ryanss/vim-hackernews)
- [move](https://github.com/matze/vim-move)
- [nrrwrgn](https://github.com/chrisbra/NrrwRgn)
- [projectionist](https://github.com/tpope/vim-projectionist)
- [rsi](https://github.com/tpope/vim-rsi)
- [sideways](https://github.com/AndrewRadev/sideways.vim)
- [splitjoin](https://github.com/AndrewRadev/splitjoin.vim)
- [startify](https://github.com/mhinz/vim-startify)
- [targets](https://github.com/wellle/targets.vim)
- [unicode.vim](https://github.com/chrisbra/unicode.vim)
- [unimpaired](https://github.com/tpope/vim-unimpaired)
- [vim-sensible](https://github.com/tpope/vim-sensible) Default setting that everyone can agree on
- [vim-workspace](https://github.com/thaerkh/vim-workspace) persist files in your workspace session, persist their undo history, autosave, untrail spaces, and more!

### By filetype

#### C and C++

- [a](https://github.com/vim-scripts/a.vim) Alternate Files quickly (.c --> .h etc)
- [c.vim](http://www.vim.org/scripts/script.php?script_id=213) C/C++ IDE.
- [clang_complete](https://github.com/Rip-Rip/clang_complete)
- [color_coded](https://github.com/jeaye/color_coded.git)
- [lh-cpp](https://github.com/LucHermitte/lh-cpp)

#### Clojure

- [clojure-highlight](https://github.com/guns/vim-clojure-highlight)
- [fireplace](https://github.com/tpope/vim-fireplace)
- [paredit](https://github.com/kovisoft/paredit)
- [rainbow_parentheses](https://github.com/junegunn/rainbow_parentheses.vim)
- [salve](https://github.com/tpope/vim-salve)
- [sexp-mappings-for-regular-people](https://github.com/tpope/vim-sexp-mappings-for-regular-people)
- [sexp](https://github.com/guns/vim-sexp)

#### HTML

- [emmet](https://github.com/mattn/emmet-vim)
- [html5](https://github.com/othree/html5.vim)

#### Java

- [javacomplete2](https://github.com/artur-shaik/vim-javacomplete2)

#### Javascript

- [es.next.syntax](https://github.com/othree/es.next.syntax.vim)
- [esformatter](https://github.com/millermedeiros/vim-esformatter)
- [javascript-libraries-syntax](https://github.com/othree/javascript-libraries-syntax.vim)
- [javascript-syntax](https://github.com/jelera/vim-javascript-syntax)
- [javascript](https://github.com/pangloss/vim-javascript)
- [node-vim-debugger](https://github.com/sidorares/node-vim-debugger)
- [node](https://github.com/moll/vim-node)
- [tern_for_vim](https://github.com/ternjs/tern_for_vim)
- [yajs](https://github.com/othree/yajs.vim)

#### Lua

- [lua-ftplugin](https://github.com/xolox/vim-lua-ftplugin)
- [lua-inspect](https://github.com/xolox/vim-lua-inspect)

#### Python

- [braceless](https://github.com/tweekmonster/braceless.vim)
- [flake8](https://github.com/nvie/vim-flake8)
- [impsort](https://github.com/tweekmonster/impsort.vim)
- [jedi](https://github.com/davidhalter/jedi-vim)
- [python-mode](https://github.com/klen/python-mode)

#### TeX

- [vimtex](https://github.com/lervag/vimtex)

#### VimL

- [scriptease](https://github.com/tpope/vim-scriptease)  A Vim plugin for Vim plugins


### ColorScheme

    * badwolf
    * cs-gruvbox
    * cs-kolor
    * cs-peaksea
    * desertink
    * inkpot
    * irblack
    * molokai
    * solarized
    * skittles_berry
    * vim-hybrid
    * vim-vombato
    * vividchalk
    * zenburn


## Visual-block:
* VisIncr
* niceblock
    better editing in visual mode
* vis

## syntax:
* markdown
* vim-perl
* uvm_gen
* vim-orgmode
* c

## Draw:
* DrawIt
* table-mode

repeat: repeat plugin commands
matchit: makes your % more awesome, extended % matching for HTML, LaTeX, and many other languages
signify: adds + and - to the signs column when changes are detected to source control files (supports git/hg/svn)
startify: gives you a better start screen
ColorV: is a color view/pick/edit/design/scheme tool
ScrollColor, csExplorer: explorer colorschemes
Conque-Shell: is a Vim plugin which allows you to run interactive programs, such as bash on linux or powershell.exe on Windows, inside a Vim buffer
file-line: open the file under cursor, and goto the line specified after the filename
headlights: add a menu to vim, revealing all plugins used



[![Bitdeli Badge](https://d2weczhvl823v0.cloudfront.net/kinghom/mydotvim/trend.png)](https://bitdeli.com/free "Bitdeli Badge")

