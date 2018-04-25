"*******************************************************************************
" Filename:          _vimrc
" Author:            Hong Jin - hon9jin@gmail.com
" Description:       Vim configuration file
"
"******************************************************************************/

let g:vimrc_loaded = 1
" Set which part to load
let g:load_vimrc_filetype = 1
let g:load_vimrc_plugin_config = 1
let g:load_vimrc_extended = 1

"-----------------------------------------------------------
" Platform
"-----------------------------------------------------------
" Identify platform {{{
  function! MySys()
    if has("win16") || has("win32") || has("win64") || has("win95")
      return "windows"
    elseif has('win32unix')
      return "cygwin"
    elseif has('gui_macvim')
      return "mac"
    else
      return "linux"
    endif
  endfunction

  let s:os = MySys()
" }}}

" Local variables {{{
  let g:dotvim_settings = {}
  " change the default directory where all miscellaneous persistent files go
  let g:dotvim_settings.cache_dir=$HOME.'/.vim-cache'

  " auto complete:
  "      neocomplete: if (v:version > 703 || (v:version == 703 && has('patch885'))) && has('lua')
  "      neocomplcache
  "      vimcompletesme
  "      mucomplete
  let g:dotvim_settings.autocomplete_method = 'vimcompletesme'

  " fuzzy finder
  let g:dotvim_settings.finder_method = 'ctrlp' " if v:version < 703

  " snippets:
  "   neosnippet
  "   ultisnips
  "   snipmate
  let g:dotvim_settings.snippet_method = 'snipmate'

  " statusline:
  "   lightline : if v:version < 702
  "   airline
  let g:dotvim_settings.statusline_method = 'lightline'

" }}}

"---------------------------------------------------------------
"""""""""""""""""""""" Basic {{{
"---------------------------------------------------------------
"  1 important
"----------------------------------------------------------------
" set all& "reset everything to their defaults

" Get out of VI's compatible mode
" Use Vim settings, rather then Vi settings.
" This must be first, because it changes other options as a side effect.
set nocompatible                " not use vi keyboard mode

if s:os == "windows"
  set runtimepath+=$HOME/.vim,$HOME/.vim/after
endif

filetype off

let g:path_of_vimrc_tmp = fnamemodify(resolve(expand('<sfile>')), ':p:h')
let g:path_of_vimrc = substitute(g:path_of_vimrc_tmp, "\\", "/", "g")
if s:os == "windows"
  let g:vimfiles = g:path_of_vimrc.'/vimfiles'
else
  let g:vimfiles = g:path_of_vimrc.'/.vim'
endif

"-----------------------------------------------------------
  """ vim-plug {{{
  " Specify a directory for plugins
  " - For Neovim: ~/.local/share/nvim/plugged
  " - Avoid using standard Vim directory names like 'plugin'
  " silent! if plug#begin(g:path_of_vimrc.'/vimfiles/plugged')
  if s:os == "windows"
    call plug#begin(g:path_of_vimrc.'/vimfiles/plugged')
  else
    call plug#begin('~/.vim/plugged')
  endif
  " Make sure you use single quotes

  """ Alignment
  " Shorthand notation; fetches https://github.com/junegunn/vim-easy-align
  Plug 'junegunn/vim-easy-align'
  Plug 'godlygeek/tabular'
  Plug 'tommcdo/vim-lion'

  """ Code completion
  if g:dotvim_settings.autocomplete_method == 'vimcompletesme'
    Plug 'ajh17/VimCompletesMe'
  elseif g:dotvim_settings.autocomplete_method == 'neocomplcache'
    Plug 'Shougo/neocomplcache'
  elseif g:dotvim_settings.autocomplete_method == 'neocomplete'
    Plug 'Shougo/neocomplete.vim'
  else
    Plug 'lifepillar/vim-mucomplete', {'on': 'MUcompleteAutoToggle'}
  endif

  " Colorscheme
  Plug 'sjl/badwolf'
  Plug 'jnurmine/Zenburn'
  Plug 'altercation/vim-colors-solarized'
  Plug 'ajmwagar/vim-deus'
  Plug 'morhetz/gruvbox'
  Plug 'tpope/vim-vividchalk'
  Plug 'tomasr/molokai'
  Plug 'chriskempson/vim-tomorrow-theme'
  Plug 'morhetz/gruvbox'
  Plug 'yuttie/hydrangea-vim'
  Plug 'tyrannicaltoucan/vim-deep-space'
  Plug 'AlessandroYorba/Despacio'
  Plug 'w0ng/vim-hybrid'

  """ Cycle
  Plug 'tpope/vim-speeddating'

  """ Commenters
  Plug 'scrooloose/nerdcommenter'

  """ Delimiter
  Plug 'Raimondi/delimitMate'
  Plug 'luochen1990/rainbow'

  """ Fuzzy finders
  Plug 'ctrlpvim/ctrlp.vim'
  Plug 'sgur/ctrlp-extensions.vim'
  " Plug 'Yggdroot/LeaderF', { 'do': './install.sh' }

  """ Indent
  Plug 'nathanaelkane/vim-indent-guides', {'on': ['IndentGuidesToggle', 'IndentGuidesEnable']}
  Plug 'Yggdroot/indentLine', { 'on': 'IndentLinesEnable' }

  """ Navigation
  Plug 'scrooloose/nerdtree', { 'on': 'NERDTreeToggle' }
  Plug 'jistr/vim-nerdtree-tabs'
  if v:version >= 703
    Plug 'majutsushi/tagbar', { 'on': 'TagbarToggle' }
  endif
  Plug 'Lokaltog/vim-easymotion'
  Plug 'justinmk/vim-sneak'
  Plug 'bkad/CamelCaseMotion'

  """ Snippets
  if g:dotvim_settings.snippet_method == 'snipmate' " neosnippet/ultisnips
    Plug 'MarcWeber/vim-addon-mw-utils'
    Plug 'tomtom/tlib_vim'
    Plug 'garbas/vim-snipmate'
  elseif g:dotvim_settings.snippet_method == 'neosnippet'
    Plug 'Shougo/neosnippet'
    Plug 'Shougo/neosnippet-snippets'
  endif
  Plug 'honza/vim-snippets'

  """ Statusline
  " Plug 'bling/vim-airline'
  Plug 'itchyny/lightline.vim'
  " Plug 'tpope/vim-flagship'

  """ Surround
  Plug 'tpope/vim-surround'

  """ Undo history
  Plug 'mbbill/undotree', { 'on': 'UndotreeToggle' }

  """ Version control
  if v:version >= 703
    Plug 'mhinz/vim-signify', {'on': ['SignifyToggle', 'SignifyEnable'] }
  endif

  """ VimL
  Plug 'tpope/vim-scriptease'

  """ Misc
  " Plug 'fholgado/minibufexpl.vim', { 'on': 'MBEOpen' }
  Plug 'jlanzarotta/bufexplorer', { 'on': ['BufExplorer', 'ToggleBufExplorer'] }
  Plug 'Konfekt/FastFold'
  Plug 'bootleq/ShowMarks'
  Plug 'bruno-/vim-vertical-move'
  Plug 'gcmt/wildfire.vim'
  Plug 'hallison/vim-markdown'
  Plug 'haya14busa/incsearch.vim'
  Plug 'haya14busa/vim-asterisk'
  Plug 'itchyny/calendar.vim'
  Plug 'kana/vim-niceblock'
  Plug 'osyo-manga/vim-anzu'
  Plug 'osyo-manga/vim-over'
  Plug 'terryma/vim-expand-region'
  Plug 'terryma/vim-multiple-cursors'
  Plug 'tpope/vim-abolish'
  Plug 'tpope/vim-repeat'
  Plug 'tpope/vim-unimpaired'
  Plug 'vim-scripts/VisIncr'
  Plug 'vim-scripts/YankRing.vim'
  Plug 'vimtaku/hl_matchit.vim'

  """ Verilog/SystemVerilog
  Plug 'sychen/vim-systemverilog', {'as': 'sychen-systemverilog'}
  Plug 'kinghom/uvm_gen', { 'for': ['systemverilog', 'verilog'] }

  " Unmanaged plugin (manually installed and updated)

  " Initialize plugin system
  call plug#end()
" }}}

"-----------------------------------------------------------
" FileType Detecting
" Enable file type detection. Use the default filetype settings.
" Also load indent files, to automatically do language-dependent indenting.
"-----------------------------------------------------------
if has('autocmd')
  filetype plugin indent on
  filetype indent on        " load filetype-specific indent files
endif

if s:os == "windows"
  language message en                   " message language
  " language message en_US                   " message language
  " language message zh_CN.UTF-8
  " lang messages zh_CN.UTF-8 "
elseif s:os == "linux"
  language message C
endif

" source $VIMRUNTIME/vimrc_example.vim
if s:os == "windows"
  " source $VIMRUNTIME/mswin.vim      " Win behaviour
endif

runtime! ftplugin/man.vim

" our <leader> will be the space key
let mapleader = ","
" let mapleader=" "

" our <localleader> will be the '-' key
let maplocalleader=","

" Avoid garbled characters in Chinese language windows OS
let $LANG='en'
set langmenu=en
source $VIMRUNTIME/delmenu.vim
source $VIMRUNTIME/menu.vim

"-----------------------------------------------------------
" Switch syntax highlighting on.
"-----------------------------------------------------------
if has('syntax') && !exists('g:syntax_on')
  syntax enable
endif

" Switch syntax highlighting on, when the terminal has colors
if &t_Co > 2 || has("gui_running")
  syntax on
endif

"-------------------------------------------------------------------------------
"  2 moving around, searching and patterns
"-------------------------------------------------------------------------------
" set whichwrap+=<,>,[,]      " Allow wrap only when cursor keys are used
if s:os == "windows"
  set path+=D:\cygwin\bin
elseif s:os == "linux"
  set path+=/usr/bin
endif
if has("gui_running")
  if has("gui_win32")     " Win OS
    set wrap            " Wrap line
"   elseif has("x11")
"   elseif has("gui_gtk2")
  endif

  set columns=135

else
  set wrap
endif

set autochdir          " Change the current working dir whenever open a file,
                       " switch buffers, delete a buffer, open/close a window

set nowrapscan      " Don't Searches wrap around the end of the file

" Sets how many lines of history VIM has to remember
if &history < 1000
  set history=1000
endif

"-----------------------------------------------------------
"Replace/Search
"-----------------------------------------------------------
set hlsearch        " Highlight matched result when searching
set incsearch       " Show the pattern when typing a search command
set ignorecase      " Ignore cases
set smartcase       "
set magic           " Changes the special characters that can be used in search patterns

" Use grep.
if executable('ack')
  set grepprg=ack\ --nogroup\ --column\ --smart-case\ --nocolor\ --follow\ $*
elseif executable('ag')
  set grepprg=ag\ --nogroup\ --column\ --smart-case\ --nocolor\ --follow
else
  set grepprg=grep\ -nH
endif
let g:grep_cmd_opts = '--line-number'
set grepformat=%f:%l:%c:%m

if v:version >= 704
  " The new Vim regex engine is currently slooooow as hell which makes syntax
  " highlighting slow, which introduces typing latency.
  " Consider removing this in the future when the new regex engine becomes
  " faster.
  set regexpengine=1
endif

"-------------------------------------------------------------------------------
"  3 tags
"-------------------------------------------------------------------------------
" ctags path
if s:os == "windows"
  let g:dotvim_settings.ctags_path = g:vimfiles . '/ctags/ctags.exe'
elseif s:os == "linux"
  let g:dotvim_settings.ctags_path='ctags'
endif

if has('path_extra')
  set tags+=./tags,./../tags,./**/tags,tags " which tags files CTRL-] will find
  " setglobal tags-=./tags tags-=./tags; tags^=./tags;
endif
"-------------------------------------------------------------------------------

"  4 displaying text
"-------------------------------------------------------------------------------
set linebreak               " wrap at the right place
set breakat=\ \ ;:,!?
set showbreak=>
set display+=lastline
" set fillchars=vert:\ ,stl:\ ,stlnc:\  " Characters to fill the statuslines and vertical separators
set fillchars=stl:-,stlnc:\ ,diff:-,vert:\|  " Characters to fill the statuslines and vertical separators
set cmdheight=1                 " heighth of CMD line
set list                        " list mode

if has('multi_byte') && &encoding ==# 'utf-8'
  let &listchars = 'tab:▸ ,trail:-,extends:❯,precedes:❮,nbsp:±'
else
  let &listchars = 'tab:> ,trail:-,extends:>,precedes:<,nbsp:.'
endif

set number                      " display line number
" set relativenumber              " show relative numbers
set numberwidth=1
set lazyredraw                  " Don't redraw while executing macros

"-------------------------------------------------------------------------------
"  5 syntax, highlighting and spelling
"-------------------------------------------------------------------------------
set background=dark
" Allow to trigger background
function! ToggleBG()
    let s:tbg = &background
    " Inversion
    if s:tbg == "dark"
        set background=light
    else
        set background=dark
    endif
endfunction
noremap <leader>bg :call ToggleBG()<CR>


"-------------------------------------------------------------------------------
"  6 multiple windows
"-------------------------------------------------------------------------------

set equalalways " Multiple windows, when created, are equal in size
" Open new split panes to right and bottom, which feels more natural
set splitbelow
set splitright
" Adjust window size of preview and help.
set previewheight=10
set helpheight=12

"-------------------------------------------------------------------------------
"  7 multiple tab pages
"-------------------------------------------------------------------------------
set showtabline=1
if &tabpagemax < 50
  set tabpagemax=50
endif

"-------------------------------------------------------------------------------
"  8 terminal
"-------------------------------------------------------------------------------
" set title                       " display title

"-------------------------------------------------------------------------------
"  9 using the mouse
"-------------------------------------------------------------------------------
"-----------------------------------------------------------
" Mouse
"-----------------------------------------------------------
if s:os == "windows"
  set mouse=a
elseif s:os == "linux"
  set mouse=va
endif
" set mousemodel=extend
set nomousehide                 " Hide the mouse when typing text

" cursor
let &t_SI = "\<Esc>]50;CursorShape=1\x7"
let &t_EI = "\<Esc>]50;CursorShape=0\x7"

"-------------------------------------------------------------------------------
" 10 GUI
"-------------------------------------------------------------------------------
set browsedir=current           " which directory to use for the file browser

"-------------------------------------------------------------------------------
" 11 printing
"-------------------------------------------------------------------------------

"-------------------------------------------------------------------------------
" 12 messages and info
"-------------------------------------------------------------------------------
set shortmess+=atoOIT           " To avoid some hint messages
if has('cmdline_info')
  set ruler                     " Show the line and column number of the cursor position
  " set rulerformat=%30(%2*%<%f%=\ %m%r\ %3l\ %c\ %p%%%) " determines the content of the ruler string
  set rulerformat=%30(%=\:b%n%y%m%r%w\ %l,%c%V\ %P%) " a ruler on steroids"
  set showcmd                     " display incomplete commands
endif
set report=0                    " Threshold for reporting number of lines changed
set noerrorbells                " No bell for error messages
set novisualbell                " Use visual bell instead of beeping
set t_vb=                       " Disable screen flash on error
" set helplang& helplang=en
" use Chinese help, support in vimcdoc.vim plugin
if version >= 603
  if s:os == "windows"
    set helplang=cn
  else
    set helplang=en
  endif
endif

"-------------------------------------------------------------------------------
" 13 selecting text
"-------------------------------------------------------------------------------
set selection=inclusive         " defines the behavior of the selection
set selectmode=mouse            " when use mouse, launch SELECT mode
set keymodel=startsel           " Shift + arrow key
" set selectmode=key
"-----------------------------------------------------------
""" ClipBoard
"-----------------------------------------------------------
" Use clipboard register.
" set clipboard+=unnamed
if has('clipboard')
  if has('unnamedplus')
    " By default, Vim will not use the system clipboard when yanking/pasting to
    " the default register. This option makes Vim use the system default
    " clipboard.
    " Note that on X11, there are _two_ system clipboards: the "standard" one, and
    " the selection/mouse-middle-click one. Vim sees the standard one as register
    " '+' (and this option makes Vim use it by default) and the selection one as
    " '*'.
    " See :h 'clipboard' for details.
    set clipboard=unnamedplus,unnamed
  else
    " Vim now also uses the selection system clipboard for default yank/paste.
    set clipboard+=unnamed
  endif
endif

"-------------------------------------------------------------------------------
" 14 editing text
"-------------------------------------------------------------------------------
set backspace=indent,start,eol  " BACKSPACE behavior
set formatoptions+=mM       " describes how automatic formatting is to be done
if v:version > 703 || v:version == 703 && has("patch541")
  set formatoptions+=j " Delete comment character when joining commented lines
endif
set showmatch       " Highlight matched pairs
set matchtime=5     " Tenths of a second to show the matching paren
set matchpairs+=<:>
"-----------------------------------------------------------
" Auto Complete Word
"-----------------------------------------------------------
" options
set complete-=u
set complete-=i
set complete+=.,w,b,kspell,ss   " current buffer, other windows' buffers, dictionary, spelling
set complete+=k                 " scan the files given with the 'dictionary' option
set completeopt=longest         " Insert mode completetion
set completeopt+=menuone        " Insert mode completetion
" Set popup menu max height.
set pumheight=20

"-------------------------------------------------------------------------------
" 15 tabs and indenting
"-------------------------------------------------------------------------------
set tabstop=4               " TAB width
set softtabstop=4           " Soft TAB width
set shiftwidth=4            " Number of spaces to use for each step of (auto)indent, for cindent
set expandtab               " use SPACE instead of TAB
set smarttab                " use SPACE instead of TAB at start of line
set shiftround              " Round indent by shiftwidth

"-----------------------------------------------------------
" Indent
"-----------------------------------------------------------
set autoindent              " Copy indent from current line when starting a new line
set cindent                 " Enables automatic C program indenting
set copyindent              " copy the previous indentation on autoindenting

"-------------------------------------------------------------------------------
" 16 folding
"-------------------------------------------------------------------------------
" set foldenable              " turn on folding
set foldenable            " disable folding
if exists("&foldlevel")
  set foldlevel=999           " make it really high, so they're not displayed by default
endif
set foldmarker={,}
set foldmethod=indent       " Make folding indent sensitive  // syntax
set foldnestmax=5
set foldcolumn=2            " width for fold
set foldlevelstart=1000     " fdls:  fold level start
set foldopen=block,hor,insert,jump,mark,percent,quickfix,search,tag,undo

"-------------------------------------------------------------------------------
" 17 diff mode
"-------------------------------------------------------------------------------
set diffopt=context:3       " display 3 lines above and below the different place
set diffopt+=iwhite
set diffopt+=filler
" if os == "windows"
  set diffexpr=MyDiff()
  function! MyDiff()
    let opt = '-a --binary '
    if &diffopt =~ 'icase'
      let opt = opt . '-i '
    endif
    if &diffopt =~ 'iwhite'
      let opt = opt . '-b '
    endif
    let arg1 = v:fname_in
    if arg1 =~ ' '
      let arg1 = '"' . arg1 . '"'
    endif
    let arg2 = v:fname_new
    if arg2 =~ ' '
      let arg2 = '"' . arg2 . '"'
    endif
    let arg3 = v:fname_out
    if arg3 =~ ' '
      let arg3 = '"' . arg3 . '"'
    endif
    let cmd = '!diff ' . opt . arg1 . ' ' . arg2 . ' > ' . arg3
    silent execute cmd
    " let eq = ''
    " if $VIMRUNTIME =~ ' '
    "     if &sh =~ '\<cmd'
    "     let cmd = '""' . $VIMRUNTIME . '\diff"'
    "     let eq = '"'
    " else
    "     let cmd = substitute($VIMRUNTIME, ' ', '" ', '') . '\diff"'
    " endif
    " else
    "     let cmd = $VIMRUNTIME . '\diff'
    " endif
    " silent execute '!' . cmd . ' ' . opt . arg1 . ' ' . arg2 . ' > ' . arg3 . eq
  endfunction
" endif

"-------------------------------------------------------------------------------
" 18 mapping
"-------------------------------------------------------------------------------

"-------------------------------------------------------------------------------
" 19 reading and writing files
"-------------------------------------------------------------------------------
set nobackup                    " no backup file
set nowritebackup               " no backup before rewrite file
"set backupdir=E:\bak
if exists("&autoread")
  set autoread                    " autoload when file changed outside vim
endif
set autowrite                   " write a modified buffer on each :next
" Default fileformat
set fileformat=unix
" Automatic recognition of a new line cord
set fileformats=unix,dos,mac
nnoremap <leader>fd :se ff=dos<cr>
nnoremap <leader>fu :se ff=unix<cr>

" undo
" persistent undo
if exists('+undofile')
  set undofile
  " let &undodir = s:get_cache_dir('undo')
  " set undodir=$HOME.'/.vim-cache/undodir'
  set undodir=g:dotvim_settings.cache_dir.'/undodir'
endif

"-------------------------------------------------------------------------------
" 20 the swap file
"-------------------------------------------------------------------------------
"set directory=E:\bak
set noswapfile
" CursorHold time
set updatetime=1000

set nrformats-=octal

set ttimeout
set ttimeoutlen=100

"-------------------------------------------------------------------------------
" 21 command line editing
"-------------------------------------------------------------------------------
set wildmode=list:longest,full  " command <Tab> completion, list matches, then longest common part, then all"
set wildignore+=.svn,CVS,.git,.hg,*.bak,*.e,*.obj,*.swp,*.pyc,*.o,*.lo,*.la,*.exe,*.db,*.old,*.mdb,*~,~*,*.so " wildmenu: ignore these extensions
if s:os == "windows"
  set wildignore+=*/.git/*,*/.hg/*,*/.svn/*,*/CVS/*,*/.DS_Store
else
  set wildignore+=.git\*,.hg\*,.svn\*,CVS\*
endif
set wildmenu                    " command-line autocompletion operates in an enhanced mode

"-------------------------------------------------------------------------------
" 22 executing external commands
"-------------------------------------------------------------------------------
" Set keyword help.
set keywordprg=:help

"-------------------------------------------------------------------------------
" 23 running make and jumping to errors
"-------------------------------------------------------------------------------
" programming related
set makeef=error.err " the errorfile for :make and :grep

"-------------------------------------------------------------------------------
" 24 system specific
"-------------------------------------------------------------------------------
if s:os == "windows"
  if exists('+shellslash')
    set shellslash      " Exchange path separator
  endif
endif

"-------------------------------------------------------------------------------
" 25 language specific
"-------------------------------------------------------------------------------
" none of these should be word dividers, so make them not be
set iskeyword+=_,$,@,%,#,-
set isfname-==  " remove = from filename characters

"-------------------------------------------------------------------------------
" 26 multi-byte characters
"-------------------------------------------------------------------------------
if has("multi_byte")

  " Windows cmd.exe still uses cp850. If Windows ever moved to
  " Powershell as the primary terminal, this would be utf-8
  " set termencoding=cp850
  if &termencoding == ""
    let &termencoding = &encoding
  endif
  " Let Vim use utf-8 internally, because many scripts require this
  "set encoding=utf-8
  " setglobal fileencoding=utf-8
  " Windows has traditionally used cp1252, so it's probably wise to
  " fallback into cp1252 instead of eg. iso-8859-15.
  " Newer Windows files might contain utf-8 or utf-16 LE so we might
  " want to try them first.
  set fileencodings=ucs-bom,utf-8,cp936,gb18030,cp1252,big5,euc-jp,euc-kr,latin1
else
  echoerr "Sorry, this version of (g)vim was not compiled with multi_byte"
endif

"-------------------------------------------------------------------------------
" 27 various
"-------------------------------------------------------------------------------
" set virtualedit=onemore         " allow for cursor beyond last character
set virtualedit+=block          " Enable virtualedit in visual block mode
" set viminfo='50,<1000,:50,n$VIM/.viminfo     " save session
set viminfo='50,<1000,:50     " save session
if !empty(&viminfo)
  set viminfo^=!
endif
set viewoptions=folds,options,cursor,unix,slash " better unix / windows compatibility

" Session options
"-----------------------------------------------------------
set sessionoptions-=curdir
set sessionoptions+=sesdir
set sessionoptions-=options

function! MyHighlights() abort
  " highlight Visual     cterm=NONE ctermbg=76  ctermfg=16  gui=NONE guibg=#5fd700 guifg=#000000
  " highlight StatusLine cterm=NONE ctermbg=231 ctermfg=160 gui=NONE guibg=#ffffff guifg=#d70000
  " highlight Normal     cterm=NONE ctermbg=17              gui=NONE guibg=#00005f
  " highlight NonText    cterm=NONE ctermbg=17              gui=NONE guibg=#00005f

  highlight OverLength  ctermbg=red ctermfg=white   guibg=red     guifg=white
  highlight Pmenu       ctermbg=8                   guibg=#606060
  highlight PmenuSel    ctermbg=1                   guifg=#dddd00 guibg=#1f82cd
  highlight PmenuSbar   ctermbg=0                   guibg=#d6d6d6
  "
  "highlight StatusLine guifg=SlateBlue guibg=Yellow
  "highlight StatusLine guifg=SlateBlue guibg=#008800
  highlight StatusLine NONE
  highlight StatusLineNC NONE
  " current window
  highlight StatusLine ctermfg=yellow     guifg=orange guibg=#008800 gui=underline
  " highlight StatusLine guifg=orange guibg=#008800 gui=underline term=bold cterm=bold ctermfg=yellow
  " not current window
  highlight StatusLineNC ctermfg=lightgrey guifg=Gray guibg=white
  " highlight StatusLineNC guifg=Gray guibg=white ctermfg=gray ctermbg=white
  highlight User1 guifg=yellow
  highlight User2 guifg=lightblue
  highlight User3 guifg=red
  highlight User4 guifg=cyan
  highlight User5 guifg=lightgreen
  highlight User6 gui=bold,inverse guifg=red term=bold,inverse ctermfg=blue
  highlight User7 gui=bold,inverse guifg=red term=bold,inverse cterm=bold ctermfg=green ctermbg=red
endfunction

augroup MyColors
    autocmd!
    autocmd ColorScheme * call MyHighlights()
augroup END

":match OverLength '\%200v.*'

if v:version > 703
  set cryptmethod=blowfish
endif

" Specify the behavior when switching buffers
try
  " set switchbuf=useopen,usetab,newtab
  set switchbuf=usetab,usetab     " Open new buffers always in new tabs
  " set showtabline=2
  catch
endtry

" Scroll options
if !&scrolloff
  set scrolloff=2
endif
if !&sidescrolloff
  set sidescrolloff=10
endif
set sidescroll=1

"-----------------------------------------------------------
" AutoCommands
"-----------------------------------------------------------
if has("autocmd") " {{{
  " Set augroup
  augroup MyAutoCmd
    autocmd!

    " automatically rebalance windows on vim resize
    autocmd VimResized * :wincmd =

    " Check timestamp more for 'autoread'.
    autocmd WinEnter * checktime

    autocmd BufReadPre,BufNewFile,BufRead *.do,*.tree setfiletype tcl
    autocmd BufReadPre,BufNewFile,BufRead *.log setfiletype txt nowrap
    autocmd BufReadPre,BufNewFile,BufRead *.rpt setfiletype txt nowrap
    autocmd BufRead,BufNewFile *.txt setfiletype txt " highlight TXT file

    " Make sure Vim returns to the same line when you reopen a file.
    autocmd BufReadPost *
        \ if line("'\"") > 0 && line("'\"") <= line("$") |
        \     execute 'normal! g`"zvzz' |
        \ endif

    autocmd BufEnter * :syntax sync fromstart
    autocmd BufEnter * :lchdir %:p:h

    " auto load vimrc when editing it
    " if os == "windows"
    "     autocmd! bufwritepost _vimrc source $VIM/_vimrc
    " elseif os == "linux"
    "     autocmd! BufWritePost .vimrc source %
    " endif

    " Automatically delete trailing DOS-returns and whitespace on file open and write.
    " autocmd BufRead,BufWritePre,FileWritePre * silent! %s/[\r \t]\+$//

    " Automatically resize vertical splits
    " autocmd WinEnter * :set winfixheight
    " autocmd WinEnter * :wincmd =

    autocmd BufNewFile,BufRead .tmux.conf*,tmux.conf* setf tmux
    autocmd FileType css,scss setlocal foldmethod=marker foldmarker={,}
    autocmd FileType css,scss nnoremap <silent> <leader>S vi{:sort<CR>
    autocmd FileType markdown setlocal nolist
    autocmd FileType vim setlocal fdm=indent keywordprg=:help
    autocmd FileType verilog_systemverilog,verilog,systemverilog setlocal autoindent
    autocmd FileType html,text,php,vim,c,java,xml,bash,shell,perl,systemverilog,verilog_systemverilog,vimwiki set textwidth=80
    autocmd FileType bash,shell set ts=2
    autocmd FileType help set nonu
    autocmd FileType lisp set ts=2 softtabstop=2
  augroup END
endif " }}}

"-----------------------------------------------------------
" Highlight current Line
"-----------------------------------------------------------
"highlight CurrentLine guibg=#4D4D4D         "848284     "guifg=white
"au! Cursorhold * exe 'match CurrentLine /\%' . line('.') . 'l.*/'

"-----------------------------------------------------------
" Abbreviations
"-----------------------------------------------------------

"-----------------------------------------------------------
""" Status Line
"-----------------------------------------------------------
" Color of Status Line
if has('statusline') " {{{
  set laststatus=2           " always show the status line
  " set statusline=[Format=%{&ff}]\ [Type=%Y]\ [Pos=%l,%v][%p%%]\ %{strftime(\"%H:%M\")}
  " set statusline=[Format=%{&ff}]\ [Type=%Y]%1*%m%*%r%h%w%=[Pos=%l,%v][%l/%L(%p%%)]
  " set statusline=[%f][Format=%{&ff}]%{'['.(&fenc!=''?&fenc:&enc).']'}%y%1*%m%*%r%h%w%=[Pos=%l,%v][%l/%L(%p%%)]
  " %([%R%M]%)   read-only, modified and modifiable flags between braces
  " %{'$'[!&list]}  shows a '$' if in list mode
  " %{'~'[&pm=='']} shows a '~' if in patchmode
  " #%n    buffer number
  set statusline=
  set statusline+=[%f]                " file name
  set statusline+=[%{&ff}]            " file format
  set statusline+=%{'['.(&fenc!=''?&fenc:&enc).']'}
  set statusline+=%y                  " file type
  set statusline+=%7*%m%*             " modified flag
  set statusline+=%r                  " readonly flag
  set statusline+=%h                  "
  set statusline+=%w
  " set statusline+=\ [%{getcwd()}] " current directory
  set statusline+=%#warningmsg#
  set statusline+=%=                  " left/right separator
  set statusline+=%6*%b(0X%B)
  " set statusline+=[Pos=%l,%c%V]
  set statusline+=[(%l,%c%V)/%L(%p%%)]%*       " cursor position
endif " }}}

" GUI Options {{{
  " set guioptions+=grTt
  set guioptions-=T
  " don't use autoselect on OS X
  if has('mac')
    set guioptions-=a
  endif
  " For CTRL-v to work autoselect must be off.
  " On Unix we have two selections, autoselect can be used.
  if !has('unix')
    set guioptions-=a
  endif

  if has("gui_win32")     " Win
    set guioptions+=bh  " Horizontal scrolbar
  endif
  set guioptions-=e
" }}}

" Font {{{
  " set default guifont
  if has("gui_running")
    " check and determine the gui font after GUIEnter.
    " NOTE: getfontname function only works after GUIEnter.
    au GUIEnter * call s:SetGuiFont()
  endif

  " set guifont
  function s:SetGuiFont()
    if has('mac')
      if getfontname( "Bitstream_Vera_Sans_Mono" ) != ""
        set guifont=Bitstream\ Vera\ Sans\ Mono:h12
      elseif getfontname( "DejaVu\ Sans\ Mono" ) != ""
        set guifont=DejaVu\ Sans\ Mono:h12
      elseif getfontname( "Menlo\ Regular" ) != ""
        set guifont=Menlo\ Regular:h12
      endif
    elseif has('unix')
      " set guifont=WenQuanYi\ Micro\ Hei\ Mono\ 10
      set guifont=Monospace\ 10
      set guifontwide=WenQuanYi\ Micro\ Hei\ Mono\ 10
    elseif has("gui_win32")     " Windows platform
      let font_name = ""
      if getfontname( "Consolas" ) != ""
        set guifont=Consolas:h11:cANSI " this is the default visual studio font
        let font_name = "Consolas"
      elseif getfontname( "Source_Code_Pro" ) != ""
        set guifont=Source_Code_Pro:h10:cANSI
        let font_name = "Source_Code_Pro"
      elseif getfontname( "Droid_Sans_Mono" ) != ""
        set guifont=Droid_Sans_Mono:h10:cANSI
        let font_name = "Droid_Sans_Mono"
      elseif getfontname( "DejaVu_Sans_Mono" ) != ""
        set guifont=DejaVu_Sans_Mono:h11:cANSI
        let font_name = "DejaVu_Sans_Mono"
      elseif getfontname( "Bitstream_Vera_Sans_Mono" ) != ""
        set guifont=Bitstream_Vera_Sans_Mono:h10:cANSI
        let font_name = "Bitstream_Vera_Sans_Mono"
      elseif getfontname( "Raize" ) != ""
        set guifont=Raize:h12:b:cANSI
        let font_name = "Raize"
      else
        set guifont=Lucida_Console:h12:cANSI
        let font_name = "Lucida_Console"
      endif
      set guifontwide=Courier_New:h12:cANSI
      silent exec "nnoremap <unique> <M-F1> :set guifont=".font_name.":h11:cANSI<CR>"
    endif
  endfunction
" }}}

"}}} Basic

"---------------------------------------------------------------
"""""""""""""""""""""" Filetypes """""""""""""""""""""""""""""""
"---------------------------------------------------------------
if g:load_vimrc_filetype "{{{

  "-----------------------------------------------------------
  " Verilog Automatic
  " {{{
    inoremap        iav     <ESC>:Allpn<CR>
    noremap         :iav        :Allpn<CR>
    " :inoremap     av      <ESC>:Allcom<CR>
    " map           :av     :Allcom<CR>
    inoremap        ihv             <ESC>:AddHeader<CR>
    noremap         <leader>hv      :AddHeader<CR>
    inoremap        icv             <ESC>:Acontent<CR>
    noremap         <leader>cv      :Acontent<CR>
  " }}}

  "---------------
  " Python
  "---------------
  " auto complete
  noremap <F9> :!python.exe
  " Only do this part when compiled with support for autocommands.
  " if has("autocmd")
  augroup ft_python
    autocmd!
    autocmd FileType python setlocal expandtab shiftwidth=4 tabstop=4 softtabstop=4
    autocmd FileType python setlocal colorcolumn=79 textwidth=80
    autocmd FileType python setlocal formatoptions+=croq
    autocmd FileType python setlocal cinwords=if,elif,else,for,while,try,except,finally,def,class,with
    autocmd FileType python setlocal foldmethod=indent
    autocmd FileType python setlocal cindent
    autocmd FileType python setlocal cinkeys-=0#
    autocmd FileType python setlocal indentkeys-=0#
    autocmd FileType python inoremap <buffer> $r return
    autocmd FileType python inoremap <buffer> $i import
    autocmd FileType python inoremap <buffer> $p print
    autocmd FileType python inoremap <buffer> $f #--- <esc>a
    autocmd FileType python map <buffer> <leader>1 /class
    autocmd FileType python map <buffer> <leader>2 /def
    autocmd FileType python map <buffer> <leader>C ?class
    autocmd FileType python map <buffer> <leader>D ?def
  augroup END

  """"""""""""""""""""""""""""""
  " => Shell section
  """"""""""""""""""""""""""""""
  if s:os == "windows"
    " ensure correct shell in gvim
    set shell=c:\windows\system32\cmd.exe
  endif

  if exists('$TMUX')
      set term=screen-256color
  endif
endif
"}}} Filetypes


"---------------------------------------------------------------
"""""""""""""""""""""" Plugin_config """""""""""""""""""""""""""
"---------------------------------------------------------------
if g:load_vimrc_plugin_config " {{{

  " ----------------------------------------------------------------------------
  " vim-plug extension
  " ----------------------------------------------------------------------------
  let g:plug_window = '-tabnew'
  let g:plug_pwindow = 'vertical rightbelow new'

  "-----------------------------------------------------------
  " Solarized {{{
    " Allow color schemes to do bright colors without forcing bold.
    if &t_Co == 8 && $TERM !~# '^linux\|^Eterm'
      set t_Co=16
    endif
    " set t_Co=256
    try
      let g:solarized_termtrans=1
      let g:solarized_termcolors=256
      let g:solarized_contrast="high"
      let g:solarized_visibility="high"
      let base16colorspace=256
      colorscheme solarized
      " set background=light
    catch
      colorscheme murphy
      " colorscheme badwolf
    endtry
  " }}}

  "-----------------------------------------------------------
  " TagList {{{
    let Tlist_Ctags_Cmd = g:dotvim_settings.ctags_path
    if !executable('ctags')
      let loaded_taglist = 1
    endif
    let Tlist_Use_Right_Window=1                " display at right side
    let Tlist_File_Fold_Auto_Close=0            " only display current file, close other files tags
    let Tlist_Sort_Type = "name"                " sort by name
    let Tlist_Exit_OnlyWindow = 1             " exit if it's the last window
    let Tlist_Auto_Open=0                     " not auto open
    let Tlist_Compact_Format=1                " compress
    let Tlist_Enable_Fold_Column=0            " Do not show folding tree
    noremap tt  :TlistToggle<CR>
    nnoremap <silent> <leader>tl :Tlist<cr>
  " }}}

  "-----------------------------------------------------------
  " tagbar {{{
      let g:tagbar_ctags_bin = g:dotvim_settings.ctags_path
      let g:tagbar_width = 20
      let g:tagbar_autofocus = 1
      let g:tagbar_sort = 1
      let g:tagbar_compact = 1
      let g:tagbar_expand = 1
      let g:tagbar_singleclick = 1
      let g:tagbar_usearrows = 1
      let g:tagbar_autoshowtag = 1
      let g:tagbar_show_visibility = 1
      let g:tagbar_map_closefold = ['h', '-', 'zc']
      let g:tagbar_map_openfold = ['l', '+', 'zo']
      " let g:tagbar_autoclose = 1    " auto close after open tag
      nnoremap <silent><leader>tb :TagbarToggle<CR>
      nnoremap <F6> :TagbarToggle<CR>
      "Open Tagbar or jump to it if already open (useful for split windows)
      nnoremap <leader>to :TagbarOpen j<CR>

      " Same as nerdtree, only open if no file was specified
      function! StartUpTagbar()
        if 0 == argc()
          TagbarOpen
        end
      endfunction

      augroup my_tagbar
        autocmd!
        " autocmd VimEnter * call StartUpTagbar()
      augroup END

      " Add Verilog/Systemverilog support
      let g:tagbar_type_systemverilog = {
          \ 'ctagstype' : 'systemverilog',
          \ 'sro' : '::',
          \ 'kinds' : [
              \ 'c:classes',
              \ 't:tasks',
              \ 'f:functions',
              \ 'm:modules',
              \ 'p:programs',
              \ 'i:interfaces',
              \ 'e:typedefs',
              \ 'd:defines'
          \]
      \}
  " }}}

  "-----------------------------------------------------------
  " MiniBufExplorer {{{
      let g:miniBufExplMapCTabSwitchBufs = 1
      let g:miniBufExplMapWindowNavVim = 1
      let g:miniBufExplMapWindowNavArrows = 1
      let g:miniBufExplModSelTarget = 1
      let g:miniBufExplSplitBelow = 1
      let g:miniBufExplMaxSize = 2
      let g:miniBufExplUseSingleClick = 1    " select by single click
      " autocmd BufRead,BufNew :call UMiniBufExplorer
      " noremap ,be :MBEToggle<CR>
  " }}}

  "-----------------------------------------------------------
  " Matchit {{{
    " Load matchit.vim, but only if the user hasn't installed a newer version.
    if !exists('g:loaded_matchit') && findfile('plugin/matchit.vim', &rtp) ==# ''
      runtime! macros/matchit.vim
      let b:match_ignorecase=0
      let b:match_words=
        \ '\<begin\>:\<end\>,' .
        \ '\<if\>:\<else\>,' .
        \ '\<module\>:\<endmodule\>,' .
        \ '\<class\>:\<endclass\>,' .
        \ '\<program\>:\<endprogram\>,' .
        \ '\<clocking\>:\<endclocking\>,' .
        \ '\<property\>:\<endproperty\>,' .
        \ '\<sequence\>:\<endsequence\>,' .
        \ '\<package\>:\<endpackage\>,' .
        \ '\<covergroup\>:\<endgroup\>,' .
        \ '\<primitive\>:\<endprimitive\>,' .
        \ '\<specify\>:\<endspecify\>,' .
        \ '\<generate\>:\<endgenerate\>,' .
        \ '\<interface\>:\<endinterface\>,' .
        \ '\<function\>:\<endfunction\>,' .
        \ '\<task\>:\<endtask\>,' .
        \ '\<case\>\|\<casex\>\|\<casez\>:\<endcase\>,' .
        \ '\<fork\>:\<join\>\|\<join_any\>\|\<join_none\>,' .
        \ '`ifdef\>:`else\>:`endif\>,'
    endif
  " }}}

  "-----------------------------------------------------------
  " hl-matchit {{{
    "" If this variable is set, augroup is defined, and start highlighting.
    let g:hl_matchit_enable_on_vim_startup = 1

    "" you can specify highlight group. see :highlight
    let g:hl_matchit_hl_groupname = 'Search'

    "" If 1 is set, sometimes do not highlight.
    let g:hl_matchit_speed_level = 1 " or 2

    "" you can specify use hl_matchit filetype.
    "let g:hl_matchit_allow_ft = 'html,vim,sh' " blah..blah..
  " }}}

  "-----------------------------------------------------------
  " Netrw {{{
    " File Explorer :e <PATH>
      let g:netrw_winsize        = 25
      let g:netrw_keepdir        = 0
      " let g:netrw_preview        = 0
      let g:netrw_liststyle      = 3
      let g:netrw_browse_split   = 0
      let g:netrw_cursor         = 3
      let g:netrw_banner         = 0
      let g:netrw_mousemaps      = 0
      let g:netrw_special_syntax = 1
      let g:netrw_timefmt        = "%y-%m-%d  %H-%M-%S"
      let g:netrw_list_hide      = '^[.]\w\|.*\.swp$'
      let g:netrw_cursor         = 0
      let g:netrw_errorlvl       = 1
      if executable('wget')
        let g:netrw_http_cmd = 'wget'
      endif

      noremap <leader>fte :Texplore<CR>            " open in new tab
      noremap <leader>fve :Vexplore<CR>           " vertical split
      nnoremap <silent> <leader>fe :Sexplore!<cr>
  " }}}

  "-----------------------------------------------------------
  " NERD Tree  File Manager {{{
    " o     open file                           " t     open file in new tab
    " go    open file,but cursor in NERDtree    " T     same as t, but focus on the current tab
    " tab   open file in a split window         " !     execute current file
    " x     close the current nodes parent      " X     Recursively close all children of the current node
    " e     open a netrw for the current dir
      noremap <leader>nt :NERDTreeToggle<CR>
      map <F5> :NERDTreeToggle<CR>
      " Opens current file heiarchy in Nerdtree
      nnoremap <leader>nf :NERDTreeFind<CR>
      let NERDChristmasTree=1                     " more colorful
      let NERDTreeWinPos="left"                   " put NERDTree at left
      let NERDTreeWinSize=25                      " set size
      let NERDTreeShowLineNumbers=0               " show line number
      let NERDTreeIgnore=['\.pyc', '\~$', '\.swo$', '\.swp$', '\.git', '\.hg', '\.svn', '\.bzr','CVS']
      " setting root dir in NT also sets VIM's cd"
      let NERDTreeChDirMode=2
      let NERDTreeShowHidden=1
      " single click to open directory
      let NERDTreeMouseMode = 2
      let NERDTreeHijackNetrw = 1

      " Only open nerdtree if no file was specified on startup
      function! StartUpNerdtree()
        if 0 == argc()
          NERDTree $HOME
        end
      endfunction

      augroup my_nerdtree
        autocmd!
        autocmd Filetype nerdtree setlocal nolist
        autocmd Filetype nerdtree nnoremap <buffer> H :vertical resize -10<cr>
        autocmd Filetype nerdtree nnoremap <buffer> L :vertical resize +10<cr>
        " autocmd VimEnter * call StartUpNerdtree()
      augroup END
  " }}}

  "-----------------------------------------------------------
  " NERDTree-tabs {{{
      noremap <leader>nn <plug>NERDTreeTabsToggle<CR>
      let g:nerdtree_tabs_open_on_console_startup=0   " NOT Open NERDTree on console vim startup
      let g:nerdtree_tabs_open_on_gui_startup=0       " Open NERDTree on gvim/macvim startup
  " }}}

  "-----------------------------------------------------------
  "Calendar {{{
    " :Calendar         " Open calendar
    " :CalendarH        " Open Calendar horizonally
    "let g:calendar_diary=<PATH>
    " let g:calendar_wruler = '日 一 二 三 四 五 六'
    let g:calendar_mark = 'left-fit'
    let g:calendar_focus_today = 1
    noremap <Leader>ca :Calendar<CR>
  " }}}

  "-----------------------------------------------------------
  " SVN Command {{{
      let g:svnj_custom_statusbar_ops_hide = 1
      if s:os == "windows"
        " let g:svnj_cache_dir=$HOME.'/.vim-cache'
        let g:svnj_cache_dir=g:dotvim_settings.cache_dir
      endif
  " }}}

  "-----------------------------------------------------------
  " showmarks {{{
    " <Leader>mt  - Toggle whether marks are displayed or not.
    " <Leader>mo  - Turn ShowMarks on, and displays marks.
    " <Leader>mh  - Clear mark on current line.
    " <Leader>ma  - Clear all marks.
    " <Leader>mm  - Places next available mark.
      " Enable ShowMarks
      let g:showmarks_enable = 1
      " Show which marks
      " let g:showmarks_include = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"
      let g:showmarks_include = "abcdefghijklmnopqrstuvwxyz"
      " Ignore help, quickfix, non-modifiable buffers
      let g:showmarks_ignore_type = "hqm"
      " Hilight lower & upper marks
      let g:showmarks_hlline_lower = 1
      let g:showmarks_hlline_upper = 1
      let g:showmarks_textlower = "\t"
      let g:showmarks_textupper = "\t"
      let g:showmarks_textother = "\t"
      let g:showmarks_no_mappings = 0
      " nmap mt <Plug>ShowMarksToggle
  " }}}

  "-----------------------------------------------------------
  " mark setting {{{
    nmap <silent> <leader>hl <Plug>MarkSet
    vmap <silent> <leader>hl <Plug>MarkSet
    nmap <silent> <leader>hh <Plug>MarkClear
    vmap <silent> <leader>hh <Plug>MarkClear
    nmap <silent> <leader>hr <Plug>MarkRegex
    vmap <silent> <leader>hr <Plug>MarkRegex
  " }}}

  "-----------------------------------------------------------
  " Vimwiki {{{
      let g:vimwiki_menu = 'Plugin.Vimwiki'
      let g:vimwiki_list = [{'path': 'E:/Workspace/Ref/vim/vim_wiki',
                          \ 'syntax': 'markdown',
                          \ 'path_html': 'E:/Workspace/Ref/vim/vim_wiki/pub_html',
                          \ 'nested_syntaxes' : {'python': 'python', 'verilog': 'verilog'},
                          \ 'diary_rel_path': 'diary/'}]
      let g:vimwiki_badsyms = ' '
      let g:vimwiki_camel_case = 0
    "    let g:vimwiki_ext2syntax = {'.md': 'markdown',
    "                    \ '.mkd': 'markdown',
    "                    \ '.markdown': 'markdown',
    "                    \ '.wiki': 'media'}
  " }}}

  "-----------------------------------------------------------
  " timestamp {{{
    let g:timestamp_regexp = '\v\C%(<%([cC]hanged?|[Mm]odified|[Uu]pdated)\s*:\s+)@<=\d{4}-\d{2}-\d{2} \d{2}:\d{2}:\d{2}|2010-11-01 12:57:29'
    let g:timestamp_rep = '%Y-%m-%d %H:%M:%S'
    let g:timestamp_modelines = 20
  " }}}

  "-----------------------------------------------------------
  " yankring.vim  {{{
      let g:yankring_enabled=0
      let g:yankring_history_file = '.vim-cache/yankring_history'
      noremap <leader>yr :YRShow<cr>
  " }}}

  "-----------------------------------------------------------
  " Colorful Parentheses {{{
  " rainbow

    let g:rainbow_active = 1 "0 if you want to enable it later via :RainbowToggle
    " Colors I got off the internet somewhere
    let g:rainbow_conf = { 'ctermfgs': ['cyan', 'magenta', 'yellow', 'grey', 'red', 'green', 'blue'],
          \                'guifgs': ['#FF0000', '#FF00FF', '#FFFF00', '#000000', '#FF0000', '#00FF00', '#0000FF'] }
  " }}}

  " ------------------------------------------------------------
  " Draw It {{{
    let g:DrChipTopLvlMenu = 'Plugin.' " remove 'DrChip' menu
  " }}}

  "-----------------------------------------------------------
  " neocomplcache {{{
  if g:dotvim_settings.autocomplete_method == 'neocomplcache'
    if v:version >= 702
      let g:acp_enableAtStartup = 0              " Disable AutoComplPop.
      let g:neocomplcache_enable_at_startup = 1  " Use neocomplcache
      let g:neocomplcache_enable_smart_case = 1  " Use smartcase
      let g:neocomplcache_min_syntax_length = 3 " Set minimum syntax keyword length.
      let g:neocomplcache_temporary_dir = g:dotvim_settings.cache_dir . '/neocomplcache'
      " Enable heavy features.
      " Use camel case completion.
      let g:neocomplcache_enable_camel_case_completion = 1 " Use camel case completion
      let g:neocomplcache_enable_underbar_completion = 1   " Use underbar completion

      let g:neocomplcache_max_list = 10
      " let g:neocomplcache_enable_fuzzy_completion = 1
      " let g:neocomplcache_fuzzy_completion_start_length = 3
      let g:neocomplcache_lock_buffer_name_pattern = '\*ku\*'

      let g:neocomplcache_ctags_program = g:dotvim_settings.ctags_path

      let g:neocomplcache_auto_completion_start_length = 2
      " Define keyword.
      if !exists('g:neocomplcache_keyword_patterns')
        let g:neocomplcache_keyword_patterns = {}
      endif
      let g:neocomplcache_keyword_patterns['default'] = '\h\w*'

      " Enable heavy omni completion.
      if !exists('g:neocomplcache_omni_patterns')
        let g:neocomplcache_omni_patterns = {}
      endif
      let g:neocomplcache_omni_patterns.c = '\%(\.\|->\)\h\w*'
      let g:neocomplcache_omni_patterns.cpp = '\h\w*\%(\.\|->\)\h\w*\|\h\w*::'

      " " Plugin key-mappings.
      " imap <C-k>     <Plug>(neocomplcache_snippets_expand)
      " smap <C-k>     <Plug>(neocomplcache_snippets_expand)
      inoremap <expr><C-g>     neocomplcache#undo_completion()
      inoremap <expr><C-l>     neocomplcache#complete_common_string()

      " Recommended key-mappings.
      " <CR>: close popup and save indent.
      " inoremap <silent> <CR> <C-r>=<SID>my_cr_function()<CR>
      function! s:my_cr_function()
        return neocomplcache#smart_close_popup() . "\<CR>"
        " For no inserting <CR> key.
        "return pumvisible() ? neocomplcache#close_popup() : "\<CR>"
      endfunction
      " <TAB>: completion.
      inoremap <expr><TAB>  pumvisible() ? "\<C-n>" : "\<TAB>"
      " <C-h>, <BS>: close popup and delete backword char.
      inoremap <expr><C-h> neocomplcache#smart_close_popup()."\<C-h>"
      inoremap <expr><BS> neocomplcache#smart_close_popup()."\<C-h>"
      inoremap <expr><C-y>  neocomplcache#close_popup()
      inoremap <expr><C-e>  neocomplcache#cancel_popup()

      " Close popup by <Space>.
      inoremap <expr><Space> pumvisible() ? neocomplcache#close_popup() : "\<Space>"
    endif
  endif
  " }}}

  "-----------------------------------------------------------
  " neocomplete {{{
  if g:dotvim_settings.autocomplete_method == 'neocomplete'
      "Note: This option must set it in .vimrc(_vimrc).  NOT IN .gvimrc(_gvimrc)!
      " Disable AutoComplPop.
      let g:acp_enableAtStartup = 0
      " Use neocomplete.
      let g:neocomplete#enable_at_startup = 1
      " Use smartcase.
      let g:neocomplete#enable_smart_case = 1
      " Set minimum syntax keyword length.
      let g:neocomplete#sources#syntax#min_keyword_length = 3
      let g:neocomplete#lock_buffer_name_pattern = '\*ku\*'
      let g:neocomplete#data_directory=g:dotvim_settings.cache_dir.'/neocomplcache'

      " Define dictionary.
      let g:neocomplete#sources#dictionary#dictionaries = {
          \ 'default' : '',
          \ 'vimshell' : $HOME.'/.vimshell_hist',
          \ 'scheme' : $HOME.'/.gosh_completions'
              \ }

      " Define keyword.
      if !exists('g:neocomplete#keyword_patterns')
          let g:neocomplete#keyword_patterns = {}
      endif
      let g:neocomplete#keyword_patterns['default'] = '\h\w*'

      " Plugin key-mappings.
      inoremap <expr><C-g>     neocomplete#undo_completion()
      inoremap <expr><C-l>     neocomplete#complete_common_string()

      " Recommended key-mappings.
      " <CR>: close popup and save indent.
      inoremap <silent> <CR> <C-r>=<SID>my_cr_function()<CR>
      function! s:my_cr_function()
        return neocomplete#close_popup() . "\<CR>"
        " For no inserting <CR> key.
        "return pumvisible() ? neocomplete#close_popup() : "\<CR>"
      endfunction
      " <TAB>: completion.
      inoremap <expr><TAB>  pumvisible() ? "\<C-n>" : "\<TAB>"
      " <C-h>, <BS>: close popup and delete backword char.
      inoremap <expr><C-h> neocomplete#smart_close_popup()."\<C-h>"
      inoremap <expr><BS> neocomplete#smart_close_popup()."\<C-h>"
      inoremap <expr><C-y>  neocomplete#close_popup()
      inoremap <expr><C-e>  neocomplete#cancel_popup()
      " Close popup by <Space>.
      "inoremap <expr><Space> pumvisible() ? neocomplete#close_popup() : "\<Space>"

      " For cursor moving in insert mode(Not recommended)
      "inoremap <expr><Left>  neocomplete#close_popup() . "\<Left>"
      "inoremap <expr><Right> neocomplete#close_popup() . "\<Right>"
      "inoremap <expr><Up>    neocomplete#close_popup() . "\<Up>"
      "inoremap <expr><Down>  neocomplete#close_popup() . "\<Down>"
      " Or set this.
      "let g:neocomplete#enable_cursor_hold_i = 1
      " Or set this.
      "let g:neocomplete#enable_insert_char_pre = 1

      " AutoComplPop like behavior.
      "let g:neocomplete#enable_auto_select = 1

      " Shell like behavior(not recommended).
      "set completeopt+=longest
      "let g:neocomplete#enable_auto_select = 1
      "let g:neocomplete#disable_auto_complete = 1
      "inoremap <expr><TAB>  pumvisible() ? "\<Down>" : "\<C-x>\<C-u>"

      " Enable heavy omni completion.
      if !exists('g:neocomplete#sources#omni#input_patterns')
        let g:neocomplete#sources#omni#input_patterns = {}
      endif
      "let g:neocomplete#sources#omni#input_patterns.php = '[^. \t]->\h\w*\|\h\w*::'
      "let g:neocomplete#sources#omni#input_patterns.c = '[^.[:digit:] *\t]\%(\.\|->\)'
      "let g:neocomplete#sources#omni#input_patterns.cpp = '[^.[:digit:] *\t]\%(\.\|->\)\|\h\w*::'

      " For perlomni.vim setting.
      " https://github.com/c9s/perlomni.vim
      let g:neocomplete#sources#omni#input_patterns.perl = '\h\w*->\h\w*\|\h\w*::'
  endif
  "}}}

  "-----------------------------------------------------------
  " conque {{{
      autocmd FileType conque_term match none
      let g:ConqueTerm_StartMessages = 0

      command! Sh ConqueTermSplit bash --login
      command! Irb ConqueTermSplit irb
      command! Py ConqueTermSplit ipython
  " }}}

  "-----------------------------------------------------------
  " indent-guides {{{
    " highlight indent with different color
    " The default mapping : <Leader>ig
      " let g:indent_guides_enable_on_vim_startup = 1   " enable when startup
      let g:indent_guides_auto_colors = 1       " automatically calculates the highlight colors
      let g:indent_guides_exclude_filetypes = ['help', 'nerdtree']
      let g:indent_guides_start_level=1
      let g:indent_guides_guide_size=1
      let g:indent_guides_color_change_percent=3
  " }}}

  "-----------------------------------------------------------
  " indentLines {{{
    autocmd! User indentLine doautocmd indentLine Syntax
  " }}}

  "-----------------------------------------------------------
  " undotree {{{
      nnoremap <Leader>gu :UndotreeToggle<CR>
  " }}}

  "-----------------------------------------------------------
  " ctrlp {{{
  if g:dotvim_settings.finder_method == 'ctrlp'
      let g:ctrlp_map = '<Leader>p'
      let g:ctrlp_cmd = 'CtrlP'
      map <leader>j :CtrlP<cr>
      " Set Ctrl-P to show match at top of list instead of at bottom, which is so
      " stupid that it's not default
      let g:ctrlp_match_window_reversed = 0
      let g:ctrlp_cache_dir = g:dotvim_settings.cache_dir . '/ctrlp'
      " Tell Ctrl-P to keep the current VIM working directory when starting a
      " search, another really stupid non default
      let g:ctrlp_working_path_mode = 'ra'
      let g:ctrlp_clear_cache_on_exit=1
      let g:ctrlp_max_height=40
      let g:ctrlp_show_hidden=0
      let g:ctrlp_follow_symlinks=1
      let g:ctrlp_max_files=20000
      let g:ctrlp_reuse_window='startify'
      let g:ctrlp_extensions=['funky']

      " let g:ctrlp_custom_ignore = '\v[\/]\.(git|hg|svn)$'
      let g:ctrlp_custom_ignore = {
          \ 'dir':  '\v[\/]\.(git|hg|svn)$',
          \ 'file': '\v\.(exe|so|dll|pyc)$',
          \ 'link': 'some_bad_symbolic_links',
          \ }
      if s:os == "windows"  " Windows
        let g:ctrlp_user_command = 'dir %s /-n /b /s /a-d'
      elseif s:os == "linux"        " MacOSX/Linux
        if executable('ag')
          let g:ctrlp_user_command = 'ag %s -l --nocolor -g ""'
        else
          let g:ctrlp_user_command = 'find %s -type f'
        endif
      endif
      let g:ctrlp_open_multi = '10t'
  endif
  " }}}

  "-----------------------------------------------------------
  " vim-cycle {{{
      nmap <silent> <Leader>n <Plug>CycleNext
      vmap <silent> <Leader>n <Plug>CycleNext
  " }}}


  "-----------------------------------------------------------
  " Neosnippet {{{
  if g:dotvim_settings.snippet_method == 'neosnippet'
      " Plugin key-mappings.
      " C-k to select-and-expand a snippet from the Neocomplcache popup (Use C-n and C-p to select it).
      " C-k can also be used to jump to the next field in the snippet.
      imap <C-k>     <Plug>(neosnippet_expand_or_jump)
      smap <C-k>     <Plug>(neosnippet_expand_or_jump)
      xmap <C-k>     <Plug>(neosnippet_expand_target)

      " Tab to select the next field to fill in the snippet.
      "" " SuperTab like snippets behavior
      " inoremap <expr><TAB> neosnippet#expandable_or_jumpable() ?
      "   \ "\<Plug>(neosnippet_expand_or_jump)"
      "   \: pumvisible() ? "\<C-n>" : "\<TAB>"
      " snoremap <expr><TAB> neosnippet#expandable_or_jumpable() ?
      "   \ "\<Plug>(neosnippet_expand_or_jump)" : "\<TAB>"

      " For snippet_complete marker.
      if has('conceal')
        set conceallevel=2 concealcursor=i
      endif"

      " use a different collection of snippets other than the built-in ones
      " Enable snipMate compatibility feature, load snipMate snippets from runtime path automatically.
      let g:neosnippet#enable_snipmate_compatibility = 1

      " Tell Neosnippet about the other snippets
      let g:neosnippet#snippets_directory=[ g:vimfiles . '/snippets/snippets',
                                          \ g:vimfiles . '/bundle/systemc/snippets']

      " associating certain filetypes with other snippet files.
      let g:neosnippet#scope_aliases = {}
      let g:neosnippet#scope_aliases['cpp'] = 'cpp,systemc'
      let g:neosnippet#scope_aliases['systemverilog'] = 'systemverilog,uvm'
  endif
  " }}}

  "-----------------------------------------------------------
  " snipMate {{{
  if g:dotvim_settings.snippet_method == 'snipmate'
      " Add my snippets folder
      let g:local_snippets = g:vimfiles.'/snippets/snippets'
      let g:snips_author = 'Hong Jin <hon9jin@gmail.com>'
      let g:snipMate = get(g:, 'snipMate', {}) " Allow for vimrc re-sourcing
      let g:snipMate.scope_aliases = {}
      let g:snipMate.scope_aliases['systemverilog'] = 'verilog,systemverilog,uvm'
      let g:snipMate.scope_aliases['verilog_systemverilog'] = 'verilog,systemverilog,uvm'
      imap <C-J> <Plug>snipMateNextOrTrigger
      smap <C-J> <Plug>snipMateNextOrTrigger
      imap <C-K> <Plug>snipMateNextOrTrigger
      smap <C-K> <Plug>snipMateNextOrTrigger
  endif "}}}

  "-----------------------------------------------------------
  " UltiSnips {{{
  if g:dotvim_settings.snippet_method == 'ultisnips'
      " better key bindings for UltiSnipsExpandTrigger
      let g:UltiSnipsExpandTrigger = "<C-J>"
      let g:UltiSnipsJumpForwardTrigger = "<C-J>"
      let g:UltiSnipsJumpBackwardTrigger = "<C-K>"
      let g:UltiSnipsEditSplit="vertical"
      let g:UltiSnipsSnippetsDir=g:vimfiles . '/snippets/UltiSnips'
  endif "}}}

  "-----------------------------------------------------------
  " delimitMate {{{
    " let loaded_delimitMate = 1
    " au FileType mail let b:loaded_delimitMate = 1
    let delimitMate_matchpairs = "(:),[:],{:},<:>"
    let delimitMate_quotes = "\" ' `"
    let g:delimitMate_expand_cr = 1
    let delimitMate_balance_matchpairs = 1
    let g:delimitMate_expand_space = 2

    augroup my_delimiMate
      autocmd!
      autocmd FileType vim,html let b:delimitMate_matchpairs = "(:),[:],{:},<:>"
      autocmd FileType systemverilog let b:delimitMate_matchpairs = "(:),[:],{:}"
      autocmd FileType c,cpp let b:delimitMate_matchpairs = "(:),[:],{:}"
      autocmd FileType vim let b:delimitMate_quotes = "' `"
      autocmd FileType systemverilog let b:delimitMate_quotes = "\""
    augroup END
  " }}}

  "-----------------------------------------------------------
  " vim-easy-align {{{
      " Start interactive EasyAlign in visual mode (e.g. vipga)
      xmap ga <Plug>(EasyAlign)

      " Start interactive EasyAlign for a motion/text object (e.g. gaip)
      nmap ga <Plug>(EasyAlign)
  " }}}

  "-----------------------------------------------------------
  " Tabular {{{
    if exists(":Tabularize")
      nnoremap <Leader>a&      : Tabularize /&<CR>
      vnoremap <Leader>a&      : Tabularize /&<CR>
      nnoremap <Leader>a=      : Tabularize /=<CR>
      vnoremap <Leader>a=      : Tabularize /=<CR>
      nnoremap <Leader>a=>     : Tabularize /=><CR>
      vnoremap <Leader>a=>     : Tabularize /=><CR>
      nnoremap <Leader>a<=     : Tabularize /<=<CR>
      vnoremap <Leader>a<=     : Tabularize /<=<CR>
      nnoremap <Leader>a:      : Tabularize /:<CR>
      vnoremap <Leader>a:      : Tabularize /:<CR>
      nnoremap <Leader>a::     : Tabularize /:\zs<CR>
      vnoremap <Leader>a::     : Tabularize /:\zs<CR>
      nnoremap <Leader>a,      : Tabularize /,<CR>
      vnoremap <Leader>a,      : Tabularize /,<CR>
      nnoremap <Leader>a,,     : Tabularize /,\zs<CR>
      vnoremap <Leader>a,,     : Tabularize /,\zs<CR>
      nnoremap <Leader>a<Bar>  : Tabularize /<Bar><CR>
      vnoremap <Leader>a<Bar>  : Tabularize /<Bar><CR>
      nnoremap <Leader>a/      : Tabularize /\/\//l2c1l0<CR>
      vnoremap <Leader>a/      : Tabularize /\/\//l2c1l0<CR>
    endif
  " }}}


  "-----------------------------------------------------------
  " fugitive {{{
    " Git integration!
    nnoremap <leader>gs :Gstatus<enter>
    nnoremap <leader>gd :Gdiff<enter>
    nnoremap <leader>gc :Gcommit<enter>
    nnoremap <leader>gl :gitv<enter>
    nnoremap <leader>ga :Git commit --amend<enter>
    nnoremap <leader>gD :Git diff --cached --color<enter>
    " this inserts the last commit message
    " % needs to be escaped, otherwise vim inserts its register %
    " Note that no <enter> so user has the option of changing number of commits
    nnoremap <leader>gh :r !git log --format=format:\%s -1
  " }}}

  "-----------------------------------------------------------
  " NerdCommenter {{{
    " Add spaces after comment delimiters by default
    let g:NERDSpaceDelims = 1   " add extra space
    " Enable trimming of trailing whitespace when uncommenting
    let g:NERDTrimTrailingWhitespace = 1
    " Allow commenting and inverting empty lines (useful when commenting a region)
    let g:NERDCommentEmptyLines = 1
  "}}}

  "-----------------------------------------------------------
  " AuthorInfo {{{
    let g:vimrc_author='Hong Jin'
    let g:vimrc_email='hongjin@fiberhome.com'
  "}}}

  "-----------------------------------------------------------
  " Grep {{{
    if s:os == "windows"
      let g:Grep_Path       = g:vimfiles.'/gnu/grep.exe'
      let g:Fgrep_Path      = g:vimfiles.'/gnu/fgrep.exe'
      let g:Egrep_Path      = g:vimfiles.'/gnu/egrep.exe'
      let g:Grep_Find_Path  = g:vimfiles.'/gnu/find.exe'
      let g:Grep_Xargs_Path = g:vimfiles.'/gnu/xargs.exe'
    endif
    let Grep_Default_Options = '-i'
    let Grep_Skip_Dirs = 'RCS CVS .svn .git'
  "}}}

  "-----------------------------------------------------------
  " airline {{{
  if g:dotvim_settings.statusline_method == 'airline'
      " let g:airline_section_b = '%{getcwd()}'
      " " let g:airline_section_c = '%t'
      " " let g:airline_section_c = airline#section#create_left(['%{getcwd()}', 'file'])
      " let g:airline_section_c = airline#section#create_left(['file'])

      let g:airline_inactive_collapse=1

      " Enable Extensions
      " let g:airline_extensions = ['branch', 'quickfix', 'tabline']
  endif
  "}}}

  "-----------------------------------------------------------
  " lightline {{{
  if g:dotvim_settings.statusline_method == 'lightline'
      "let g:lightline = {
      "    \     'active': {
      "    \         'left': [['mode', 'paste' ], ['readonly', 'filename', 'modified']],
      "    \         'right': [['lineinfo'], ['percent'], ['fileformat', 'fileencoding']]
      "    \     }
      "    \ }
  endif
  " }}}

  "-----------------------------------------------------------
  " easymotion {{{
    " triggered with `<Leader><Leader>`
    " `<Leader><Leader>w` to find the beginning of a word
    " `<Leader><Leader>f` to find the character
    " `<Leader><Leader>b  to Beginning of word backward
    " `<Leader><Leader>e  to End of word forward
    " `<Leader><Leader>j  to Line downward
    " `<Leader><Leader>k  to Line upward
      " let g:EasyMotion_leader_key = '<space>'
      " change the target keys
      " let g:EasyMotion_keys = '1234567890'
      " disable shading : 0
      let g:EasyMotion_do_shade = 1
      hi link EasyMotionTarget ErrorMsg
      hi link EasyMotionShade Comment
  "}}}

  "-----------------------------------------------------------
  " Verilog {{{
    " verilog root menu
    let g:PluginTopLvlMenu = 'Plugin'
  "}}}

  "-----------------------------------------------------------
  " uvm_gen {{{
    let g:uvm_author    = "Hong Jin"
    let g:uvm_email     = "hongjin@fiberhome.com"
    let g:uvm_company   = "Copyright (c) " . strftime ("%Y") . ", Fiberhome Telecommunication Technology Co., Ltd."
    let g:uvm_department = "Microelectronics Dept. Logic Development Group."
  "}}}

  "-----------------------------------------------------------
  " multi_cursor {{{
    let g:multi_cursor_use_default_mapping=1
  "}}}

  "-----------------------------------------------------------
  " CamelCaseMotion {{{
    " Replace the default 'w', 'b' and 'e' mappings with <Plug>CamelCaseMotion_?
    map <silent> W <Plug>CamelCaseMotion_w
    map <silent> B <Plug>CamelCaseMotion_b
    map <silent> E <Plug>CamelCaseMotion_e
    sunmap W
    sunmap B
    sunmap E
    omap <silent> iw <Plug>CamelCaseMotion_iw
    xmap <silent> iw <Plug>CamelCaseMotion_iw
    omap <silent> ib <Plug>CamelCaseMotion_ib
    xmap <silent> ib <Plug>CamelCaseMotion_ib
    omap <silent> ie <Plug>CamelCaseMotion_ie
    xmap <silent> ie <Plug>CamelCaseMotion_ie
  "}}}

  "-----------------------------------------------------------
  " anzu {{{
    " display the current match index number and total match number of search pattern
    " mapping
    nmap n <Plug>(anzu-n-with-echo)
    nmap N <Plug>(anzu-N-with-echo)
    " nmap * <Plug>(anzu-star-with-echo)
    " nmap # <Plug>(anzu-sharp-with-echo)

    " clear status
    nmap <Esc><Esc> <Plug>(anzu-clear-search-status)

    " statusline
    " set statusline+=%{anzu#search_status()}
  "}}}

  "-----------------------------------------------------------
  " c-support {{{
    " C/C++ IDE
    let g:C_GlobalTemplateFile = g:vimfiles . '/bundle/c/c-support/templates/Templates'
    let g:C_LocalTemplateFile  = g:vimfiles . '/c-support/templates/Templates'
    let g:C_Root = '&Plugin.&C\/C\+\+.'
    let g:C_FormatDate         = '%Y-%m-%d'
    let g:C_FormatTime         = '%H:%M:%S'
  "}}}

  "-----------------------------------------------------------
  " expand-region {{{
    let g:expand_region_text_objects = {
        \ 'iw'  :1,
        \ 'iW'  :1,
        \ 'i"'  :1,
        \ 'i''' :1,
        \ 'i]'  :1,
        \ 'ib'  :1,
        \ 'iB'  :1,
        \ 'il'  :0,
        \ 'ip'  :1,
        \ 'ie'  :1,
        \ }
    xmap v <Plug>(expand_region_expand)
    xmap V <Plug>(expand_region_shrink)
  "}}}

  "-----------------------------------------------------------
  " wildfire {{{
    " This selects the next closest text object.
    let g:wildfire_fuel_map = "<ENTER>"

    " This selects the previous closest text object.
    let g:wildfire_water_map = "<BS>"

    let g:wildfire_objects = ["i'", 'i"', "i)", "i]", "i}", "ip", "it"]
  "}}}

  "-----------------------------------------------------------
  " incsearch {{{
    map /  <Plug>(incsearch-forward)
    map ?  <Plug>(incsearch-backward)
    map g/ <Plug>(incsearch-stay)
    let g:incsearch#magic = '\v' " very magic
    let g:incsearch#magic = '\V' " very nomagic
    let g:incsearch#magic = '\m' " magic
    let g:incsearch#magic = '\M' " nomagic
    map n <Plug>(incsearch-nohl)<Plug>(anzu-n-with-echo)
    map N <Plug>(incsearch-nohl)<Plug>(anzu-N-with-echo)
  "}}}

  "-----------------------------------------------------------
  " vim-asterisk {{{
  " provides immap *   <Plug>(asterisk-*)
    map *   <Plug>(asterisk-g*)
    map g*  <Plug>(asterisk-*)
    map #   <Plug>(asterisk-g#)
    map g#  <Plug>(asterisk-#)

    map z*  <Plug>(asterisk-z*)
    map gz* <Plug>(asterisk-gz*)
    map z#  <Plug>(asterisk-z#)
    map gz# <Plug>(asterisk-gz#)
  " }}}

  "-----------------------------------------------------------
  " FastFold {{{
    nmap zuz <Plug>(FastFoldUpdate)
    let g:fastfold_savehook = 1
    let g:fastfold_fold_command_suffixes =  ['x','X','a','A','o','O','c','C']
    let g:fastfold_fold_movement_commands = [']z', '[z', 'zj', 'zk']
    let g:tex_fold_enabled   = 1
    let g:vimsyn_folding     = 'af'
    let g:xml_syntax_folding = 1
    let g:php_folding        = 1
    let g:perl_fold          = 1
  " }}}

  "-----------------------------------------------------------
  " signify {{{
  let g:signify_vcs_list = [ 'git', 'svn' ]
  " }}}
endif

"}}} Plugin_config -----------------------------------------


"-----------------------------------------------------------
"""""""""""""""""""""" Extended """"""""""""""""""""""""""""
"-----------------------------------------------------------
"{{{
if g:load_vimrc_extended

  "-----------------------------------------------------------
  " Key Mapping Setting {{{
  "-----------------------------------------------------------

  " map <F1> :call ToggleSketch()<CR>
  " map <F2> zr
  " map <F3>
  " map <F4> :call TitleDet()
  " map <F4>    :q<CR>
  " imap <F4>    <ESC>:q<CR>
  inoremap <silent> <F4> <C-o><F4>
  " map <F5> LookUp File
  " imap <silent> <F5> <C-o><F5>
  " F4 / F5 - change window height
  " "nnoremap <silent> <F4> <C-w>+
  " "imap <silent> <F4> <C-o><F4>
  " "nnoremap <silent> <F5> <C-w>-
  " "imap <silent> <F5> <C-o><F5>

  " map <F7> :tabprevious<CR>
  map <silent> <F7> <C-o><F7>
  " map <F7> :tabnext<CR>
  map <silent> <F8> <C-o><F8>

  map  <F7>           :tabprevious<CR>
  map  <F8>           :tabnext<CR>
  map  <leader>tn     :tabnew<CR>
  map  <leader>tc     :tabclose<CR>
  map  <leader>to     :tabonly<cr>
  imap  <F7>          <ESC>:tabprevious<CR>i
  imap  <F8>          <ESC>:tabnext<CR>i
  imap  ^T            <ESC>:tabnew<CR>i

  " map <F9> :!python.exe %
  map <F10> :execute "vimgrep /" . expand("<cword>") . "/j **" <Bar> cw<CR>
  " Buffer - reverse everything ... :)
  map <F11> ggVGg?     " rot-13
  map     <F12>   a<C-R>=strftime(" @ %Y-%m-%d %H:%M")<CR>
  imap    <F12>   <C-R>=strftime(" @ %Y-%m-%d %H:%M")<CR>
  " insert time    strftime("%c")

  " repeat command for each line in selection
  vnoremap . :normal .<CR>

  " shortcut for :diffupdate
  nnoremap du :diffupdate<CR>

  " map Ctrl+C to Escape
  inoremap <C-c> <Esc>

  " reselect visual block after indent
  vnoremap > >gv
  vnoremap < <gv

  " ,/ - remove highlighted search
  " nnoremap <silent> ,/ :noh<CR>

  " ,1-9 - quick buffer switching
  nnoremap <silent> <leader>1 :b1<CR>
  nnoremap <silent> <leader>2 :b2<CR>
  nnoremap <silent> <leader>3 :b3<CR>
  nnoremap <silent> <leader>4 :b4<CR>
  nnoremap <silent> <leader>5 :b5<CR>
  nnoremap <silent> <leader>6 :b6<CR>
  nnoremap <silent> <leader>7 :b7<CR>
  nnoremap <silent> <leader>8 :b8<CR>
  nnoremap <silent> <leader>9 :b9<CR>

  " Allow insert mode editing like emacs
  inoremap <C-a>  <Home>
  inoremap <C-e>  <End>
  inoremap <C-f> <Right>
  inoremap <C-b> <Left>

  noremap <M-d>  <C-o>diW   " delete word
  noremap <M-y>  <C-o>yiW   " yank word

  " Buffer commands
  nnoremap <silent> <leader>bb :buffers<CR>
  nnoremap <silent> <Leader>bd :bdelete<CR>

  " ,bn - next buffer
  nnoremap <silent> <leader>bn :bnext<CR>

  " ,bp - previous buffer
  nnoremap <silent> <leader>bp :bprevious<CR>

  " Remove trailing whitespace
  nnoremap <leader>dws :silent! %s/\s\+$//ge<enter>
  vnoremap <leader>dws :s/\s\+$//ge<enter>
  " Remove trailing ^M
  nmap <leader>dms :%s/\r$//g<CR>:noh<CR>

  " Ignore whitespace in diffs.
  " Also shows current diffopt status.
  nnoremap <leader>s :set diffopt+=iwhite<enter>:set diffopt<enter>
  nnoremap <leader>S :set diffopt-=iwhite<enter>:set diffopt<enter>

  " ,e* - Edit the vimrc file
  nnoremap <silent> <Leader>ev :e $MYVIMRC<CR>
  nnoremap <silent> <Leader>sv :so $MYVIMRC<CR>
  nnoremap <silent> <Leader>egv :e $MYGVIMRC<CR>
  nnoremap <silent> <Leader>sgv :so $MYGVIMRC<CR>

  " ,c - close current window
  " nnoremap <silent> <leader>c :silent! close<CR>

  " ,d - open definition in new window
  nnoremap <silent> <leader>d <C-w>f

  " ,P - Go back to previous file
  noremap <Leader>P <C-^>

  " ,s - split horizontally
  " nnoremap <silent> <leader>s :split<CR>
  nnoremap <silent> <leader>h :split^M^W^W<cr>

  " ,v - Reselect text that was just pasted
  nnoremap <leader>v V`]

  " ,W - clear trailing whitespace
  " nnoremap <silent> <leader>W :%s=\s\+$==<CR>
  nnoremap <leader>W :%s/\s\+$//<cr>

  " clearing highlighted search
  nnoremap <silent> <leader>\ :nohlsearch<CR>
  nnoremap <ESC><ESC> :nohlsearch<CR>

  inoremap <buffer> /*          /**/<Left><Left>
  inoremap <buffer> /*<Space>   /*<Space><Space>*/<Left><Left><Left>
  inoremap <buffer> /*<CR>      /*<CR>*/<Esc>O
  inoremap <buffer> <Leader>/*  /*

  " Easy escape."{{{
  inoremap jj           <Esc>
  onoremap jj           <ESC>
  inoremap j<Space>     j
  onoremap j<Space>     j
  "}}}

  " Jump mark can restore column."{{{
  nnoremap \  `
  " Useless command.
  nnoremap M  m
  "}}}

  " Smart <C-f>, <C-b>.
  nnoremap <silent> <C-f> <C-f>
  nnoremap <silent> <C-b> <C-b>

  " Like gv, but select the last changed text.
  nnoremap gc  `[v`]
  " Specify the last changed text as {motion}.
  vnoremap <silent> gc  :<C-u>normal gc<CR>
  onoremap <silent> gc  :<C-u>normal gc<CR>

  " Smart home and smart end."{{{
  nnoremap <silent> gh  :<C-u>call SmartHome("n")<CR>
  nnoremap <silent> ge  :<C-u>call SmartEnd("n")<CR>
  xnoremap <silent> gh  <ESC>:<C-u>call SmartHome("v")<CR>
  xnoremap <silent> ge  <ESC>:<C-u>call SmartEnd("v")<CR>
  nnoremap <expr> gm    (virtcol('$')/2).'\|'
  xnoremap <expr> gm    (virtcol('$')/2).'\|'

  " Fast saving
  nnoremap <silent> <leader>wr :w<cr>
  nnoremap <silent> <leader>wf :w!<cr>
  nnoremap <silent> <leader>w :w!<cr>
  " Force Saving Files that Require Root Permission
  cnoremap w!! %!sudo tee > /dev/null %
  " Fast quiting
  nnoremap <silent> <leader>qw :wq<cr>
  nnoremap <silent> <leader>qf :q!<cr>
  nnoremap <silent> <leader>qq :q<cr>
  nnoremap <silent> <leader>qa :qa<cr>
  " Fast remove highlight search
  nnoremap <silent> <leader><cr> :noh<cr>
  " Fast redraw
  nnoremap <silent> <leader>rr :redraw!<cr>

  "Smart way to move btw. windows
  " nmap <C-j> <C-W>j
  nnoremap <C-k> <C-W>k
  nnoremap <C-h> <C-W>h
  nnoremap <C-l> <C-W>l

  "Moving fast to front, back and 2 sides ;)
  inoremap <m-$> <esc>$a
  inoremap <m-0> <esc>0i

  " Easily macro.
  nnoremap @@ @a

  " CTRL-A is Select All
  " noremap     <C-A>   gggH<C-O>G
  " inoremap    <C-A>   <C-O>gg<C-O>gH<C-O>G
  " cnoremap    <C-A>   <C-C>gggH<C-O>G
  " onoremap    <C-A>   <C-C>gggH<C-O>G
  " snoremap    <C-A>   <C-C>gggH<C-O>G
  " xnoremap    <C-A>   <C-C>ggVG
  "
  "undo
  noremap     <C-Z> u
  inoremap    <C-Z> <C-O>u
  "" cut
  "vnoremap <C-X> "+x
  "" copy
  "vnoremap <C-C> "+y
  "" paste
  "map <C-Q>      "+gP
  "cmap <C-Q>     <C-R>+
  "" save
  "noremap <C-S>      :update<CR>
  "vnoremap <C-S>     <C-C>:update<CR>
  "inoremap <C-S>     <C-O>:update<CR>

  " comma always followed by a space
  " inoremap  ,  ,<Space>

  " set filetype to verilog
  "map ,fv     :set ft=verilog<CR>
  noremap <leader>fv     :set ft=systemverilog<CR>

  " Fold
  nnoremap <silent> <leader>zo zO
  vnoremap <silent> <leader>zo zO
  " Fold close & Fold open
  noremap <unique> <kPlus> zo
  noremap <unique> <kMinus> zc
  map <leader>zz :call ToggleFold()<CR>

  " Set as toggle foldcomment
  nnoremap zc @=((foldclosed(line('.')) < 0) ? 'zc' :'zo')<CR>
  nnoremap zr zR

  if version >= 600
    " Reduce folding
    map <F2> zr
    map <S-F2> zR
    " Increase folding
    map <F3> zm
    map <S-F3> zM
  endif

  " Yank from the cursor to the end of the line, to be consistent with C and D
  nnoremap Y y$

  "-----------------------------
  " Spell checking
  noremap <leader>sn ]s
  noremap <leader>sp [s
  noremap <leader>sa zg
  noremap <leader>s? z=

  " " don't use exact searches for */#
  " " "noremap * g*
  " " "noremap # g#
  " noremap <kMultiply> g*          " map * to g*
  " " Smart word search."{{{
  " " Search cursor word by word unit.
  " " nnoremap <silent> *  :<C-u>call <SID>SetSearch('""yiw', 'word')<CR>
  " " Search cursor word.
  " nnoremap <silent> g* :<C-u>call <SID>SetSearch('""yiw')<CR>
  " " Search from cursor to word end.
  " " nnoremap <silent> #  :<C-u>call <SID>SetSearch('""ye')<CR>

  " " Search selected text.
  " xnoremap <silent> * :<C-u>call <SID>SetSearch('""vgvy')<CR>
  " xnoremap <silent> # :<C-u>call <SID>SetSearch('""vgvy')<CR>

  " " Visual mode pressing * or # searches for the current selection
  " " Super useful! From an idea by Michael Naumann
  " vnoremap <silent> * :call VisualSelection('f', '')<CR>
  " vnoremap <silent> # :call VisualSelection('b', '')<CR>

  function! VisualSelection(direction, extra_filter) range
    let l:saved_reg = @"
    execute "normal! vgvy"

    let l:pattern = escape(@", '\\/.*$^~[]')
    let l:pattern = substitute(l:pattern, "\n$", "", "")

    if a:direction == 'b'
      execute "normal ?" . l:pattern . "^M"
    elseif a:direction == 'gv'
      call CmdLine("vimgrep " . '/'. l:pattern . '/' . ' **/*.' . a:extra_filter)
    elseif a:direction == 'replace'
      call CmdLine("%s" . '/'. l:pattern . '/')
    elseif a:direction == 'f'
      execute "normal /" . l:pattern . "^M"
    endif

    let @/ = l:pattern
    let @" = l:saved_reg
  endfunction

  """"""""""""""""""""""""""""""
  " Set search word.
  " If set additional parametar, search by word unit.
  """"""""""""""""""""""""""""""
  function! s:SetSearch(cmd, ...)
    let saved_reg = @"
    if a:cmd != ''
      silent exec 'normal! '.a:cmd
    endif
    let pattern = escape(@", '\\/.*$^~[]')
    let pattern = substitute(pattern, '\n$', '', '')
    if a:0 > 0
      let pattern = '\<'.pattern.'\>'
    endif
    let @/ = pattern
    let @" = saved_reg
    echo @/
  endfunction "}}}

  " Smart home function"{{{
  function! SmartHome(mode)
    let curcol = col('.')

    if &wrap
      normal! g^
    else
      normal! ^
    endif
    if col('.') == curcol
      if &wrap
        normal! g0
      else
        normal! 0
      endif
    endif

    if a:mode == "v"
      normal! msgv`s
    endif

    return ""
  endfunction "}}}

  " Smart end function"{{{
  function! SmartEnd(mode)
    let curcol = col('.')
    let lastcol = a:mode ==# 'i' ? col('$') : col('$') - 1

    " Gravitate towards ending for wrapped lines
    if curcol < lastcol - 1
      call cursor(0, curcol + 1)
    endif

    if curcol < lastcol
      if &wrap
        normal! g$
      else
        normal! $
      endif
    else
      normal! g_
    endif

    " Correct edit mode cursor position, put after current character
    if a:mode == "i"
      call cursor(0, col(".") + 1)
    endif

    if a:mode == "v"
      normal! msgv`s
    endif

    return ""
  endfunction "}}}
  "}}}

  " Paste next line.
  nnoremap <silent> gp o<ESC>p^
  nnoremap <silent> gP O<ESC>P^
  xnoremap <silent> gp o<ESC>p^
  xnoremap <silent> gP O<ESC>P^

  " Jump to a line and the line of before and after of the same indent."{{{
  " Useful for Python.
  nnoremap <silent> g{ :<C-u>call search('^' . matchstr(getline(line('.') + 1), '\(\s*\)') .'\S', 'b')<CR>^
  nnoremap <silent> g} :<C-u>call search('^' . matchstr(getline(line('.')), '\(\s*\)') .'\S')<CR>^

  " Copy remaining word from above or below.
  " Useful in situations where you need to repeat some code and don't want to
  " copy a whole line and edit parts of it.
  "     Wordwise Ctrl-Y in insert mode - Vim Tips Wiki
  "     http://vim.wikia.com/wiki/Wordwise_Ctrl-Y_in_insert_mode
  inoremap <expr> <c-y> matchstr(getline(line('.')-1), '\%' . virtcol('.') . 'v\%(\k\+\\|.\)')
  inoremap <expr> <c-e> matchstr(getline(line('.')+1), '\%' . virtcol('.') . 'v\%(\k\+\\|.\)')
  "}}}

  " Select rectangle.
  xnoremap r <C-v>
  " Select until end of current line in visual mode.
  xnoremap v $h

  " a>, i], etc... "{{{
  " <angle>
  onoremap aa  a>
  xnoremap aa  a>
  onoremap ia  i>
  xnoremap ia  i>

  " [rectangle]
  onoremap ar  a]
  xnoremap ar  a]
  onoremap ir  i]
  xnoremap ir  i]

  " 'quote'
  onoremap aq  a'
  xnoremap aq  a'
  onoremap iq  i'
  xnoremap iq  i'

  " "double quote"
  onoremap ad  a"
  xnoremap ad  a"
  onoremap id  i"
  xnoremap id  i"
  "}}}

  " Move in fold
  noremap <unique> z<Up> zk
  noremap <unique> z<Down> zj
  if has("gui_running") "  the <alt> key is only available in gui mode.
    noremap <unique> <M-Up> zk
    noremap <unique> <M-Down> zj
  endif

  " Easy Diff goto
  noremap <unique> <C-Up> [c
  " noremap <unique> <C-k> [c
  noremap <unique> <C-Down> ]c
  " noremap <unique> <C-j> ]c

  " map Up & Down to gj & gk, helpful for wrap text edit
  noremap <unique> <Up> gk
  noremap <unique> <Down> gj

  nnoremap <space> 5jzz
  nnoremap <backspace> 5kzz

  " move vertically by visual line
  noremap j gjzz
  noremap k gkzz
  " noremap gj j
  " noremap gk k
  " Wrapped lines goes down/up to next row, rather than next line in file
  " nnoremap j gj
  " nnoremap k gk
  noremap G Gzz
  noremap gg ggzz
  noremap <C-d> <C-d>zz
  noremap <C-u> <C-u>zz

  " Keep search matches in the middle of the window.
  " zz centers the screen on the cursor, zv unfolds any fold if the cursor
  " suddenly appears inside a fold.
  " nnoremap * *zzzv
  " nnoremap # #zzzv
  " nnoremap n nzzzv
  " nnoremap N Nzzzv
  " noremap n nzz
  " noremap N Nzz
  " noremap * *zz
  " noremap # #zz

  " nnoremap g* g*zz
  " nnoremap g# g#zz
  " Format Jump, center the screen when jumping through the changelist
  nnoremap <silent> g; g;zz
  nnoremap <silent> g, g,zz

  " In normal mode, we use : much more often than ; so lets swap them.
  " nnoremap ; :
  " nnoremap : ;
  " vnoremap ; :
  " vnoremap : ;

  " Use Q for formatting the current paragraph (or selection)
  vnoremap Q gq
  nnoremap Q gqap

  " nnoremap <C-h> :<C-u>help<Space>

  " using Perl/Python-compatible regex syntax
  " Thanks to Steve Losh for this liberating tip
  " See http://stevelosh.com/blog/2010/09/coming-home-to-vim
  " nnoremap / /\v
  " vnoremap / /\v

  " Jump to matching pairs easily, with Tab
  nnoremap <Tab> %
  vnoremap <Tab> %

  " Use shift-H and shift-L for move to beginning/end
  nnoremap H 0
  nnoremap L $

  " cd to the directory containing the file in the buffer
  nnoremap <silent> <leader>cd :lcd %:h<CR>
  nnoremap <silent> <leader>cr :lcd <c-r>=FindGitDirOrRoot()<cr><cr>
  nnoremap <silent> <leader>md :!mkdir -p %:p:h<CR>

  " Get off my lawn
  " nnoremap <Left> :echoe "Use h"<CR>
  " nnoremap <Right> :echoe "Use l"<CR>
  " nnoremap <Up> :echoe "Use k"<CR>
  " nnoremap <Down> :echoe "Use j"<CR>

  """ Code folding options
  nnoremap <leader>f0 :set foldlevel=0<CR>
  nnoremap <leader>f1 :set foldlevel=1<CR>
  nnoremap <leader>f2 :set foldlevel=2<CR>
  nnoremap <leader>f3 :set foldlevel=3<CR>
  nnoremap <leader>f4 :set foldlevel=4<CR>
  nnoremap <leader>f5 :set foldlevel=5<CR>
  nnoremap <leader>f6 :set foldlevel=6<CR>
  nnoremap <leader>f7 :set foldlevel=7<CR>
  nnoremap <leader>f8 :set foldlevel=8<CR>
  nnoremap <leader>f9 :set foldlevel=9<CR>

  " Bash like keys for the command line
  cnoremap <C-A>      <Home>
  cnoremap <C-E>      <End>
  cnoremap <C-K>      <C-U>

  " autocomplete search history in command mode
  cnoremap <C-P>      <Up>
  cnoremap <C-N>      <Down>

  " toggle the background between light and dark
  map <Leader>bg :let &background = ( &background == "dark"? "light" : "dark" )<CR>

  " use ,F to jump to tag in a vertical split
  nnoremap <silent> <Leader>F :let word=expand("<cword>")<CR>:vsp<CR>:wincmd w<cr>:exec("tag ". word)<cr>

  " use ,gf to go to file in a vertical split
  nnoremap <silent> <Leader>gf :vertical botright wincmd f<CR>

  " Auto indent pasted text
  nnoremap p p=`]<C-o>
  nnoremap P P=`]<C-o>

  " ,gt: ctags go to definition in new tab
  nnoremap <leader>gt  <C-w><C-]><C-w>T

  " highlight last inserted text
  nnoremap gV `[v`]

  " ----------------------------------------------------------------------------
  " Quickfix
  " ----------------------------------------------------------------------------
  nnoremap ]q :cnext<cr>zz
  nnoremap [q :cprev<cr>zz
  nnoremap ]l :lnext<cr>zz
  nnoremap [l :lprev<cr>zz

  " ----------------------------------------------------------------------------
  " Buffers
  " ----------------------------------------------------------------------------
  nnoremap ]b :bnext<cr>
  nnoremap [b :bprev<cr>

  " ----------------------------------------------------------------------------
  " Tabs
  " ----------------------------------------------------------------------------
  nnoremap ]t :tabn<cr>
  nnoremap [t :tabp<cr>
  " }}}

  "-----------------------------------------------------------
  " Functions
  "-----------------------------------------------------------

  "-----------------------------------------------------------
  " Switch to buffer according to file name
  function! SwitchToBuf(filename)
    "let fullfn = substitute(a:filename, "^\\~/", $HOME . "/", "")
    " find in current tab
    let bufwinnr = bufwinnr(a:filename)
    if bufwinnr != -1
      exec bufwinnr . "wincmd w"
      return
    else
      " find in each tab
      tabfirst
      let tab = 1
      while tab <= tabpagenr("$")
        let bufwinnr = bufwinnr(a:filename)
        if bufwinnr != -1
          exec "normal " . tab . "gt"
          exec bufwinnr . "wincmd w"
          return
        endif
        tabnext
        let tab = tab + 1
      endwhile
      " not exist, new tab
      exec "tabnew " . a:filename
    endif
  endfunction

  function! CmdLine(str)
    exe "menu Foo.Bar :" . a:str
    emenu Foo.Bar
    unmenu Foo
  endfunction

  function! VisualSearch(direction) range
    let l:saved_reg = @"
    execute "normal! vgvy"

    let l:pattern = escape(@", '\\/.*$^~[]')
    let l:pattern = substitute(l:pattern, "\n$", "", "")

    if a:direction == 'b'
      execute "normal ?" . l:pattern . "^M"
    elseif a:direction == 'gv'
      call CmdLine("vimgrep " . '/'. l:pattern . '/' . ' **/*.')
    elseif a:direction == 'f'
      execute "normal /" . l:pattern . "^M"
    elseif a:direction == 'replace'
      call CmdLine("%s" . '/'. l:pattern . '/')
    else
      execute "normal /" . l:pattern . "^M"
    endif

    let @/ = l:pattern
    let @" = l:saved_reg
  endfunction

  "Basically you press * or # to search for the current selection !! Really useful
  " vnoremap <silent> * :call VisualSearch('f')<CR>
  " vnoremap <silent> # :call VisualSearch('b')<CR>
  " vnoremap <silent> gv :call VisualSearch('gv')<CR>

  noremap <Leader>ch :call SetColorColum()<CR>
  function! SetColorColum()
    let col_num = virtcol(".")
    let cc_list = split(&cc, ',')
    if count(cc_list, string(col_num)) <= 0
      execute "set cc+=".col_num
    else
      execute "set cc-=".col_num
    endif
  endfunction

  cnoremap $q <C-\>eDeleteTillSlash()<cr>

  " autocmd GUIEnter * call libcallnr("vimtweak.dll", "SetAlpha", 230)

  " retab
  fu! Retab()
    :retab
    :%s/\s\+$//
  endfunction

  " Remap VIM 0 to first non-blank character
  map 0 ^
  nnoremap <Home> ^
endif
"}}} Extended ----------------------------------------------

" {{{ Fisilink ---------------------------------------------

augroup my_fileheader
  autocmd!
  autocmd BufNewFile *.spec call FHHeader()
  " when create a new file, insert header
  autocmd BufNewFile *.v,*.sv,*.svh exec ":call SetFSLTitle()"
augroup END

noremap <Leader>fh :call FHHeader()<CR>
function! FHHeader()
  let s:comment = "//"
  let s:commentline = s:comment .   "----------------------------------------------------------------------"
  let s:company = s:comment .       " Copyright (c) " . strftime ("%Y") . ", Fiberhome Telecommunication Technology Co., Ltd."
  let s:department = s:comment .    " Microelectronics Dept."
  let s:copyright = s:comment .     " All rights reserved."
  let s:file = s:comment .          " FileName    : " . expand("%:t")
  let s:author = s:comment .        " Author      : " . g:vimrc_author
  let s:email= s:comment .          " EMail       : " . g:vimrc_email
  let s:version = s:comment .       " Version     : 1.0"
  let s:created = s:comment .       " Created     : " . strftime ("%Y-%m-%d %H:%M:%S")
  let s:modified = s:comment .      " Modified    : " . strftime ("%Y-%m-%d %H:%M:%S")
  let s:description= s:comment .    " Description : "
  let s:hierarchy= s:comment .      " Hierarchy   : "
  let s:history= s:comment .        " History"
  let s:history_author= s:comment . "     Author   :"
  let s:history_date= s:comment .   "     Date     :"
  let s:history_rev= s:comment .    "     Revision :"

  call append (0, [s:commentline,
        \ s:company,
        \ s:department,
        \ s:copyright,
        \ s:comment,
        \ s:file,
        \ s:author,
        \ s:email,
        \ s:version,
        \ s:created,
        \ s:modified,
        \ s:description,
        \ s:hierarchy,
        \ s:commentline,
        \ s:history,
        \ s:history_author,
        \ s:history_date,
        \ s:history_rev,
        \ s:commentline])
endfunction

" set header function
func! SetFSLTitle()
  call setline(1          , "\//                              ;;;;`';;;.                                                                            ")
  call append(line(".")   , "\//                            ,`;;;;`';;;;,                                                                           ")
  call append(line(".")+1 , "\//                          ::` :;;: `;;;';                                                                           ")
  call append(line(".")+2 , "\//                        `    `` `    ;;;;                                                                           ")
  call append(line(".")+3 , "\//              `:'++++++++++++++      .';;                                                                           ")
  call append(line(".")+4 , "\//             ;+'+''++'+'+++'++:      ,;;;                                                                           ")
  call append(line(".")+5 , "\//            '+++++++++'+'+++++       ;''`                                                                           ")
  call append(line(".")+6 , "\//           ;+''''+''''+++++'',      `;''                                                                            ")
  call append(line(".")+7 , "\//           ++''+++++++''++++:       ;;'`                                                                            ")
  call append(line(".")+8 , "\//          `++++++'''''';;:.        :;;:                                                                             ")
  call append(line(".")+9 , "\//          ,+++++'                 .;;;                                                                              ")
  call append(line(".")+10, "\//          ;++++++                `;;'                                                                               ")
  call append(line(".")+11, "\//          '+++++'               `;;'                                                                                ")
  call append(line(".")+12, "\//        ,.'+++++'              `';;                                                                                 ")
  call append(line(".")+13, "\//       ;;`++++++;`.,:;''''''  `';;                                                                                  ")
  call append(line(".")+14, "\//      ;;. '++++++++++''++'+. `';;                                                                                   ")
  call append(line(".")+15, "\//     '': `+++++++''++++'+'+ ,;',                                                                                    ")
  call append(line(".")+16, "\//    ;;;  .++++'''++''+++++`;;;`   +'''''''    ;+''+';   +++'''+' ++''+''+     :+'''+++,+''+'+'   ++'+,+'''''':.+'''+")
  call append(line(".")+17, "\//   :';   ;'++++'++''''++',;;:      +++++`   .+'    +'    '++++`   ''+'+.       `+'+'+   ,'+'+'    ''   +''++`  ,''` ")
  call append(line(".")+18, "\//  .;;`   '++++'''';;:,,.`;;`       +++++    '':    :+    '++++    ;'+++         +'++:    ''+++,   :.   '''+'   ':   ")
  call append(line(".")+19, "\//  ';:    ++++'''       ,;.         +'+''   '++;     '    ++++'    ++'+'        `'+++.   `:+'+'+   ;    +++++  ;,    ")
  call append(line(".")+20, "\// ,;;     ''++'';  .   ;,           +'+':   +'++,    ;    '+++:    +''+'        ,++++`   .`++''+`  '    ++++; ;'`    ")
  call append(line(".")+21, "\// ';;     ++'''+. ;  `,            `+'+'.   ++++++:       ++++.    +''+:        ;'+++    ; .++++'  '    ++++,'+'+    ")
  call append(line(".")+22, "\//`;;.     '+++; ,;  `              .+'++`   '+++'+++'    .++++`    ''++,        ''+++    '  '++++  '   `''+++'+++'   ")
  call append(line(".")+23, "\//,''.    .'+. .;:                  :''++     '+''+++''   :'+'+    .++++`        ++++'    '  :++++; ;   ,'++'`++'++`  ")
  call append(line(".")+24, "\//:;';       ,;;'                   '+'++      ;+'+'+++`  ;+'++    :'+++         +++';    '   +'+++`,   '+'+' :+'++;  ")
  call append(line(".")+25, "\//,;;;;.`.:;;''++                   '+'+'   '    ;'++'+`  ++'++    ;++'+         +'+',    ;   ''++''`   '+'++  ''+'+  ")
  call append(line(".")+26, "\//`;;;;;;';;;''+'                   ++'+'   +`    `++++`  ++++'    '++'+     `: `'++'`   `.   `+'+++    ++++'  '+''+` ")
  call append(line(".")+27, "\// .';;;;;;'+'++;                   +'++:   +'     ;+''   ++++:    +++''     +  ,++'+    ,`    +'''+    '+'':  .++++: ")
  call append(line(".")+28, "\//   ,::. ''++'+,                  `++++.   ++     '''`  `'+++.    +'++'   .':  '++'+    '`    .++++   `++++,  .+++++ ")
  call append(line(".")+29, "\//       `++++'+`                  '++++;  `+++   .''`   ''+'';   ;'++++::'++  `+'''+`  ,+;     +'''   '++++;  '++'+'`")
  call append(line(".")+30, "\//       .''''''                  ,,,,,,,,  `:'+'+'.    ,,,,,,,, ,,,,,,,,,,,. .,,,,,,,`,,,,.    .,,.  ,,,,,,,`,,,,,,,,")
  call append(line(".")+31, "\//--------------------------------------------------------------------------------------------------------------------")
  call append(line(".")+32, "\// Copyright (c), Fisilink Microelectronics Technology Co., Ltd")
  call append(line(".")+33, "\// Author      : ".$USER)
  call append(line(".")+34, "\// Created Time: ".strftime("%c"))
  call append(line(".")+35, "")
  call append(line(".")+36, "\// Date        : ".strftime("%Y-%m-%d %H:%M:%S"))
  call append(line(".")+37, "\// Revision    : 1.0")
  call append(line(".")+38, "\// Description : ")
  call append(line(".")+39, "\//--------------------------------------------------------------------------------------------------------------------")
  call append(line(".")+40, "")
  " go to end of file
  autocmd BufNewFile * normal G
endfunc
"for c++
iab for_ for () begin<enter><enter>end
iab if_ if () begin<enter><enter>end
iab ife_ if () begin<enter><enter>end<enter>else begin<enter><enter>end
iab ifee_ if () begin<enter><enter>end<enter>else if () begin<enter><enter>end<enter>else begin<enter><enter>end
"for sv/v
iab al_ always @(posedge clk or negedge rst_n) begin<enter>if (!rst_n) begin<enter><enter>end else begin<enter><enter>end<enter>end

iab info_ `uvm_info (get_name(), $psprintf (""), UVM_NONE);
iab warning_ `uvm_warning (get_name(), $psprintf (""));
iab error_ `uvm_error (get_name(), $psprintf (""));
iab fatal_ `uvm_fatal (get_name(), $psprintf (""));

iab sq_ sequence s_xx;<enter><enter>endsequence<enter><enter>property p_xx;<enter>@(posedge clk) s_xx;<enter>endproperty<enter><enter>assert_xx : assert property (p_xx);

map     <F9>   a<C-R>='// '.$USER.strftime(" @ %Y-%m-%d %H:%M")<CR>

function! AddCommentBlock()
  let a:comment_line="////////////////////////////////////////////////////////////////////////////////"
  let a:name_line="// struct      : "
  let a:dscp_line="// description : "

  call append(line(".")   , a:comment_line)
  call append(line(".")+1 , a:name_line)
  call append(line(".")+2 , a:dscp_line)
  call append(line(".")+3 , a:comment_line)
endfunction

function! MakeFSLStruct(name)
  let a:comment_line="////////////////////////////////////////////////////////////////////////////////"
  let a:struct_name_line="// struct      : " . a:name
  let a:struct_dscp_line="// description : "

  call append(line(".")   , a:comment_line)
  call append(line(".")+1 , a:struct_name_line)
  call append(line(".")+2 , a:struct_dscp_line)
  call append(line(".")+3 , a:comment_line)
  call append(line(".")+4 , "")
  call append(line(".")+5 , "typedef struct {")
  call append(line(".")+6 , "")
  call append(line(".")+7 , "} " . a:name . ";")
endfunction

"}}} Fisilink ----------------------------------------------


" Strip trailing whitespace
function! <SID>StripTrailingWhitespaces()
  " Preparation: save last search, and cursor position.
  let _s=@/
  let l = line(".")
  let c = col(".")
  " Do the business:
  %s/\s\+$//e
  " Clean up: restore previous search history, and cursor position
  let @/=_s
  call cursor(l, c)
endfunction
autocmd BufWritePre * :call <SID>StripTrailingWhitespaces()
" autocmd FileType c,cpp,scss,css,html,erb,java,php,ruby,python,javascript autocmd BufWritePre <buffer> :call <SID>StripTrailingWhitespaces()
" nnoremap <leader>cs :call <SID>StripTrailingWhitespaces()<cr>


" Search for the current selection
function! s:VSetSearch()
  let temp = @s
  norm! gv"sy
  let @/ = '\V' . substitute(escape(@s, '/\'), '\n', '\\n', 'g')
  let @s = temp
endfunction

function! MyFormatXml()
  set filetype=xml
  :%s/></>\r</g
  " :%s/<\([^>]\)*>/\r&/g<CR>
  :normal gg=G<CR>
endfunction

nmap <leader>ml :call MyFormatXml()<CR>
nmap <F8> :call MyFormatXml()<CR>



" ============================================================================
" LOCAL VIMRC {{{
" ============================================================================
let g:local_vimrc = fnamemodify(resolve(expand('<sfile>')), ':p:h').'/vimrc.local'
if filereadable(g:local_vimrc)
  execute 'source' g:local_vimrc
endif

" }}}

set secure

" vim: fdm=marker ts=2 sts=2 sw=2

