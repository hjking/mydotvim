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

let g:dotvim_settings = {}
" change the default directory where all miscellaneous persistent files go
let g:dotvim_settings.cache_dir=$HOME.'/.vim-cache'

let s:settings = {}
" auto complete
if (v:version > 703 || v:version == 703 && has('patch885')) && has('lua')
  let s:settings.autocomplete_method = 'neocomplete' " ycm/neocomplcache
else
  let s:settings.autocomplete_method = 'neocomplcache' " ycm/neocomplete
endif
" fuzzy finder
if v:version < 703
  let s:settings.finder_method = 'ctrlp'
else
  let s:settings.finder_method = 'unite'
endif

" snippets
let s:settings.snippet_method = 'snipmate' " neosnippet/ultisnips

" statusline
if v:version < 702
  let s:settings.statusline_method = 'lightline'
else
  let s:settings.statusline_method = 'airline'
endif

" let s:cache_dir = get(g:dotvim_settings, 'cache_dir', '~/.vim-cache')
" let g:cache_dir=$HOME.'/.vim-cache'

"---------------------------------------------------------------
"""""""""""""""""""""" Basic """""""""""""""""""""""""""""""""""
"---------------------------------------------------------------
"{{{
"-------------------------------------------------------------------------------
"  1 important
"-------------------------------------------------------------------------------
set all& "reset everything to their defaults

" Get out of VI's compatible mode
" Use Vim settings, rather then Vi settings.
" This must be first, because it changes other options as a side effect.
set nocompatible                " not use vi keyboard mode

filetype off

"-----------------------------------------------------------
" FileType Detecting
" Enable file type detection. Use the default filetype settings.
" Also load indent files, to automatically do language-dependent indenting.
"-----------------------------------------------------------
" filetype on
" filetype plugin on
" filetype indent on
if has('autocmd')
  filetype plugin indent on
endif

"-----------------------------------------------------------
" Platform
"-----------------------------------------------------------
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

let os = MySys()
let s:is_windows = has('win32') || has('win64')
let s:is_cygwin = has('win32unix')
let s:is_macvim = has('gui_macvim')

if os == "windows"
  let g:vimfiles = split(&runtimepath, ',')[1]
elseif os == "linux"
  let g:vimfiles = split(&runtimepath, ',')[0]
endif

set runtimepath=$HOME/.vim,$VIM/vimfiles,$VIMRUNTIME,$VIM/vimfiles/after,$HOME/.vim/after

if os == "windows"
  language message en                   " message language
  " language message en_US                   " message language
  " language message zh_CN.UTF-8
  " lang messages zh_CN.UTF-8 " 解决consle输出乱码
elseif os == "linux"
  language message C
endif

" source $VIMRUNTIME/vimrc_example.vim
if os == "windows"
  " source $VIMRUNTIME/mswin.vim      " Win behaviour
endif

runtime! ftplugin/man.vim

" set mapleader
let mapleader = ","
let g:mapleader=","

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

syntax on

"-------------------------------------------------------------------------------
"  2 moving around, searching and patterns
"-------------------------------------------------------------------------------
" set whichwrap+=<,>,[,]      " Allow wrap only when cursor keys are used
if os == "windows"
  set path+=D:\cygwin\bin
elseif os == "linux"
  set path+=/usr/bin
endif
if has("gui_running")
  if has("gui_win32")     " Win OS
    set wrap            " Wrap line
"   elseif has("x11")
"   elseif has("gui_gtk2")
  endif
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

"-------------------------------------------------------------------------------
"  3 tags
"-------------------------------------------------------------------------------
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
if &listchars ==# 'eol:$'
  set listchars=tab:>\ ,trail:-,extends:>,precedes:<,nbsp:+
  " set listchars=tab:\>\ ,trail:.,extends:>,precedes:<
  " set listchars=tab:▸\,trail:-,extends:>,precedes:<,nbsp:+
endif
set number                      " display line number
set numberwidth=1
set lazyredraw                  " Don't redraw while executing macros


"-------------------------------------------------------------------------------
"  5 syntax, highlighting and spelling
"-------------------------------------------------------------------------------
try
  colorscheme murphy
catch
endtry

set background=dark

"-------------------------------------------------------------------------------
"  6 multiple windows
"-------------------------------------------------------------------------------

set equalalways " Multiple windows, when created, are equal in size
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
if os == "windows"
  set mouse=a
elseif os == "linux"
  set mouse=va
endif
" set mousemodel=extend
set nomousehide                 " Hide the mouse when typing text

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
  if os == "windows"
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
if has('unnamedplus')
  set clipboard& clipboard+=unnamedplus
else
  set clipboard& clipboard+=unnamed
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
set complete+=.,w,b,kspell,ss      " current buffer, other windows' buffers, dictionary, spelling
set complete+=k                 " scan the files given with the 'dictionary' option
set completeopt=longest,menuone    " Insert mode completetion
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
set smartindent             " Do smart autoindenting when starting a new line
set cindent                 " Enables automatic C program indenting

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
" set scrollbind      " 左右两侧的屏幕滚动是同步的
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
" set wildmode=longest:full,full
set wildmode=list:longest,full  " command <Tab> completion, list matches, then longest common part, then all"
set wildignore+=.svn,CVS,.git,.hg,*.bak,*.e,*.obj,*.swp,*.pyc,*.o,*.lo,*.la,*.exe,*.db,*.old,*.mdb,*~,~*,*.so " wildmenu: ignore these extensions
if os == "windows"
  set wildignore+=*/.git/*,*/.hg/*,*/.svn/*,*/CVS/*,*/.DS_Store
else
  set wildignore+=.git\*,.hg\*,.svn\*,CVS\*
endif
set wildmenu                    " command-line completion operates in an enhanced mode

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
if os == "windows"
  if exists('+shellslash')
    set shellslash      " Exchange path separator
  endif
endif

"-------------------------------------------------------------------------------
" 25 language specific
"-------------------------------------------------------------------------------
set iskeyword+=_,$,@,%,#,-  " Keywords for search and some commands, no wrap
set isfname-==  " remove = from filename characters

"-------------------------------------------------------------------------------
" 26 multi-byte characters
"-------------------------------------------------------------------------------
if has("multi_byte")
  if v:lang =~? '^\(zh\)\|\(ja\)\|\(ko\)'
    set ambiwidth=double
  endif
  " Set fileencoding priority
  if getfsize(expand("%")) > 0
    set fileencodings=ucs-bom,utf-8,cp936,gb18030,big5,euc-jp,sjis,cp932,cp949,euc-kr,latin1
  else
    set fileencodings=cp936,cp932,cp949,big5,euc-jp,euc-kr,latin1
  endif
  " CJK environment detection and corresponding setting
  if v:lang =~ "^zh_CN"
  " Use cp936 to support GBK, euc-cn == gb2312
    " set encoding=chinese
    set fileencoding=chinese
  elseif v:lang =~ "^zh_TW"
    set fileencoding=taiwan
  elseif v:lang =~ "^ko"
    set fileencoding=euc-kr
  elseif v:lang =~ "^ja_JP"
    set fileencoding=cp932              " euc-jp
  elseif v:lang =~ "utf8$"  || v:lang =~ "UTF-8$" || v:lang =~ "^en_US"
    " Detect UTF-8 locale, and replace CJK setting if needed
    set fileencoding=utf-8
  endif
  if &encoding ==# 'latin1' && has('gui_running')
    set encoding=utf-8
  endif
  let &termencoding = &encoding
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

" HighLight Character
highlight OverLength ctermbg=red ctermfg=white guibg=red guifg=white
" highlight pop menu
highlight Pmenu ctermbg=8 guibg=#606060
highlight PmenuSel ctermbg=1 guifg=#dddd00 guibg=#1f82cd
highlight PmenuSbar ctermbg=0 guibg=#d6d6d6
highlight LineNr ctermbg=0
highlight FoldColumn ctermbg=0
highlight ShowMarksHLl ctermbg=0
highlight ShowMarksHLu ctermbg=0
highlight ShowMarksHLo ctermbg=0
highlight ShowMarksHLm ctermbg=0

":match OverLength '\%200v.*'

if v:version > 703
  set cryptmethod=blowfish
endif

" Specify the behavior when switching buffers
try
  set switchbuf=useopen,usetab,newtab
  set showtabline=2
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
if has("autocmd")
  " Set augroup
  augroup MyAutoCmd
    autocmd!

    " automatically rebalance windows on vim resize
    autocmd VimResized * :wincmd =

    " Check timestamp more for 'autoread'.
    autocmd WinEnter * checktime

    autocmd BufReadPre,BufNewFile,BufRead *.vp,*.sva setfiletype systemverilog
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

    " remove all trailing whitespace in a file
    autocmd BufWritePre * :%s/\s\+$//e

    " Automatically resize vertical splits
    " autocmd WinEnter * :set winfixheight
    " autocmd WinEnter * :wincmd =

    autocmd BufNewFile,BufRead .tmux.conf*,tmux.conf* setf tmux
    autocmd FileType css,scss setlocal foldmethod=marker foldmarker={,}
    autocmd FileType css,scss nnoremap <silent> <leader>S vi{:sort<CR>
    autocmd FileType markdown setlocal nolist
    autocmd FileType vim setlocal fdm=indent keywordprg=:help
    autocmd FileType xml,html vmap <C-o> <ESC>'<i<!--<ESC>o<ESC>'>o-->
    autocmd FileType java,c,cpp,cs vmap <C-o> <ESC>'<o/*<ESC>'>o*/
    autocmd FileType html,text,php,vim,c,java,xml,bash,shell,perl,systemverilog,vimwiki set textwidth=80
    autocmd FileType bash,shell set ts=2
    autocmd FileType help set nonu
    autocmd FileType lisp set ts=2 softtabstop=2
  augroup END
endif " has("autocmd")

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
if has('statusline')
  set laststatus=2           " always show the status line
  "highlight StatusLine guifg=SlateBlue guibg=Yellow
  "highlight StatusLine guifg=SlateBlue guibg=#008800
  highlight StatusLine NONE
  highlight StatusLineNC NONE
  " current window
  highlight StatusLine guifg=orange guibg=#008800 gui=underline ctermfg=yellow
  " highlight StatusLine guifg=orange guibg=#008800 gui=underline term=bold cterm=bold ctermfg=yellow
  " not current window
  highlight StatusLineNC guifg=Gray guibg=white ctermfg=lightgrey
  " highlight StatusLineNC guifg=Gray guibg=white ctermfg=gray ctermbg=white
  highlight User1 guifg=yellow
  highlight User2 guifg=lightblue
  highlight User3 guifg=red
  highlight User4 guifg=cyan
  highlight User5 guifg=lightgreen
  highlight User6 gui=bold,inverse guifg=red term=bold,inverse ctermfg=blue " ctermbg=brown
  highlight User7 gui=bold,inverse guifg=red term=bold,inverse cterm=bold ctermfg=green ctermbg=red
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
endif

"}}} Basic -------------------------------------------------------------

"---------------------------------------------------------------
"""""""""""""""""""""" Filetypes """""""""""""""""""""""""""""""
"---------------------------------------------------------------
"{{{
if g:load_vimrc_filetype

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
    autocmd FileType python setlocal formatoptions+=croq smartindent
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
  if s:is_windows && !s:is_cygwin
    " ensure correct shell in gvim
    set shell=c:\windows\system32\cmd.exe
  endif

  if exists('$TMUX')
      set term=screen-256color
  endif

  " Enable file type detection.
  " Use the default filetype settings, so that mail gets 'tw' set to 72,
  " 'cindent' is on in C files, etc.
  " Also load indent files, to automatically do language-dependent indenting.
  " auto detect filetype and load setting
  "filetype plugin indent on

  " For all text files set 'textwidth' to 71 characters.
  "autocmd FileType text setlocal textwidth=71

  " zope dtml
  "autocmd BufNewFile,BufRead *.dtml setf dtml

  " skeleton file
  " use template
  "autocmd BufNewFile test*.py 0r ~/.vim/skeleton/test.py
  "autocmd BufNewFile alltests.py 0r ~/.vim/skeleton/alltests.py
  "autocmd BufNewFile *.py 0r ~/.vim/skeleton/skeleton.py

  " shell script
  "autocmd fileType sh setlocal sw=4 | setlocal sta

  " RedHat spec file
  "autocmd BufNewFile,BufReadPost *.spec setf spec

  " Brainfuck file
  "autocmd BufNewFile,BufReadPost *.b setf brainfuck

  " When editing a file, always jump to the last known cursor position.
  " Don't do it when the position is invalid or when inside an event handler
  " (happens when dropping a file on gvim).
  "autocmd BufReadPost *
   " \ if line("'\"") > 0 && line("'\"") <= line("$") |
   " \   exe :"normal g`\"" |
   " \ endif
" endif :"" has("autocmd")
endif
"}}} Filetypes -------------------------------------------------------------


"---------------------------------------------------------------
"""""""""""""""""""""" Plugin_config """""""""""""""""""""""""""
"---------------------------------------------------------------
"{{{
if g:load_vimrc_plugin_config

  "-----------------------------------------------------------
  """ pathogen.vim
  " auto load all plugins
  "{{{
    let g:pathogen_not_loaded_plugin = 1
    let g:path_of_vimrc_tmp = expand('<sfile>:h')
    let g:path_of_vimrc = substitute(g:path_of_vimrc_tmp, "\\", "/", "g")
    " if os == "windows"
    "   source $VIM/vimfiles/bundle/pathogen/autoload/pathogen.vim
    " elseif os == "linux"
    "   source ~/.vim/bundle/pathogen/autoload/pathogen.vim
    " endif
    runtime! bundle/pathogen/autoload/pathogen.vim
    " disable bundle
    let g:pathogen_blacklist = []

    if v:version < 700 || (v:version == 700 && !has('patch167'))
      call add(g:pathogen_blacklist, 'tagbar')
    endif

    if v:version < 701
      call add(g:pathogen_blacklist, 'lookupfile')
    endif

    if v:version < 702
      call add(g:pathogen_blacklist, 'airline')
      call add(g:pathogen_blacklist, 'neocomplcache')
      call add(g:pathogen_blacklist, 'neosnippet')
      call add(g:pathogen_blacklist, 'indent-guides')
    endif

    if v:version >= 702
      call add(g:pathogen_blacklist, 'lightline')
    endif

    if v:version < 702 || !has('float')
      call add(g:pathogen_blacklist, 'L9')
    endif
      call add(g:pathogen_blacklist, 'FuzzyFinder')

    if v:version < 703
    "    call add(g:pathogen_blacklist, 'niceblock')
      call add(g:pathogen_blacklist, 'easymotion')
      call add(g:pathogen_blacklist, 'unite')
    endif

    if v:version < 703 || !has('python')
      call add(g:pathogen_blacklist, 'gundo')
    endif

    " Disable on purpose
    " if exists('g:pathogen_not_loaded_plugin')
    if v:version < 703 || !has('patch584')
      call add(g:pathogen_blacklist, 'YouCompleteMe')
    endif

    " disable plugins
    call add(g:pathogen_blacklist, 'syntastic')

    call pathogen#infect()
    " execute pathogen#infect()
    call pathogen#helptags()
    " pathogen 管理vba格式的插件
    "   :e name.vba
    "   :!mkdir $VIM\vimfiles\bundle\name
    "   :UseVimball $VIM\vimfiles\bundle\name

    ""if filereadable(expand("~/.vimrc.bundles.local"))
    ""    source ~/.vimrc.bundles.local
    ""endif

  " }}}

  "-----------------------------------------------------------
  " Solarized
  " Allow color schemes to do bright colors without forcing bold.
  if &t_Co == 8 && $TERM !~# '^linux\|^Eterm'
    set t_Co=16
  endif
  " set t_Co=256
  if pathogen#is_disabled('solarized') == 0
    " let hour = strftime("%H")
    " if 6 <= hour && hour < 18
    "   set background=light
    " else
    "   set background=dark
    " endif
    let g:solarized_termtrans=1
    let g:solarized_termcolors=256
    let g:solarized_contrast="high"
    let g:solarized_visibility="high"
  endif
  try
    let base16colorspace=256
    colorscheme solarized
    " set background=light
  catch
    colorscheme murphy
  endtry

  "-----------------------------------------------------------
  """ python-mode
  " Disable pylint checking every save
  " {{{
    if pathogen#is_disabled('python-mode') == 0
      let g:pymode_lint_write = 0
      let g:pymode_lint = 1
      let g:pymode_lint_checker = "pyflakes,pep8"

      " Set key 'R' for run python code
      " let g:pymode_run_key = 'R'
      let g:pymode_run_key = '<leader>r'

      " Support virtualenv
      let g:pymode_virtualenv = 1

      " Enable breakpoints plugin
      let g:pymode_breakpoint = 1
      let g:pymode_breakpoint_key = '<leader>b'

      " syntax highlighting
      let g:pymode_syntax = 1
      let g:pymode_syntax_all = 1
      let g:pymode_syntax_indent_errors = g:pymode_syntax_all
      let g:pymode_syntax_space_errors = g:pymode_syntax_all

      " Don't autofold code
      let g:pymode_folding = 0
    endif
  " }}}

  "-----------------------------------------------------------
  " TagList
  " {{{
    if pathogen#is_disabled('taglist') == 0
      if os == "windows"
        let Tlist_Ctags_Cmd = g:vimfiles . '/ctags58/ctags.exe'           "设置ctags的路径
      elseif os == "linux"
        let Tlist_Ctags_Cmd = '/usr/bin/ctags'
      endif
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
    endif
  " }}}

  "-----------------------------------------------------------
  " tagbar
  " {{{
    if pathogen#is_disabled('tagbar') == 0
      if os == "windows"
        let g:tagbar_ctags_bin = g:vimfiles . '\ctags58\ctags.exe'
      elseif os == "linux"
        let g:tagbar_ctags_bin = 'ctags'
      endif
      let g:tagbar_width = 20
      let g:tagbar_autofocus = 1
      let g:tagbar_sort = 1
      let g:tagbar_compact = 1
      let g:tagbar_expand = 1
      let g:tagbar_singleclick = 1
      let g:tagbar_usearrows = 1
      let g:tagbar_autoshowtag = 1
      let g:tagbar_show_visibility = 1
      " let g:tagbar_autoclose = 1    " auto close after open tag
      nnoremap <silent><leader>tb :TagbarToggle<CR>
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
    endif
  " }}}

  "-----------------------------------------------------------
  " File Explorer
  "-----------------------------------------------------------
  "let g:explVertical=1                   " split verticially
  "window size
  "let g:explWinSize=35                   " width of 35 pixels
  "let g:explSplitLeft=1
  "let g:explSplitBelow=1

  "-----------------------------------------------------------
  "Tree explorer
  "-----------------------------------------------------------
  "let g:Tlist_Enable_Fold_Column=0
  "let g:treeExplVertical=1
  "let g:treeExplWinSize=30
  " let g:explSplitLeft=1
  " let g:explSplitBelow=1
  " "Hide some files
  " let g:explHideFiles='^\.,.*\.class$,.*\.swp$,.*\.pyc$,.*\.swo$,\.DS_Store$'
  " "Hide the help thing..
  " let g:explDetailedHelp=0

  "-----------------------------------------------------------
  " MiniBufExplorer
  " {{{
    if pathogen#is_disabled('minibufexpl') == 0
      let loaded_minibufexplorer = 0         " *** Disable minibuffer plugin
      let g:miniBufExplMapCTabSwitchBufs = 1
      let g:miniBufExplMapWindowNavVim = 1
      let g:miniBufExplMapWindowNavArrows = 1
      let g:miniBufExplModSelTarget = 1
      let g:miniBufExplSplitBelow = 1
      let g:miniBufExplMaxSize = 2
      let g:miniBufExplUseSingleClick = 1    " select by single click
      " autocmd BufRead,BufNew :call UMiniBufExplorer
      " noremap ,be :MBEToggle<CR>
    endif
  " }}}

  "-----------------------------------------------------------
  "Matchit
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

  "-----------------------------------------------------------
  " hl-matchit
  " {{{
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
  " Netrw  File Explorer :e <PATH>
  " {{{
  "  if pathogen#is_disabled('netrw') == 0
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
  "  endif
  " }}}

  "-----------------------------------------------------------
  " NERD Tree  File Manager
  " o     open file                           " t     open file in new tab
  " go    open file,but cursor in NERDtree    " T     same as t, but focus on the current tab
  " tab   open file in a split window         " !     execute current file
  " x     close the current nodes parent      " X     Recursively close all children of the current node
  " e     open a netrw for the current dir
  " {{{
    if pathogen#is_disabled('nerdtree') == 0
      noremap <leader>nt :NERDTreeToggle<CR>
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

    endif
  " }}}

  "-----------------------------------------------------------
  " NERDTree-tabs
  " {{{
    if pathogen#is_disabled('nerdtree-tabs') == 0
      noremap <leader>nn <plug>NERDTreeTabsToggle<CR>
      let g:nerdtree_tabs_open_on_console_startup=0   " NOT Open NERDTree on console vim startup
      let g:nerdtree_tabs_open_on_gui_startup=0       " Open NERDTree on gvim/macvim startup
    endif
  " }}}

  "-----------------------------------------------------------
  "Calendar
  " :Calendar         "Open calendar   " :CalendarH        "打开水平的日历窗口
  "-----------------------------------------------------------
  "let g:calendar_diary=<PATH>
  " let g:calendar_wruler = '日 一 二 三 四 五 六'
  let g:calendar_mark = 'left-fit'
  let g:calendar_focus_today = 1
  noremap <Leader>ca :Calendar<CR>

  "-----------------------------------------------------------
  " SVN Command
  " {{{
    if pathogen#is_disabled('svnj') == 0
      let g:svnj_custom_statusbar_ops_hide = 1
      if os == "windows"
        " let g:svnj_cache_dir=$HOME.'/.vim-cache'
        let g:svnj_cache_dir=g:dotvim_settings.cache_dir
      endif
    endif
  " }}}

  "-----------------------------------------------------------
  " showmarks setting
  " <Leader>mt  - Toggle whether marks are displayed or not.
  " <Leader>mo  - Turn ShowMarks on, and displays marks.
  " <Leader>mh  - Clear mark on current line.
  " <Leader>ma  - Clear all marks.
  " <Leader>mm  - Places next available mark.
  " {{{
    if pathogen#is_disabled('ShowMarks') == 0
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
      let g:showmarks_no_mappings = 1
      nnoremap mt <Plug>ShowMarksToggle
    endif
  " }}}

  "-----------------------------------------------------------
  " mark setting
  " {{{
    nnoremap <silent> <leader>hl <Plug>MarkSet
    vnoremap <silent> <leader>hl <Plug>MarkSet
    nnoremap <silent> <leader>hh <Plug>MarkClear
    vnoremap <silent> <leader>hh <Plug>MarkClear
    nnoremap <silent> <leader>hr <Plug>MarkRegex
    vnoremap <silent> <leader>hr <Plug>MarkRegex
  " }}}

  "-----------------------------------------------------------
  " Vimwiki
  " {{{
    if pathogen#is_disabled('vimwiki') == 0
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
    endif
  " }}}

  "-----------------------------------------------------------
  " timestamp
  " {{{
    " let loaded_timestamp = 1
    " let g:timestamp_regexp = '\v\C%(<Last %([cC]hanged?|[Mm]odified)\s*:\s+)@<=.*$|2010-08-13 09:49:39'
    " let g:timestamp_regexp = '\v\C%(<Last %([cC]hanged?|[Mm]odified|[Uu]pdated)\s*:\s+)@<=\d{4}-\d{2}-\d{2} \d{2}:\d{2}:\d{2}|2010-11-01 12:57:29'
    let g:timestamp_regexp = '\v\C%(<%([cC]hanged?|[Mm]odified|[Uu]pdated)\s*:\s+)@<=\d{4}-\d{2}-\d{2} \d{2}:\d{2}:\d{2}|2010-11-01 12:57:29'
    let g:timestamp_rep = '%Y-%m-%d %H:%M:%S'
    let g:timestamp_modelines = 20
  " }}}

  "-----------------------------------------------------------
  " yankring.vim
  " {{{
    if pathogen#is_disabled('yankring') == 0
      let g:yankring_enabled=0
      let g:yankring_history_file = '.vim-cache/yankring_history'
      noremap <leader>yr :YRShow<cr>
    endif
  " }}}

  "-----------------------------------------------------------
  " Colorful Parentheses
  " rainbow_parentheses
  " {{{
    let g:rbpt_colorpairs = [
        \ ['White',       'Gray'],
        \ ['Darkblue',    'RoyalBlue3'],
        \ ['darkgray',    'Magenta'],
        \ ['darkmagenta', 'Cyan'],
        \ ['darkgreen',   'Purple'],
        \ ['darkcyan',    'Red'],
        \ ['darkred',     'Violet'],
        \ ['darkmagenta', 'DarkYellow'],
        \ ['darkgreen',   'SlateBlue'],
        \ ['darkcyan',    'Orange'],
        \ ['darkred',     'Brown'],
        \ ['green',       'Green'],
        \ ['cyan',        'Yellow'],
        \ ['yellow',      'DarkOrchid3'],
        \ ['brown',       'SeaGreen3'],
        \ ['red',         'firebrick3'],
        \ ]
    let g:rbpt_max = 16
    let g:rbpt_loadcmd_toggle = 0

    augroup my_rainbow
      autocmd!
      autocmd VimEnter * RainbowParenthesesToggle
      autocmd Syntax * RainbowParenthesesLoadRound
      autocmd Syntax * RainbowParenthesesLoadSquare
      autocmd Syntax * RainbowParenthesesLoadBraces
    augroup END
  " }}}

  "-----------------------------------------------------------
  " Powerline
  " {{{
  " Powerline and neocomplcache require Vim 7.2
    if pathogen#is_disabled('vim-powerline') == 0
      if os == "windows"
        ""let g:Powerline_symbols = 'compatible'
        let g:Powerline_symbols = 'unicode'
      elseif has('gui_macvim')
        let g:Powerline_symbols = 'fancy'
      else
        let g:Powerline_symbols = 'unicode'
      endif

      let g:Powerline_cache_enabled = 1
      " override the dividers
      let g:Powerline_dividers_override = ['>>', '>', '<<', '<']
      let g:Powerline_stl_path_style = 'short'
      " let Powerline_theme = 'skwp'
      " let Powerline_colorscheme = 'skwp'
      " Insert the charcode segment after the filetype segment
      " call Pl#Theme#InsertSegment('ws_marker', 'after', 'lineinfo')
      " Replace the scrollpercent segment with the charcode segment
      " call Pl#Theme#ReplaceSegment('scrollpercent', 'fileinfo')
    endif
  " }}}

  "-----------------------------------------------------------
  " Syntastic
  " {{{
    let g:loaded_syntastic_plugin = 1
    if pathogen#is_disabled('syntastic') == 0
      let g:syntastic_auto_loc_list = 0 " auto open error window
      let g:syntastic_check_on_wq = 0   " skip syntax check when saving file
      let g:syntastic_auto_jump = 0     " auto jump to the first issue detected
      let g:syntastic_loc_list_height = 5 " height of the location lists
      " Check C/C++
      let g:syntastic_cpp_check_header = 1 " check header file
      let g:syntastic_cpp_auto_refresh_includes = 1 " enable header files being re-checked in every filw write
    endif
  " }}}

  " ------------------------------------------------------------
  " Draw It
  " {{{
    let g:DrChipTopLvlMenu = 'Plugin.' " remove 'DrChip' menu
  " }}}

  "-----------------------------------------------------------
  " neocomplcache
  if s:settings.autocomplete_method == 'neocomplcache' "{{{
    if pathogen#is_disabled('neocomplcache') == 0
      if v:version > 702
        let g:acp_enableAtStartup = 0              " Disable AutoComplPop.
        let g:neocomplcache_enable_at_startup = 1  " Use neocomplcache
        let g:neocomplcache_enable_auto_select = 1
        let g:neocomplcache_enable_smart_case = 1  " Use smartcase
        let g:neocomplcache_min_syntax_length = 3 " Set minimum syntax keyword length.
        let g:neocomplcache_enable_quick_match = 1
        let g:neocomplcache_temporary_dir = g:dotvim_settings.cache_dir . '/neocomplcache'
        " Enable heavy features.
        " Use camel case completion.
        let g:neocomplcache_enable_camel_case_completion = 1 " Use camel case completion
        let g:neocomplcache_enable_underbar_completion = 1   " Use underbar completion

        let g:neocomplcache_max_list = 5
        let g:neocomplcache_enable_fuzzy_completion = 1
        let g:neocomplcache_fuzzy_completion_start_length = 3
        let g:neocomplcache_lock_buffer_name_pattern = '\*ku\*'

        let g:neocomplcache_source_disable = {
          \ 'syntax_complete': 1,
          \ }

        let g:neocomplcache_auto_completion_start_length = 2
        " Define keyword.
        if !exists('g:neocomplcache_keyword_patterns')
          let g:neocomplcache_keyword_patterns = {}
        endif
        let g:neocomplcache_keyword_patterns['default'] = '\h\w*'

        if !exists('g:neocomplcache_omni_patterns')
          let g:neocomplcache_omni_patterns = {}
        endif

        let g:neocomplcache_omni_patterns.ruby = '[^. *\t]\.\w*\|\h\w*::'
        let g:neocomplcache_omni_patterns.php = '[^. \t]->\h\w*\|\h\w*::'
        let g:neocomplcache_omni_patterns.c = '\%(\.\|->\)\h\w*'
        let g:neocomplcache_omni_patterns.cpp = '\h\w*\%(\.\|->\)\h\w*\|\h\w*::'

        " " Plugin key-mappings.
        " inoremap <C-k>     <Plug>(neocomplcache_snippets_expand)
        " snoremap <C-k>     <Plug>(neocomplcache_snippets_expand)
        " inoremap <expr><C-g>     neocomplcache#undo_completion()
        " inoremap <expr><C-l>     neocomplcache#complete_common_string()

        " Recommended key-mappings.
        " <CR>: close popup and save indent.
        " inoremap <silent> <CR> <C-r>=<SID>my_cr_function()<CR>
        " function! s:my_cr_function()
        "   return neocomplcache#smart_close_popup() . "\<CR>"
        "   " For no inserting <CR> key.
        "   "return pumvisible() ? neocomplcache#close_popup() : "\<CR>"
        " endfunction
        " <TAB>: completion.
        " inoremap <expr><TAB>  pumvisible() ? "\<C-n>" : "\<TAB>"
        " <C-h>, <BS>: close popup and delete backword char.
        inoremap <expr><C-h> neocomplcache#smart_close_popup()."\<C-h>"
        inoremap <expr><BS> neocomplcache#smart_close_popup()."\<C-h>"
        inoremap <expr><C-y>  neocomplcache#close_popup()
        inoremap <expr><C-e>  neocomplcache#cancel_popup()

        "
        " Close popup by <Space>.
        " inoremap <expr><Space> pumvisible() ? neocomplcache#close_popup() : "\<Space>"

        " Enable omni completion.
        augroup my_complete
          autocmd!
        autocmd FileType css setlocal omnifunc=csscomplete#CompleteCSS
        autocmd FileType html,markdown setlocal omnifunc=htmlcomplete#CompleteTags
        autocmd FileType javascript setlocal omnifunc=javascriptcomplete#CompleteJS
        autocmd FileType python setlocal omnifunc=pythoncomplete#Complete
        autocmd FileType xml setlocal omnifunc=xmlcomplete#CompleteTags
        augroup END

        " Enable heavy omni completion.
        if !exists('g:neocomplcache_omni_patterns')
          let g:neocomplcache_omni_patterns = {}
        endif
      endif
    endif
  endif " }}}

  "-----------------------------------------------------------
  " neocomplete
  if s:settings.autocomplete_method == 'neocomplete' "{{{
    if pathogen#is_disabled('neocomplete') == 0
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

      " Enable omni completion.
      autocmd FileType css setlocal omnifunc=csscomplete#CompleteCSS
      autocmd FileType html,markdown setlocal omnifunc=htmlcomplete#CompleteTags
      autocmd FileType javascript setlocal omnifunc=javascriptcomplete#CompleteJS
      autocmd FileType python setlocal omnifunc=pythoncomplete#Complete
      autocmd FileType xml setlocal omnifunc=xmlcomplete#CompleteTags

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
  endif "}}}

  "-----------------------------------------------------------
  " conque
  " {{{
    if pathogen#is_disabled('Conque-Shell') == 0
      autocmd FileType conque_term match none
      let g:ConqueTerm_StartMessages = 0

      command! Sh ConqueTermSplit bash --login
      command! Irb ConqueTermSplit irb
      command! Py ConqueTermSplit ipython
    endif
  " }}}

  "-----------------------------------------------------------
  " indent-guides
  " {{{
  " highlight indent with different color
    if pathogen#is_disabled('indent-guides') == 0
      let g:indent_guides_enable_on_vim_startup = 1   " enable when startup
      let g:indent_guides_auto_colors = 1       " automatically calculates the highlight colors
      let g:indent_guides_exclude_filetypes = ['help', 'nerdtree']
      let g:indent_guides_start_level=1
      let g:indent_guides_guide_size=1
      let g:indent_guides_color_change_percent=3
      " if !has('gui_running')
      "   let g:indent_guides_auto_colors=0
      "   function! s:indent_set_console_colors()
      "     hi IndentGuidesOdd ctermbg=235
      "     hi IndentGuidesEven ctermbg=236
      "   endfunction
      "   autocmd VimEnter,Colorscheme * call s:indent_set_console_colors()
      " endif
    endif
  " }}}

  "-----------------------------------------------------------
  " fuzzy finder
  " {{{
  " FuzzyFinder/L9 require Vim 7.2 and floating-point support
    if pathogen#is_disabled('FuzzyFinder') == 0
      let g:fuf_dataDir=g:dotvim_settings.cache_dir.'/fuzzyfinder-data'
      ""call add(g:pathogen_blacklist, 'l9')
      ""call add(g:pathogen_blacklist, 'fuzzyfinder')
      nnoremap <Leader>ffb :FufBuffer<CR>
      nnoremap <Leader>fff :FufFileWithCurrentBufferDir<CR>
      nnoremap <Leader>ffj :FufJumpList<CR>
      nnoremap <Leader>ffl :FufLine<CR>
    endif
  " }}}

  "-----------------------------------------------------------
  " gundo
  " Gundo requires Vim 7.3 and Python
  " {{{
    if pathogen#is_disabled('gundo') == 0
      nnoremap <silent> <Leader>u :GundoToggle<CR>
    endif
  " }}}

  "-----------------------------------------------------------
  " ctrlp
  if s:settings.finder_method == 'ctrlp' "{{{
    if pathogen#is_disabled('ctrlp') == 0
      let g:ctrlp_map = '<Leader>p'
      let g:ctrlp_cmd = 'CtrlP'
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
      if os == "windows"  " Windows
        let g:ctrlp_user_command = 'dir %s /-n /b /s /a-d'
      elseif os == "linux"        " MacOSX/Linux
        if executable('ag')
          let g:ctrlp_user_command = 'ag %s -l --nocolor -g ""'
        else
          let g:ctrlp_user_command = 'find %s -type f'
        endif
      endif
      " let g:ctrlp_user_command = ['.git', 'cd %s && git ls-files']
      " let g:ctrlp_user_command = ['.git', 'cd %s && git ls-files . -co --exclude-standard', 'find %s -type f']
      " let g:ctrlp_user_command = ['.hg', 'hg --cwd %s locate -I .']
      ""let g:ctrlp_user_command = {
      ""        \ 'types': {
      ""            \ 1: ['.git', 'cd %s && git ls-files'],
      ""            \ 2: ['.hg', 'hg --cwd %s locate -I .'],
      ""            \ },
      ""        \ 'fallback': 'find %s -type f'
      ""        \ }
      " Open multiplely selected files in a tab by default
      let g:ctrlp_open_multi = '10t'
    endif
  endif
  " }}}


  "-----------------------------------------------------------
  " vim-cycle
  " {{{
    if pathogen#is_disabled('vim-cycle') == 0
      " let g:cycle_default_groups = [
      "       \   [['true', 'false']],
      "       \   [['yes', 'no']],
      "       \   [['on', 'off']],
      "       \   [['+', '-']],
      "       \   [['>', '<']],
      "       \   [['"', "'"]],
      "       \   [['==', '!=']],
      "       \   [['0', '1']],
      "       \   [['and', 'or']],
      "       \   [['in', 'out']],
      "       \   [['up', 'down']],
      "       \   [['min', 'max']],
      "       \   [['get', 'set']],
      "       \   [['add', 'remove']],
      "       \   [['to', 'from']],
      "       \   [['read', 'write']],
      "       \   [['save', 'load', 'restore']],
      "       \   [['next', 'previous', 'prev']],
      "       \   [['only', 'except']],
      "       \   [['without', 'with']],
      "       \   [['exclude', 'include']],
      "       \   [['width', 'height']],
      "       \   [['asc', 'desc']],
      "       \   [['是', '否']],
      "       \   [['上', '下']],
      "       \   [['男', '女']],
      "       \   [['Sunday', 'Monday', 'Tuesday', 'Wednesday', 'Thursday',
      "       \     'Friday', 'Saturday'], ['hard_case', {'name': 'Days'}]],
      "       \   [['{:}', '[:]', '(:)'], 'sub_pairs'],
      "       \   [['（:）', '「:」', '『:』'], 'sub_pairs']
      "       \ ]
      nnoremap <silent> <Leader>n <Plug>CycleNext
      vnoremap <silent> <Leader>n <Plug>CycleNext
    endif
  " }}}

  "-----------------------------------------------------------
  " Neosnippet
  " {{{
  if s:settings.snippet_method == 'neosnippet'
    if pathogen#is_disabled('neosnippet') == 0
      " Plugin key-mappings.
      inoremap <C-k>     <Plug>(neosnippet_expand_or_jump)
      snoremap <C-k>     <Plug>(neosnippet_expand_or_jump)
      xnoremap <C-k>     <Plug>(neosnippet_expand_target)

      "" " SuperTab like snippets behavior
      "" imap <expr><TAB> neosnippet#expandable() ? "\<Plug>(neosnippet_expand_or_jump)" : pumvisible() ? "\<C-n>" : "\<TAB>"
      "" smap <expr><TAB> neosnippet#expandable() ? "\<Plug>(neosnippet_expand_or_jump)" : "\<TAB>"
      inoremap <expr><TAB> neosnippet#expandable_or_jumpable() ?
        \ "\<Plug>(neosnippet_expand_or_jump)"
        \: pumvisible() ? "\<C-n>" : "\<TAB>"
      snoremap <expr><TAB> neosnippet#expandable_or_jumpable() ?
        \ "\<Plug>(neosnippet_expand_or_jump)"
        \: "\<TAB>"

      " For snippet_complete marker.
      if has('conceal')
        set conceallevel=2 concealcursor=i
      endif"

      " Enable snipMate compatibility feature.
      let g:neosnippet#enable_snipmate_compatibility = 0  " no
      " Installing default snippets is optional
      let g:neosnippet#disable_runtime_snippets = {
                                                    \   '_' : 1,
                                                    \ }
      " Tell Neosnippet about the other snippets
      " use a different collection of snippets other than the built-in ones
      let g:neosnippet#snippets_directory=[ g:vimfiles . '/bundle/vim-snippets/snippets',
                                          \ g:vimfiles . '/snippets',
                                          \ g:vimfiles . '/bundle/systemc/snippets']
      " associating certain filetypes with other snippet files.
      let g:neosnippet#scope_aliases = {}
      let g:neosnippet#scope_aliases['cpp'] = 'cpp,systemc'
    endif
  endif
  " }}}

  "-----------------------------------------------------------
  " snipMate
  if s:settings.snippet_method == 'snipmate' "{{{
    if pathogen#is_disabled('vim-snipmate') == 0
      let g:snipMate = get(g:, 'snipMate', {}) " Allow for vimrc re-sourcing
      let g:snipMate.scope_aliases = {}
      let g:snipMate.scope_aliases['systemverilog'] = 'verilog,systemverilog'
    endif
  endif "}}}

  "-----------------------------------------------------------
  " delimitMate
  " {{{
  " let loaded_delimitMate = 1
  " au FileType mail let b:loaded_delimitMate = 1
    let delimitMate_matchpairs = "(:),[:],{:},<:>"
    let delimitMate_quotes = "\" ' `"
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
  " Alignment

  " vim-easy-align
  " {{{
    if pathogen#is_disabled('vim-easy-align') == 0
      " Start interactive EasyAlign in visual mode (e.g. vipga)
      xmap ga <Plug>(EasyAlign)

      " Start interactive EasyAlign for a motion/text object (e.g. gaip)
      nmap ga <Plug>(EasyAlign)
    endif
  " }}}

  "-----------------------------------------------------------
  " Tabular
  " {{{
    if exists(":Tabularize")
      nnoremap <Leader>a& :Tabularize /&<CR>
      vnoremap <Leader>a& :Tabularize /&<CR>
      nnoremap <Leader>a= :Tabularize /=<CR>
      vnoremap <Leader>a= :Tabularize /=<CR>
      nnoremap <Leader>a: :Tabularize /:<CR>
      vnoremap <Leader>a: :Tabularize /:<CR>
      nnoremap <Leader>a:: :Tabularize /:\zs<CR>
      vnoremap <Leader>a:: :Tabularize /:\zs<CR>
      nnoremap <Leader>a,  :Tabularize /,<CR>
      vnoremap <Leader>a,  :Tabularize /,<CR>
      nnoremap <Leader>a,, :Tabularize /,\zs<CR>
      vnoremap <Leader>a,, :Tabularize /,\zs<CR>
      nnoremap <Leader>a<Bar> :Tabularize /<Bar><CR>
      vnoremap <Leader>a<Bar> :Tabularize /<Bar><CR>
    endif
  " }}}

  "-----------------------------------------------------------
  " unite
  if s:settings.finder_method == 'unite' "{{{
    if pathogen#is_disabled('unite') == 0
      " Use the fuzzy matcher for everything
      call unite#filters#matcher_default#use(['matcher_fuzzy'])
      " Use the rank sorter for everything
      call unite#filters#sorter_default#use(['sorter_rank'])
      " Set up some custom ignores
      call unite#custom_source('file_rec,file_rec/async,file_mru,file,buffer,grep',
                  \ 'ignore_pattern', join([
                  \ '\.git/',
                  \ 'git5/.*/review/',
                  \ 'google/obj/',
                  \], '\|'))
      " nnoremap [unite] <Nop>
      " xnoremap [unite] <Nop>
      " nmap <leader>f [unite]
      " xmap <leader>f [unite]

      nnoremap [unite]S :<C-U>Unite source<CR>
      nnoremap <silent> [unite]f :<C-U>UniteWithBufferDir -buffer-name=files -start-insert file<CR>
      nnoremap <silent> [unite]r :<C-U>Unite -buffer-name=mru -start-insert file_mru<CR>
      nnoremap <silent> [unite]/ :<C-U>Unite -buffer-name=search line<CR>
      nnoremap <silent> [unite]d :<C-U>Unite -buffer-name=mru_dir -start-insert directory_mru<CR>
      nnoremap <silent> [unite]t :<C-U>Unite -buffer-name=tabs -start-insert tab<CR>
      nnoremap <silent> [unite]p :<C-U>Unite -buffer-name=registers -start-insert register<CR>
      xnoremap <silent> [unite]p :<C-U>Unite -buffer-name=register register<CR>
      nnoremap <silent> [unite]b :<C-U>Unite -buffer-name=bookmarks bookmark<CR>
      nnoremap <silent> [unite]m :<C-U>Unite mark<CR>
      nnoremap <silent> [unite]h :<C-U>Unite -buffer-name=helps help<CR>
      nnoremap <silent> [unite]o :<C-U>Unite outline<CR>
      nnoremap <silent> [unite]q :<C-u>Unite qflist -no-quit<CR>
      nnoremap <silent> [unite]s :<C-u>Unite -start-insert session<CR>
      nnoremap <silent> [unite]g :<C-u>Unite tab<CR>
      " nnoremap <silent> [unite]G :<C-u>Unite grep -no-quit<CR>
      nnoremap <silent> [unite]j :<C-u>Unite jump<CR>
      nnoremap <silent> [unite]c :<C-u>Unite change<CR>
      nnoremap <silent> [unite]q :<C-u>Unite poslist<CR>
      nnoremap <space>y :Unite history/yank<cr>
      nnoremap <space>s :Unite -quick-match buffer<cr>

      if executable('ack-grep')
        let g:unite_source_grep_command = 'ack-grep'
        let g:unite_source_grep_default_opts = '-i --no-heading --no-color -a -H'
      elseif executable('ack')
        let g:unite_source_grep_command = 'ack'
        let g:unite_source_grep_default_opts = '-i --no-heading --no-color -a -H'
      elseif executable('ag')
        let g:unite_source_grep_command = 'ag'
        let g:unite_source_grep_default_opts =
              \ '-i --vimgrep --hidden --ignore ' .
              \ '''.hg'' --ignore ''.svn'' --ignore ''.git'' --ignore ''.bzr'''
      elseif executable('pt')
        let g:unite_source_grep_command = 'pt'
        let g:unite_source_grep_default_opts = '--nogroup --nocolor'
      elseif executable('ack')
        let g:unite_source_grep_command = 'ack'
        let g:unite_source_grep_default_opts = '-i --no-heading --no-color -k -H'
      endif
      let g:unite_source_grep_recursive_opt = ''
      let g:unite_source_grep_encoding = 'utf-8'

      let g:unite_update_time = 70
      let g:unite_enable_split_vertically = 0   " split horizontally
      let g:unite_enable_ignore_case = 1
      let g:unite_enable_smart_case = 1
      let g:unite_enable_start_insert = 1   " start in INSERT mode
      let g:unite_enable_use_short_source_names = 1
      let g:unite_source_history_yank_enable = 1  " search through yank history
      let g:unite_winheight = 10
      let g:unite_data_directory = expand(g:dotvim_settings.cache_dir.'/unite')
      let g:unite_cursor_line_highlight = 'TabLineSel'
      " let g:unite_source_file_mru_time_format = "(%m/%d %T) "
      let g:unite_source_file_mru_filename_format = ':~:.'
      let g:unite_source_file_mru_limit = 300
      " let g:unite_source_directory_mru_time_format = ''
      let g:unite_source_directory_mru_limit = 300
      let g:unite_split_rule = "botright"   " Open in bottom right
      let g:unite_source_rec_max_cache_files = 99999

      function! s:unite_settings()
        nnoremap <buffer> <C-J> <Plug>(unite_loop_cursor_down)
        nnoremap <buffer> <C-K> <Plug>(unite_loop_cursor_up)
        nnoremap <buffer> m <Plug>(unite_toggle_mark_current_candidate)
        nnoremap <buffer> M <Plug>(unite_toggle_mark_all_candidate)
        nnoremap <buffer> <LocalLeader><F5> <Plug>(unite_redraw)
        nnoremap <buffer> <LocalLeader>q <Plug>(unite_exit)

        vnoremap <buffer> m <Plug>(unite_toggle_mark_selected_candidates)

        inoremap <buffer> <C-J> <Plug>(unite_select_next_line)
        inoremap <buffer> <C-K> <Plug>(unite_select_previous_line)
        inoremap <buffer> <LocalLeader><BS> <Plug>(unite_delete_backward_path)
        inoremap <buffer> <LocalLeader>q <Plug>(unite_exit)
      endfunction
    endif
  endif
  " }}}

  "-----------------------------------------------------------
  " fugitive - Git integration!
  " Probably the best or second best plugin of them all.
  " {{{
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
    " Remove trailing whitespace
    " Mnemonic: delete whitespace
    nnoremap <leader>dws :silent! %s/\s\+$//ge<enter>
    vnoremap <leader>dws :s/\s\+$//ge<enter>
    " Ignore whitespace in diffs.
    " Also shows current diffopt status.
    nnoremap <leader>s :set diffopt+=iwhite<enter>:set diffopt<enter>
    nnoremap <leader>S :set diffopt-=iwhite<enter>:set diffopt<enter>
  " }}}


  "-----------------------------------------------------------
  " NerdCommenter
  "{{{
    let g:NERDSpaceDelims = 1   " add extra space
    " Enable trimming of trailing whitespace when uncommenting
    let g:NERDTrimTrailingWhitespace = 1
  "}}}

  "-----------------------------------------------------------
  " Molokai
  " if pathogen#is_disabled('molokai') == 0
  "   colorscheme molokai
  " endif

  "-----------------------------------------------------------
  " AuthorInfo
  "{{{
    let g:vimrc_author='Hong Jin'
    let g:vimrc_email='hongjin@fiberhome.com'
  "}}}

  "-----------------------------------------------------------
  " Grep
  "{{{
    if os == "windows"
      let g:Grep_Path = './vimfiles/gnu/grep.exe'
      let g:Fgrep_Path  = './vimfiles/gnu/fgrep.exe'
      let g:Egrep_Path  = './vimfiles/gnu/egrep.exe'
      let g:Grep_Find_Path = './vimfiles/gnu/find.exe'
      let g:Grep_Xargs_Path = './vimfiles/gnu/xargs.exe'
    endif
    let Grep_Default_Options = '-i'
    let Grep_Skip_Dirs = 'RCS CVS .svn .git'
  "}}}


  "-----------------------------------------------------------
  " airline
  if s:settings.statusline_method == 'airline' "{{{
    if pathogen#is_disabled('airline') == 0
      " let g:loaded_airline = 1
      " enable fugitive integration >
      let g:airline_powerline_fonts = 1
      " let g:airline_extensions = ['branch', 'quickfix']
      let g:airline_section_c = airline#section#create_left(['%{getcwd()}', 'file'])
      let g:airline#extensions#branch#enabled = 0
      let g:airline_inactive_collapse=1
      " enable syntastic integration >
      let g:airline#extensions#syntastic#enabled = 0
      " enable/disable tagbar integration >
      let g:airline#extensions#tagbar#enabled = 0
      " change how tags are displayed (:help tagbar-statusline) >
      let g:airline#extensions#tagbar#flags = ''  "default
      let g:airline#extensions#tagbar#flags = 'f'
      let g:airline#extensions#tagbar#flags = 's'
      let g:airline#extensions#tagbar#flags = 'p'
      " bufferline
      let g:airline#extensions#bufferline#enabled = 0
      " enable/disable detection of whitespace errors. >
      let g:airline#extensions#whitespace#enabled = 0
      " configure which whitespace checks to enable. >
      let g:airline#extensions#whitespace#checks = [ 'indent', 'trailing' ]
      " anzu-mode
      let g:airline#extensions#anzu#enabled = 0
    endif
  endif
  "}}}

  "-----------------------------------------------------------
  " lightline
  if s:settings.statusline_method == 'lightline' "{{{
    if pathogen#is_disabled('lightline') == 0
      let g:lightline = {
          \ 'colorscheme': 'solarized_dark',
          \ }
    endif
  endif
  " }}}

  "-----------------------------------------------------------
  " easymotion
  " triggered with `<Leader><Leader>`
  " `<Leader><Leader>w` to find the beginning of a word
  " `<Leader><Leader>f` to find the character
  " `<Leader><Leader>b  to Beginning of word backward
  " `<Leader><Leader>e  to End of word forward
  " `<Leader><Leader>j  to Line downward
  " `<Leader><Leader>k  to Line upward
  "{{{
    if pathogen#is_disabled('easymotion') == 0
      " change the target keys
      " let g:EasyMotion_keys = '1234567890'
      " disable shading : 0
      let g:EasyMotion_do_shade = 1
      hi link EasyMotionTarget ErrorMsg
      hi link EasyMotionShade Comment
    endif
  "}}}

  "-----------------------------------------------------------
  " Verilog
  " verilog root menu
  "{{{
    let g:PluginTopLvlMenu = 'Plugin'
  "}}}

  "-----------------------------------------------------------
  "  Color Scheme Explorer
  "{{{
    let g:scroll_colors = 1
    let loaded_csExplorer = 1
  "}}}

  "-----------------------------------------------------------
  " uvm_gen
  "{{{
    let g:uvm_author    = "Hong Jin"
    let g:uvm_email     = "hongjin@fiberhome.com"
    let g:uvm_company   = "Copyright (c) " . strftime ("%Y") . ", Fiberhome Telecommunication Technology Co., Ltd."
    let g:uvm_department = "Microelectronics Dept. Logic Development Group."
  "}}}

  "-----------------------------------------------------------
  " multi_cursor
  "{{{
    let g:multi_cursor_use_default_mapping=1
  "}}}

  "-----------------------------------------------------------
  " CamelCaseMotion
  "{{{
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
  " anzu
  " display the current match index number and total match number of search pattern
  "{{{
  " mapping
    nmap n <Plug>(anzu-n-with-echo)
    nmap N <Plug>(anzu-N-with-echo)
    " nmap * <Plug>(anzu-star-with-echo)
    " nmap # <Plug>(anzu-sharp-with-echo)

    " clear status
    " nmap <Esc><Esc> <Plug>(anzu-clear-search-status)
  "}}}

  "-----------------------------------------------------------
  " c-support
  " C/C++ IDE
  "{{{
    let g:C_GlobalTemplateFile = g:vimfiles . '/bundle/c/c-support/templates/Templates'
    let g:C_LocalTemplateFile  = g:vimfiles . '/c-support/templates/Templates'
    let g:C_Root = '&Plugin.&C\/C\+\+.'
    let g:C_FormatDate         = '%Y-%m-%d'
    let g:C_FormatTime         = '%H:%M:%S'
  "}}}

  "-----------------------------------------------------------
  " expand-region
  "{{{
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
  "}}}

  "-----------------------------------------------------------
  " wildfire
  "{{{
    " This selects the next closest text object.
    let g:wildfire_fuel_map = "<ENTER>"

    " This selects the previous closest text object.
    let g:wildfire_water_map = "<BS>"

    let g:wildfire_objects = ["i'", 'i"', "i)", "i]", "i}", "ip", "it"]

    " use '*' to mean 'all other filetypes'
    " in this example, html and xml share the same text objects
    let g:wildfire_objects = {
        \ "*" : ["i'", 'i"', "i)", "i]", "i}", "ip"],
        \ "html,xml" : ["at"],
    \ }
  "}}}
endif

"}}} Plugin_config -----------------------------------------


"-----------------------------------------------------------
"""""""""""""""""""""" Extended """"""""""""""""""""""""""""
"-----------------------------------------------------------
"{{{
if g:load_vimrc_extended

  "-----------------------------------------------------------
  " Custom mappings
  " Key Mapping Setting
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

  " map <F6> :tabprevious<CR>
  map <silent> <F6> <C-o><F6>
  " map <F7> :tabnext<CR>
  map <silent> <F7> <C-o><F7>

  map  <F6>           :tabprevious<CR>
  map  <F7>           :tabnext<CR>
  map  <leader>tn     :tabnew<CR>
  map  <leader>tc     :tabclose<CR>
  map  <leader>to     :tabonly<cr>
  imap  <F6>          <ESC>:tabprevious<CR>i
  imap  <F7>          <ESC>:tabnext<CR>i
  imap  ^T            <ESC>:tabnew<CR>i

  " Buffer - reverse everything ... :)
  map <F8> ggVGg?     " rot-13
  " map <F9> :!python.exe %
  map <F10> :execute "vimgrep /" . expand("<cword>") . "/j **" <Bar> cw<CR>
  " map <F11>
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

  inoremap <C-k>  <C-o>d$
  noremap <M-d>  <C-o>diW   " delete word
  noremap <M-y>  <C-o>yiW   " yank word

  " Buffer commands
  nnoremap <silent> <Leader>bd :bdelete<CR>

  " ,bn - next buffer
  nnoremap <silent> <leader>bn :bnext<CR>

  " ,bp - previous buffer
  nnoremap <silent> <leader>bp :bprevious<CR>


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

  " don't use exact searches for */#
  " "noremap * g*
  " "noremap # g#
  noremap <kMultiply> g*          " map * to g*
  " Smart word search."{{{
  " Search cursor word by word unit.
  " nnoremap <silent> *  :<C-u>call <SID>SetSearch('""yiw', 'word')<CR>
  " Search cursor word.
  nnoremap <silent> g* :<C-u>call <SID>SetSearch('""yiw')<CR>
  " Search from cursor to word end.
  " nnoremap <silent> #  :<C-u>call <SID>SetSearch('""ye')<CR>

  " Search selected text.
  xnoremap <silent> * :<C-u>call <SID>SetSearch('""vgvy')<CR>
  xnoremap <silent> # :<C-u>call <SID>SetSearch('""vgvy')<CR>

  " Visual mode pressing * or # searches for the current selection
  " Super useful! From an idea by Michael Naumann
  vnoremap <silent> * :call VisualSelection('f', '')<CR>
  vnoremap <silent> # :call VisualSelection('b', '')<CR>

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
  " noremap n nzz
  " noremap N Nzz
  " noremap * *zz
  " noremap # #zz
  nnoremap g* g*zz
  nnoremap g# g#zz

  " nnoremap ; :
  " Use Q for formatting the current paragraph (or selection)
  vnoremap Q gq
  nnoremap Q gqap

  " nnoremap <C-h> :<C-u>help<Space>

  " using Perl/Python-compatible regex syntax
  " Thanks to Steve Losh for this liberating tip
  " See http://stevelosh.com/blog/2010/09/coming-home-to-vim
  nnoremap / /\v
  vnoremap / /\v

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
  vnoremap <silent> * :call VisualSearch('f')<CR>
  vnoremap <silent> # :call VisualSearch('b')<CR>
  vnoremap <silent> gv :call VisualSearch('gv')<CR>

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

  augroup my_fileheader
    autocmd!
    autocmd BufNewFile *.spec call FHHeader()
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


set secure

" vim: fdm=marker ts=2 sts=2 sw=2

