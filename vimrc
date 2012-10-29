"*******************************************************************************
" Filename:          _vimrc
" Author:            Hong Jin - bestkindy@gmail.com
" Created:           2010-08-13 14:04:30
" Last Modified:     2012-10-29 14:19:48
" Revesion:          0.1
" ID:                $Id$
" Reference:         Vim docs
" Description:       Vim configuration file
"
" Revision History:
" Date          Auther      Revision        Description
" ------------------------------------------------------------------------------
" 2010.08.13    Hong Jin    0.1             1. Initial revision
" 2010.12.01    Hong Jin    0.2             1. Change coloscheme to randomly
" ------------------------------------------------------------------------------
"
"******************************************************************************/

"-------------------------------------------------------------------------------
" Get out of VI's compatible mode
" Use Vim settings, rather then Vi settings.
" This must be first, because it changes other options as a side effect.
"-------------------------------------------------------------------------------
set nocompatible                " not use vi keyboard mode

let g:vimrc_loaded = 1

"-----------------------------------------------------------
" Platform
"-----------------------------------------------------------
function! MySys()
    if has("win16") || has("win32") || has("win64") || has("win95")
    "   runtime mswin.vim
        return "windows"
    else
        return "linux"
    endif
endfunction

"-----------------------------------------------------------
""" pathogen.vim {{{
" auto load all plugins
"-----------------------------------------------------------
if MySys() == "windows"
    source $VIM/vimfiles/bundle/vim-pathogen/autoload/pathogen.vim
    call pathogen#infect()
elseif MySys() == "linux"
    " source ~/.vim/bundle/vim-pathogen/autoload/pathogen.vim
    runtime bundle/vim-pathogen/autoload/pathogen.vim
    call pathogen#infect('')
endif
let g:pathogen_disabled = []

" pathogen ����vba��ʽ�Ĳ��
"   :e name.vba
"   :!mkdir $VIM\vimfiles\bundle\name
"   :UseVimball $VIM\vimfiles\bundle\name
" }}}
if v:version < 702
    call add(g:pathogen_disabled, 'Zoomwin')
    call add(g:pathogen_disabled, 'Vimball')
    call add(g:pathogen_disabled, 'neocomplcache')
    call add(g:pathogen_disabled, 'cscope_win')
    call add(g:pathogen_disabled, 'syntastic')
    call add(g:pathogen_disabled, 'powerline')
endif

if v:version < '702' || !has('float')
    call add(g:pathogen_disabled, 'L9')
    call add(g:pathogen_disabled, 'FuzzyFinder')
endif

if v:version < 702
    let g:loaded_acp = 1
endif

if v:version < 700 || !has('patch167')
    call add(g:pathogen_disabled, 'tagbar')
endif

if v:version < 703 || !has('python')
    call add(g:pathogen_disabled, 'gundo')
endif

call pathogen#runtime_append_all_bundles()
call pathogen#helptags()

"-----------------------------------------------------------
" Encoding Setting
"-----------------------------------------------------------
if has("multi_byte")
    " Set fileencoding priority
    if getfsize(expand("%")) > 0
        set fileencodings=ucs-bom,utf-8,cp936,gb18030,big5,euc-jp,sjis,cp932,cp949,euc-kr,latin1
    else
        set fileencodings=cp936,cp932,cp949,big5,euc-jp,euc-kr,latin1
    endif
    " CJK environment detection and corresponding setting
    if v:lang =~ "^zh_CN"
    " Use cp936 to support GBK, euc-cn == gb2312
        set encoding=chinese
        set termencoding=chinese
        set fileencoding=chinese
    elseif v:lang =~ "^zh_TW"
        " cp950, big5 or euc-tw. Are they equal to each other?
        set encoding=taiwan
        set termencoding=taiwan
        set fileencoding=taiwan
    elseif v:lang =~ "^ko"
        " Copied from someone's dotfile, untested
        set encoding=euc-kr
        set termencoding=euc-kr
        set fileencoding=euc-kr
    elseif v:lang =~ "^ja_JP"
        " Copied from someone's dotfile, unteste
        set encoding=cp932                  " euc-jp
        set termencoding=cp932              " euc-jp
        set fileencoding=cp932              " euc-jp
    endif
    " Detect UTF-8 locale, and replace CJK setting if needed
    if v:lang =~ "utf8$" || v:lang =~ "UTF-8$"
        set encoding=utf-8
        set termencoding=utf-8
        set fileencoding=utf-8
    endif
else
    echoerr "Sorry, this version of (g)vim was not compiled with multi_byte"
endif

fun! ViewUTF8()
    set encoding=utf-8
    set termencoding=big5
endfun

fun! UTF8()
    set encoding=utf-8                                  
    set termencoding=big5
    set fileencoding=utf-8
    set fileencodings=ucs-bom,big5,utf-8,latin1
endfun

fun! Big5()
    set encoding=big5
    set fileencoding=big5
endfun

"set langmenu=zh_CN.UTF-8
set langmenu=none               " menu language
"language message zh_CN.UTF-8
lang mes en_US                   " message language
" lang messages zh_CN.UTF-8 " ���consle�������

set history=200                 " save cmd number in history
set viminfo='50,<1000,:50,n$VIM/viminfo     " save session

source $VIMRUNTIME/vimrc_example.vim
" source $VIMRUNTIME/mswin.vim      " Win behaviour
" behave mswin

" set helplang=cn                 " use Chinese help

"-----------------------------------------------------------
" Switch syntax highlighting on.
"-----------------------------------------------------------
syntax enable

filetype off

syntax on

"-----------------------------------------------------------
" FileType Detecting
" Enable file type detection. Use the default filetype settings.
" Also load indent files, to automatically do language-dependent indenting.
"-----------------------------------------------------------
filetype plugin on              " load filetype plugin
filetype indent on              " load indent

if exists("&autoread")
set autoread                    " autoload when file changed outside vim
endif
set autowrite                   " write a modified buffer on each :next , ...

set lazyredraw                  " Don't redraw while executing macros

" HighLight Character
highlight OverLength ctermbg=red ctermfg=white guibg=red guifg=white
":match OverLength '\%200v.*'

colorscheme peachpuff
" colorscheme darkblue

"-----------------------------------------------------------
" Backup
"-----------------------------------------------------------
"set directory=E:\bak
"set backupdir=E:\bak
set nobackup                    " no backup file
set nowritebackup               " no backup before rewrite file
set noswapfile

"-----------------------------------------------------------
" Mouse
"-----------------------------------------------------------
if MySys() == "windows"
    set mouse=a
elseif MySys() == "linux"
    set mouse=v
endif
set selection=inclusive         " defines the behavior of the selection
set selectmode=mouse            " when use mouse, launch SELECT mode
set keymodel=startsel           " Shift + arrow key
" set mousemodel=extend
set nomousehide
" set selectmode=key

"-----------------------------------------------------------
"Performance
"-----------------------------------------------------------
" Line Number
set number                      " display line number
set numberwidth=1

if MySys() == "windows"
    set path+=D:\cygwin\bin
elseif MySys() == "linux"
    set path+=/usr/bin
endif

set cmdheight=1                 " heighth of CMD line
set columns=100                 " max column number
" set title                       " display title
set shortmess=atI               " To avoid some hint messages
set report=0                    " Threshold for reporting number of lines changed
set noerrorbells                " No bell for error messages
" set fillchars=vert:\ ,stl:\ ,stlnc:\  " Characters to fill the statuslines and vertical separators
set fillchars=stl:-,stlnc:\ ,diff:-  " Characters to fill the statuslines and vertical separators
set novisualbell                " Use visual bell instead of beeping

"-----------------------------------------------------------
""" Line Feed
"-----------------------------------------------------------
set fileformats=unix,dos,mac
nmap <leader>fd :se ff=dos<cr>
nmap <leader>fu :se ff=unix<cr>

"-----------------------------------------------------------
""" Wrap Line
"-----------------------------------------------------------
set whichwrap+=<,>,[,]      " Allow wrap only when cursor keys are used
if has("gui_running")
    if has("gui_win32")     " Win OS
        set wrap            " Wrap line
"   elseif has("x11")
"   elseif has("gui_gtk2")
    endif
else
    set wrap
endif
set linebreak               " wrap at the right place
set showbreak=>
set iskeyword+=_,$,@,%,#,-  " Keywords for search and some commands, no wrap

"-----------------------------------------------------------
""" ClipBoard
"-----------------------------------------------------------
set clipboard+=unnamed

set list                        " list mode
"set listchars=tab:\|\ ,trail:.,extends:>,precedes:<,eol:$   "display TAB��EOL,etc
set listchars=tab:\|\ ,trail:.,extends:>,precedes:<

set autochdir          " Change the current working dir whenever open a file,
                       " switch buffers, delete a buffer, open/close a window

"-----------------------------------------------------------
""" Status Line
"-----------------------------------------------------------
if has('cmdline_info')
    set ruler                     " Show the line and column number of the cursor position
    " set rulerformat=%30(%2*%<%f%=\ %m%r\ %3l\ %c\ %p%%%) " determines the content of the ruler string
    set rulerformat=%30(%=\:b%n%y%m%r%w\ %l,%c%V\ %P%) " a ruler on steroids"
endif
" Color of Status Line
if has('statusline')
    "highlight StatusLine guifg=SlateBlue guibg=Yellow
    "highlight StatusLine guifg=SlateBlue guibg=#008800
    highlight StatusLine guifg=orange guibg=#008800 gui=underline
    highlight StatusLineNC guifg=Gray guibg=White
    set laststatus=2           " always show the status line
    hi User1 guifg=yellow
    hi User2 guifg=lightblue
    hi User3 guifg=red
    hi User4 guifg=cyan
    hi User5 guifg=lightgreen
    hi User6 gui=bold,inverse guifg=red term=bold,inverse cterm=bold,inverse ctermfg=red
    " set statusline=[Format=%{&ff}]\ [Type=%Y]\ [Pos=%l,%v][%p%%]\ %{strftime(\"%H:%M\")}
    " set statusline=[Format=%{&ff}]\ [Type=%Y]%1*%m%*%r%h%w%=[Pos=%l,%v][%l/%L(%p%%)]
    " set statusline=[%f][Format=%{&ff}]%{'['.(&fenc!=''?&fenc:&enc).']'}%y%1*%m%*%r%h%w%=[Pos=%l,%v][%l/%L(%p%%)]
    set statusline=
    set statusline+=[%f]                " file name
    set statusline+=[Format=%{&ff}]     " file format
    set statusline+=%{'['.(&fenc!=''?&fenc:&enc).']'}
    set statusline+=%y                  " file type
    set statusline+=%6*%m%*             " modified flag
    set statusline+=%r                  " readonly flag
    set statusline+=%h                  " 
    set statusline+=%w
    set statusline+=%=                  " left/right separator
    set statusline+=%b(0X%B)
    set statusline+=[Pos=%l,%c%V]
    set statusline+=[%l/%L(%p%%)]       " cursor position
endif
set showcmd                     " display incomplete commands

"-----------------------------------------------------------
"Replace/Search
"-----------------------------------------------------------
set hlsearch        " Highlight matched result when searching
set incsearch       " Show the pattern when typing a search command
set gdefault        " Replace all matched in a line, not just first one
set showmatch       " Highlight matched pairs
set matchtime=5     " Tenths of a second to show the matching paren
set ignorecase      " Ignore cases
set smartcase       " 
set nowrapscan      " Don't Searches wrap around the end of the file
set magic           " Changes the special characters that can be used in search patterns

"-----------------------------------------------------------
""" Folding Setting
"-----------------------------------------------------------
set nofoldenable            " disable folding
if exists("&foldlevel")
    set foldlevel=999           " make it really high, so they're not displayed by default
endif
set foldenable              " turn on folding
set foldmarker={,}
set foldmethod=indent       " Make folding indent sensitive  // syntax
set foldnestmax=5
set foldcolumn=2            " width for fold
set foldlevel=5             " Don't autofold anything (but I can still fold manually)
set foldlevelstart=1000     " fdls:  fold level start
set foldopen-=search        " don't open folds when you search into them
"set foldopen-=undo         " don't open folds when you undo stuff
""" Code folding options
nmap <leader>f0 :set foldlevel=0<CR>
nmap <leader>f1 :set foldlevel=1<CR>
nmap <leader>f2 :set foldlevel=2<CR>
nmap <leader>f3 :set foldlevel=3<CR>
nmap <leader>f4 :set foldlevel=4<CR>
nmap <leader>f5 :set foldlevel=5<CR>
nmap <leader>f6 :set foldlevel=6<CR>
nmap <leader>f7 :set foldlevel=7<CR>
nmap <leader>f8 :set foldlevel=8<CR>
nmap <leader>f9 :set foldlevel=9<CR>

"-----------------------------------------------------------
" File Format
"-----------------------------------------------------------
set backspace=2             " Influences the working of <BS>, <Del>, CTRL-W and CTRL-U in Insert mode
set backspace=indent,eol,start " same effect with above line
set formatoptions+=mM       " describes how automatic formatting is to be done
set tabstop=4               " TAB width
set softtabstop=4           " Soft TAB width
set shiftwidth=4            " Number of spaces to use for each step of (auto)indent, for cindent
set expandtab               " use SPACE instead of TAB
set smarttab                " use SPACE instead of TAB at start of line

"-----------------------------------------------------------
" Indent
"-----------------------------------------------------------
set autoindent              " Copy indent from current line when starting a new line
set smartindent             " Do smart autoindenting when starting a new line
set cindent                 " Enables automatic C program indenting

if v:version > '703'
    set cryptmethod=blowfish
endif

set splitbelow
set splitright

set virtualedit+=block

set display+=lastline

"-----------------------------------------------------------
" Diff
"-----------------------------------------------------------
set diffopt=context:3       " display 3 lines above and below the different place
" set scrollbind      " �����������Ļ������ͬ����
set diffopt+=iwhite
if MySys() == "windows"
    set diffexpr=MyDiff()
    function! MyDiff()
        let opt = '-a --binary '
        if &diffopt =~ 'icase' | let opt = opt . '-i ' | endif
        if &diffopt =~ 'iwhite' | let opt = opt . '-b ' | endif
        let arg1 = v:fname_in
        if arg1 =~ ' ' | let arg1 = '"' . arg1 . '"' | endif
        let arg2 = v:fname_new
        if arg2 =~ ' ' | let arg2 = '"' . arg2 . '"' | endif
        let arg3 = v:fname_out
        if arg3 =~ ' ' | let arg3 = '"' . arg3 . '"' | endif
        let eq = ''
        if $VIMRUNTIME =~ ' '
            if &sh =~ '\<cmd'
            let cmd = '""' . $VIMRUNTIME . '\diff"'
            let eq = '"'
        else
            let cmd = substitute($VIMRUNTIME, ' ', '" ', '') . '\diff"'
        endif
        else
            let cmd = $VIMRUNTIME . '\diff'
        endif
        silent execute '!' . cmd . ' ' . opt . arg1 . ' ' . arg2 . ' > ' . arg3 . eq
    endfunction
endif

" if $TERM == "xterm"
    set t_Co=256
    " colors simple256
    let g:solarized_termcolors=256      " use solarized 256 fallback
" endif

"-----------------------------------------------------------
" Session options
"-----------------------------------------------------------
set sessionoptions-=curdir
set sessionoptions+=sesdir

"-----------------------------------------------------------
" Auto Complete Word
"-----------------------------------------------------------
" options
set complete-=u
set complete-=i
set complete+=.,w,b,kspell,ss      " current buffer, other windows' buffers, dictionary, spelling
set completeopt=longest,menu    " Insert mode completetion
" set wildmode=longest:full,full
set wildmode=list:longest,full  " command <Tab> completion, list matches, then longest common part, then all"
set wildmenu                    " command-line completion operates in an enhanced mode
set wildignore+=.svn,CVS,.git,.hg,*.bak,*.o,*.e,*~,*.obj,*.swp,*.pyc,*.o,*.lo,*.la,*.exe,*.db,*.old,*.dat,*.,tmp,*.mdb,*~,~* " wildmenu: ignore these extensions
set wildignore+=*/tmp/*,*.so,*.swp,*.zip     " MacOSX/Linux"
set wildignore+=*\\tmp\\*,*.swp,*.zip,*.exe

"-----------------------------------------------------------
"Auto Complete Pairs
"-----------------------------------------------------------
"   :inoremap ( ()<ESC>i
"   :inoremap ) <c-r>=ClosePair(')')<CR>
"   :inoremap { {}<ESC>i
"   :inoremap } <c-r>=ClosePair('}')<CR>
"   :inoremap [ []<ESC>i
"   :inoremap ] <c-r>=ClosePair(']')<CR>
":inoremap < <><ESC>i
":inoremap > <c-r>=ClosePair('>')<CR>

function! ClosePair(char)
    if getline('.')[col('.') - 1] == a:char
        return "\<Right>"
    else
        return a:char
    endif
endf

"-----------------------------------------------------------------------------
" Custom mappings
"-----------------------------------------------------------------------------
"
" Key Mapping Setting
"
"        Normal  Visual  Select  Operator-pending    Insert  Command-line    Lang-Arg
" :map    yes    yes      yes        yes              -          -            -
" :nmap   yes    -         -         -                -          -            -
" :vmap    -     yes      yes        -                -          -            -
" :xmap    -     yes       -         -                -          -            -
" :smap    -      -       yes        -                -          -            -
" :omap    -      -        -         yes              -          -            -
" :map!    -      -        -         -               yes        yes           -
" :imap    -      -        -         -               yes         -            -
" :cmap    -      -        -         -                -         yes           -
" :lmap    -      -        -         -               yes*       yes*          yes*
"-----------------------------------------------------------
" set mapleader
let mapleader=","
let g:mapleader=","

" map <F1> :call ToggleSketch()<CR>
" map <F2> zr
" map <F3>
" map <F4> :call TitleDet()
" map <F4>    :q<CR>
" imap <F4>    <ESC>:q<CR>
imap <silent> <F4> <C-o><F4>
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
imap  <F6>          <ESC>:tabprevious<CR>i
imap  <F7>          <ESC>:tabnext<CR>i
imap  ^T            <ESC>:tabnew<CR>i

" Buffer - reverse everything ... :)
map <F8> ggVGg?     " rot-13
" map <F9> :!python.exe %
" map <F10>
" map <F11>
map     <F12>   a<C-R>=strftime(" @ %Y-%m-%d %H:%M")<CR>
imap    <F12>   <C-R>=strftime(" @ %Y-%m-%d %H:%M")<CR>
" insert time    strftime("%c")

" Fast saving
nmap <silent> <leader>wr :w<cr>
nmap <silent> <leader>wf :w!<cr>
nmap <silent> <leader>w :w!<cr>
" Fast quiting
nmap <silent> <leader>qw :wq<cr>
nmap <silent> <leader>qf :q!<cr>
nmap <silent> <leader>qq :q<cr>
nmap <silent> <leader>qa :qa<cr>
" Fast remove highlight search
nmap <silent> <leader><cr> :noh<cr>
" Fast redraw
nmap <silent> <leader>rr :redraw!<cr>

"Smart way to move btw. windows
" nmap <C-j> <C-W>j
nmap <C-k> <C-W>k
nmap <C-h> <C-W>h
nmap <C-l> <C-W>l

"Moving fast to front, back and 2 sides ;)
imap <m-$> <esc>$a
imap <m-0> <esc>0i

" auto load vimrc when editing it
if MySys() == "windows"
    nmap ,v :e $VIM/_vimrc<CR> " key mapping for editing vimrc
    autocmd! bufwritepost vimrc source $VIM/_vimrc
elseif MySys() == "linux"
    nmap ,v :e ~/.vimrc
    autocmd! bufwritepost vimrc source ~/.vimrc
endif

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

"Bash like
cnoremap <C-A>    <Home>
cnoremap <C-E>    <End>
cnoremap <C-K>    <C-U>

" set filetype to verilog
"map ,fv     :set ft=verilog<CR>
map ,fv     :set ft=verilog<CR>

" Fold
nmap <silent> <leader>zo zO
vmap <silent> <leader>zo zO

if version >= 600
  " Reduce folding
    map <F2> zr
    map <S-F2> zR
  " Increase folding
    map <F3> zm
    map <S-F3> zM
endif

"-----------------------------------------------------------
" Spell checking
"-----------------------------------------------------------
map <leader>sn ]s
map <leader>sp [s
map <leader>sa zg
map <leader>s? z=

" don't use exact searches for */#
" "noremap * g*
" "noremap # g#
map <kMultiply> g*          " map * to g*

" repeat command for each line in selection
vnoremap . :normal .<CR>

" shortcut for :diffupdate
nnoremap du :diffupdate<CR>

" map Ctrl+C to Escape
inoremap <C-c> <Esc>

" reselect visual block after indent
vnoremap > >gv
vnoremap < <gv

" autocomplete search history in command mode
cnoremap <C-n> <Up>
cnoremap <C-p> <Down>

" ,/, F2 - remove highlighted search
" "nnoremap <silent> ,/ :noh<CR>
nnoremap <silent> <F2> :noh<CR>

" ,1-9 - quick buffer switching
nnoremap <silent> ,1 :b1<CR>
nnoremap <silent> ,2 :b2<CR>
nnoremap <silent> ,3 :b3<CR>
nnoremap <silent> ,4 :b4<CR>
nnoremap <silent> ,5 :b5<CR>
nnoremap <silent> ,6 :b6<CR>
nnoremap <silent> ,7 :b7<CR>
nnoremap <silent> ,8 :b8<CR>
nnoremap <silent> ,9 :b9<CR>

" Allow insert mode editing like emacs
imap <C-a>  <Home>
imap <C-e>  <End>
imap <C-k>  <C-o>d$
imap <M-d>  <C-o>dw

" Buffer commands
nmap <silent> <Leader>bd :bd<CR>

" Edit the vimrc file
nmap <silent> <Leader>ev :e $MYVIMRC<CR>
nmap <silent> <Leader>sv :so $MYVIMRC<CR>
nmap <silent> <Leader>egv :e $MYGVIMRC<CR>
nmap <silent> <Leader>sgv :so $MYGVIMRC<CR>

" ,c - close current window
" nnoremap <silent> <leader>c :silent! close<CR>

" ,d - open definition in new window
nmap <silent> <leader>d <C-w>f

" ,n - next buffer
nnoremap <silent> <leader>n :bnext<CR>

" ,p - previous buffer
nnoremap <silent> <leader>p :bprevious<CR>

" ,s - split horizontally
nnoremap <silent> <leader>s :split<CR>

" ,v - split vertically
nnoremap <silent> <leader>v :vsplit<CR>

" ,w - write file
nnoremap <silent> <leader>w :write<CR>

" ,W - clear trailing whitespace
nnoremap <silent> <leader>W mw:%s/\s\s*$//e<CR>:nohlsearch<CR>`w:echohl Question<CR>:echo "Trailing whitespace cleared"<CR>:echohl none<CR>

"clearing highlighted search
nmap <silent> <leader>/ :nohlsearch<CR>

"-----------------------------------------------------------
" AutoCommands
"-----------------------------------------------------------
if has("autocmd") 
    autocmd FileType xml,html,c,cs,java,perl,shell,bash,cpp,python,vim,php,ruby,Verilog_SystemVerilog,sv set number
    autocmd FileType xml,html vmap <C-o> <ESC>'<i<!--<ESC>o<ESC>'>o-->
    autocmd FileType java,c,cpp,cs vmap <C-o> <ESC>'<o/*<ESC>'>o*/
    autocmd FileType html,text,php,vim,c,java,xml,bash,shell,perl,python,Verilog_SystemVerilog,sv,vimwiki set textwidth=80
    autocmd FileType lisp set ts=2
    au  FileType help set nonu
    autocmd FileType lisp set softtabstop=2
    autocmd BufReadPre,BufNewFile,BufRead *.vp setfiletype Verilog_SystemVerilog
"    autocmd BufNewFile,BufRead *.sv      setfiletype systemverilog
    autocmd BufReadPre,BufNewFile,BufRead *.do *.tree     setfiletype tcl
    autocmd BufReadPre,BufNewFile,BufRead *.log setfiletype txt
    autocmd BufRead,BufNewFile *.txt setfiletype txt " highlight TXT file
    autocmd BufReadPost * 
      \ if line("'\"") > 0 && line("'\"") <= line("$") |
      \   exe "normal g`\"" |
      \ endif
"    autocmd BufWritePost $MYVIMRC so $MYVIMRC
    autocmd BufEnter * :syntax sync fromstart
endif " has("autocmd")

"-----------------------------------------------------------
" Highlight current Line
"-----------------------------------------------------------
"highlight CurrentLine guibg=#4D4D4D         "848284     "guifg=white
"au! Cursorhold * exe 'match CurrentLine /\%' . line('.') . 'l.*/'
set ut=100

"-----------------------------------------------------------
" Abbreviations
"-----------------------------------------------------------
iab #c= ====================
iab #c# ####################
iab #c1 /****************************************************************
iab #c2 <Space>***************************************************************/


"-----------------------------------------------------------
" Visual mode
"-----------------------------------------------------------
function! CmdLine(str)
    exe "menu Foo.Bar :" . a:str
    emenu Foo.Bar
    unmenu Foo
endfunction

" From an idea by Michael Naumann
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
  else
    execute "normal /" . l:pattern . "^M"
  endif
  let @/ = l:pattern
  let @" = l:saved_reg
endfunction

"Basically you press * or # to search for the current selection !! Really useful
vnoremap <silent> * :call VisualSearch('f')<CR>
vnoremap <silent> # :call VisualSearch('b')<CR>


"-----------------------------------------------------------
""""  Setting for Programming
"-----------------------------------------------------------
"---------------
" Python
"---------------
" auto complete
autocmd FileType python set omnifunc=pythoncomplete#Complete
map <F9> :!python.exe
" Only do this part when compiled with support for autocommands.
" if has("autocmd")
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

  " python, not use <tab>
  "autocmd FileType python setlocal et | setlocal sta | setlocal sw=4
  " Python Unittest setting
  "autocmd FileType python compiler pyunit | setlocal makeprg=python\ %
  "autocmd FileType python setlocal makeprg=python\ ./alltests.py
  "autocmd BufNewFile,BufRead test*.py setlocal makeprg=python\ %
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

"-----------------------------------------------------------
"Java
"-----------------------------------------------------------

"-----------------------------------------------------------
" Verilog Automatic
"-----------------------------------------------------------
:inoremap       iav     <ESC>:Allpn<CR>
map             :iav        :Allpn<CR>
" :inoremap     av      <ESC>:Allcom<CR>
" map               :av     :Allcom<CR>
:inoremap       ihv             <ESC>:AddHeader<CR>
map             <leader>hv      :AddHeader<CR>
:inoremap       icv             <ESC>:Acontent<CR>
map             <leader>cv      :Acontent<CR>


"=====================================================================
" Plugin Setting
"=====================================================================
"-----------------------------------------------------------
"Tag List
"-----------------------------------------------------------
":TlistOpen����taglist���ڣ�           ":TlistClose���ر�taglist����
"����ʹ�á�:TlistToggle���ڴ򿪺͹رռ��л�       " ʹ��" tl"���Ϳ��Դ�/�ر�taglist����
"map <silent> <leader>tl :TlistToogle<cr>       " <CR>  ���������tag�������λ�ã������˫����tag����Ҳһ��
" o   ��һ���´򿪵Ĵ�������ʾ�����tag         " <Space> ��ʾ�����tag��ԭ�Ͷ���
" u  ����taglist�����е�tag                     " s  ��������ʽ���ڰ���������Ͱ�����˳��������л�
" x  taglist���ڷŴ����С������鿴�ϳ���tag
" +  ��һ���۵���ͬzo                 " -  ��tag�۵�������ͬzc
" *  �����е��۵���ͬzR               " =  ������tag�۵�������ͬzM
" [[  ����ǰһ���ļ�                    " ]]  ������һ���ļ�
" q   �ر�taglist����                   " <F1>  ��ʾ����
"""""""""""""""""""""""""""""""""""""""""""""""""""""""
if MySys() == "windows"
    let Tlist_Ctags_Cmd = './vimfiles/ctags58/ctags.exe'           "����ctags��·��
elseif MySys() == "linux"
    let Tlist_Ctags_Cmd = '/usr/bin/ctags'
endif
let Tlist_Use_Right_Window=1                " display at right side
let Tlist_File_Fold_Auto_Close=0            " only display current file, close other files tags
let Tlist_Sort_Type = "name"                " sort by name
let Tlist_Exit_OnlyWindow = 1             " exit if it's the last window
let Tlist_Auto_Open=0                     " not auto open
let Tlist_Compact_Format=1                " compress
let Tlist_Enable_Fold_Column=0            " Do not show folding tree
" let tlist_actionscript_settings = 'actionscript;c:class;f:method;p:property;v:variable'
" let Tlist_Show_Menu=1                     " show taglist menu
" let Tlist_Show_One_File=1           
" let Tlist_Auto_Update=1                   " auto update
" let Tlist_Process_File_Always             " ʼ�ս����ļ��е�tag
" let Tlist_WinWidth = 20                   " set width of the vertically split taglist window
" map to  :TlistOpen<CR>                    " ����ӳ�� to ��tag����
" map tc  :TlistClose<CR>                   " tc �ر�tag����
map tt  :TlistToggle<CR>
nmap <silent> <leader>tl :Tlist<cr>

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
"WinManager
"-----------------------------------------------------------
" let loaded_winmanager = 1
"nmap <silent> <leader>wm :WMToggle<cr>
let g:winManagerWindowLayout='NERDTree|BufExplorer'  
"let g:winManagerWindowLayout='FileExplorer|TagList' "what windows CTRL-N �л�
"let g:winManagerWindowLayout = 'FileExplorer|TagList'  
"let g:winManagerWindowLayout = 'FileExplorer'  
let g:winManagerWidth = 25               " How wide should it be( pixels)
let g:defaultExplorer = 0
nmap wm :WMToggle<cr>
nmap <C-W><C-F> :FirstExplorerWindow<cr>
nmap <C-W><C-B> :BottomExplorerWindow<cr>
autocmd BufWinEnter \[Buf\ List\] setl nonumber

"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
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

"-----------------------------------------------------------
"MiniBufExplorer
"-----------------------------------------------------------
let loaded_minibufexplorer = 0         " *** Disable minibuffer plugin
let g:miniBufExplMapCTabSwitchBufs = 1
let g:miniBufExplMapWindowNavVim = 1
let g:miniBufExplMapWindowNavArrows = 1
let g:miniBufExplModSelTarget = 1
let g:miniBufExplSplitBelow = 1
let g:miniBufExplMaxSize = 2
let g:miniBufExplUseSingleClick = 1    " select by single click
autocmd BufRead,BufNew :call UMiniBufExplorer

"-----------------------------------------------------------
"BufExplorer
"-----------------------------------------------------------
"       map ,be :BufExplorerHorizontalSplit<CR> " set hotkey for BufExplorer
"       let g:bufExplorerDefaultHelp=1          " Show default help.
"       let g:bufExplorerDetailedHelp=0         " Show detailed help
"       let g:bufExplorerShowRelativePath=1     " Show relative paths.
"       let g:bufExplorerSortBy='name'          " Sort by name.
"       let g:bufExplorerSplitBelow=0           " Split new window above current.
"       let g:bufExplorerShowDirectories=1      " Show directories

"-----------------------------------------------------------
"Matchit
"-----------------------------------------------------------
"let b:match_ignorecase=1

"-----------------------------------------------------------
" Netrw  File Explorer :e <PATH>
"-----------------------------------------------------------
":Explore    ��Ex���������ļ������           "<F1>        ��ʾ����
"<cr>        ��������ΪĿ¼��������Ŀ¼�������������ļ�������VIM�򿪸��ļ�
"-           �����ϼ�Ŀ¼               "c    �л�VIM�ĵ�ǰ����Ŀ¼Ϊ���������Ŀ¼
"d           ����Ŀ¼                   "D    ɾ���ļ���Ŀ¼
"i           �л���ʾ��ʽ               "R    �����ļ���Ŀ¼
"s           ѡ������ʽ               "x    ���������ʽ��ʹ����ָ���ĳ���򿪸��ļ�
"
if v:version < '702'
    let g:loaded_netrwPlugin = 1
else
    let g:netrw_winsize=25
    map fe :Texplore<CR>            " open in new tab
    map vfe :Vexplore<CR>           " vertical split
    nmap <silent> <leader>fe :Sexplore!<cr>
endif
"-----------------------------------------------------------
" NERD Tree  File Manager
"-----------------------------------------------------------
" o     open file                           " t     open file in new tab
" go    open file,but cursor in NERDtree    " T     same as t, but focus on the current tab
" tab   open file in a split window         " !     execute current file
" x     close the current nodes parent      " X     Recursively close all children of the current node
" e     open a netrw for the current dir
map ne :NERDTree<CR>
let NERDChristmasTree=1                     " more colorful
let NERDTreeWinPos="left"                   " put NERDTree at left
let NERDTreeWinSize=25                      " set size
let NERDTreeShowLineNumbers=0               " show line number
let NERDTreeIgnore=['\.pyc', '\~$', '\.swo$', '\.swp$', '\.git', '\.hg', '\.svn', '\.bzr']

"-----------------------------------------------------------
"Scope
"-----------------------------------------------------------
if has("cscope")
    if MySys() == "linux"
        set csprg=/usr/bin/cscope
    else
        set csprg=cscope
    endif
    set csto=1
    set cst
    set nocsverb
    " add any database in current directory
    if filereadable("cscope.out")
        cs add cscope.out
    " else add database pointed to by environment
    elseif $CSCOPE_DB != ""
    cs add $CSCOPE_DB
    endif
    set csverb
    set cscopetag
    set cscopequickfix=s-,g-,c-,d-,t-,e-,f-,i-
endif

"-----------------------------------------------------------
"Calendar
" :Calendar         "Open calendar   " :CalendarH        "��ˮƽ����������
"-----------------------------------------------------------
"let g:calendar_diary=<PATH>
let g:calendar_wruler = '�� һ �� �� �� �� ��'
let g:calendar_mark = 'left-fit'
let g:calendar_focus_today = 1
map ca :Calendar<CR>

"-----------------------------------------------------------
" lookupfile setting
"-----------------------------------------------------------
if v:version < '701'
    let g:loaded_lookupfile = 1
else
    let g:LookupFile_MinPatLength = 2
    let g:LookupFile_PreserveLastPattern = 0
    let g:LookupFile_PreservePatternHistory = 0
    let g:LookupFile_AlwaysAcceptFirst = 1
    let g:LookupFile_AllowNewFiles = 0
    if filereadable("./filenametags")
        let g:LookupFile_TagExpr = '"./filenametags"'
    endif
    map lf :LookupFile<cr>
    map lb :LUBufs<cr>
    map lw :LUWalk<cr>

    " lookup file with ignore case
    function! LookupFile_IgnoreCaseFunc(pattern)
        let _tags = &tags
        try
            let &tags = eval(g:LookupFile_TagExpr)
            let newpattern = '\c' . a:pattern
            let tags = taglist(newpattern)
        catch
            echohl ErrorMsg | echo "Exception: " . v:exception | echohl NONE
            return ""
        finally
            let &tags = _tags
        endtry

        " Show the matches for what is typed so far.
        let files = map(tags, 'v:val["filename"]')
        return files
    endfunction
    let g:LookupFile_LookupFunc = 'LookupFile_IgnoreCaseFunc'
endif
"-----------------------------------------------------------
" SVN Command
"-----------------------------------------------------------
" let SVNCommandSplit='vertical'
" let SVNCommandDiffSplit='vertical'
let SVNCommandEnableBufferSetup=1
let SVNCommandEdit='split'
let SVNCommandNameResultBuffers=1
" let SVNAutoCommitDiff='1'
let SVNCommandCommitOnWrite=1
let SVNCommandAutoSVK='svk'


"-----------------------------------------------------------
" showmarks setting
"-----------------------------------------------------------
" Enable ShowMarks
let showmarks_enable = 1
" Show which marks
let showmarks_include = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"
" Ignore help, quickfix, non-modifiable buffers
let showmarks_ignore_type = "hqm"
" Hilight lower & upper marks
let showmarks_hlline_lower = 1
let showmarks_hlline_upper = 1


"-----------------------------------------------------------
" mark setting
"-----------------------------------------------------------
nmap <silent> <leader>hl <Plug>MarkSet
vmap <silent> <leader>hl <Plug>MarkSet
nmap <silent> <leader>hh <Plug>MarkClear
vmap <silent> <leader>hh <Plug>MarkClear
nmap <silent> <leader>hr <Plug>MarkRegex
vmap <silent> <leader>hr <Plug>MarkRegex


"-----------------------------------------------------------
" Vimwiki
"-----------------------------------------------------------
let g:vimwiki_list = [{'path': 'E:/Workspace/Ref/vim/vim_wiki',
                     \ 'path_html': 'E:/Workspace/Ref/vim/vim_wiki/pub_html',
                     \ 'nested_syntaxes' : {'python': 'python', 'verilog': 'verilog'},
                     \ 'diary_rel_path': 'diary/'}]
let g:vimwiki_badsyms = ' '
let g:vimwiki_camel_case = 0

"-----------------------------------------------------------
" timestamp
"-----------------------------------------------------------
"let g:timestamp_regexp = '\v\C%(<Last %([cC]hanged?|[Mm]odified)\s*:\s+)@<=.*$|2010-08-13 09:49:39'
let g:timestamp_regexp = '\v\C%(<Last %([cC]hanged?|[Mm]odified|[Uu]pdated)\s*:\s+)@<=\d{4}-\d{2}-\d{2} \d{2}:\d{2}:\d{2}|2010-11-01 12:57:29'
let g:timestamp_rep = '%Y-%m-%d %H:%M:%S'
let g:timestamp_modelines = 20

"-----------------------------------------------------------
" Auto Change Date
"-----------------------------------------------------------
" autodate.vim: include "Last Changed: ."
"   let autodate_keyword_pre =
"   let autodate_keyword_pre  = '\$Date'            : default: '\cLast Changed:'
"   let autodate_keyword_post = '\$'                " default: '\.'
"   let autodate_format = ': %Y/%m/%d %H:%M:%S '
let plugin_autodate_disable = 1     " disable
let autodate_format = '%Y/%m/%d-%H:%M:%S '
""" Function: change last change time
function! LastMod()
  if line("$") > 5
    let l = 5
  else
    let l = line("$")
  endif
  exe "1," . l . "s/[Ll]ast [Mm]odified: .*/Last modified: " . strftime("%c") . " [" . hostname() . "]/e"
endfunction


"-----------------------------------------------------------
" yankring.vim
"-----------------------------------------------------------
let g:yankring_enabled=0
map <leader>yr :YRShow<cr>

"global search and replace in all buffers with one command
function AllBuffers(cmnd)
  let cmnd = a:cmnd
  let i = 1
  while (i <= bufnr("$"))
    if bufexists(i)
      execute "buffer" i
      execute cmnd
    endif
    let i = i+1
  endwhile
endfun


"-----------------------------------------------------------
" Auto commenting for "}"
" au BufNewFile,BufRead *.c,*.cc,*.C,*.h,*.v,*.py imap } <ESC>:call CurlyBracket()<CR>a

function CurlyBracket()
  let l:my_linenum = line(".")
  iunmap }
  sil exe "normal i}"
  imap } <ESC>:call CurlyBracket()<CR>
  let l:result1 =  searchpair('{', '', '}', 'bW')
  if (result1 > 0)
    let l:my_string = substitute(getline("."), '^\s*\(.*\){', '\1', "")
    sil exe ":" . l:my_linenum
    sil exe "normal a //" . l:my_string
  endif
endfunction

set isfname-==  " remove = from filename characters

"-----------------------------------------------------------
" Rainbow Parentheses
let g:rainbow_active = 1
let g:rainbow_load_separately = [
    \   [ '*' , [['(', ')'], ['\[', '\]'], ['{', '}']] ],
    \   [ '*.tex' , [['(', ')'], ['\[', '\]']] ],
    \   [ '*.cpp' , [['(', ')'], ['\[', '\]'], ['{', '}']] ],
    \   [ '*.{html,htm}' , [['(', ')'], ['\[', '\]'], ['{', '}'], ['<\a[^>]*>', '</[^>]*>']] ],
    \   ]
let g:rainbow_guifgs = ['RoyalBlue3', 'SeaGreen3', 'DarkOrange3', 'FireBrick',]

" function s:rainbow_parenthsis_load()
""if exists("g:btm_rainbow_color") && g:btm_rainbow_color
""    call rainbow_parenthsis#LoadSquare ()
""    call rainbow_parenthsis#LoadRound ()
""    call rainbow_parenthsis#Activate ()
""endif
" endfunction

" au Syntax python call s:rainbow_parenthsis_load()
" "au Syntax verilog call s:rainbow_parenthsis_load()
" au Syntax Verilog_SystemVerilog call s:rainbow_parenthsis_load()
" au Syntax vim call s:rainbow_parenthsis_load()
" au Syntax sh call s:rainbow_parenthsis_load()
" au Syntax csh call s:rainbow_parenthsis_load()
" au Syntax conf call s:rainbow_parenthsis_load()
" au Syntax c call s:rainbow_parenthsis_load()

"""""""""""""""""""""""""""""""""""
"" Command Line mode
"""""""""""""""""""""""""""""""""""
" $q is super useful when browsing on the command line
cno $q <C-\>eDeleteTillSlash()<cr>

" Bash like keys for the command line
cnoremap <C-A>      <Home>
cnoremap <C-E>      <End>
cnoremap <C-K>      <C-U>

cnoremap <C-P> <Up>
cnoremap <C-N> <Down>


"""" vis
let g:loaded_vis = 1


"""" mrswin
" let g:mrswin = 1
"

"-----------------------------------------------------------
" _ Powerline {{{
" Powerline and neocomplcache require Vim 7.2
if index(g:pathogen_disabled, 'powerline') == -1
""if v:version > '702'
    if !has('gui_running')
        call add(g:pathogen_disabled, 'powerline')
    endif
    if has('win32') || has('win64')
      let g:Powerline_symbols = 'compatible'
    elseif has('gui_macvim')
      let g:Powerline_symbols = 'fancy'
    endif

    let g:Powerline_cache_enabled = 1
    " let Powerline_theme = 'skwp'
    " let Powerline_colorscheme = 'skwp'
    " Insert the charcode segment after the filetype segment
    call Pl#Theme#InsertSegment('ws_marker', 'after', 'lineinfo')
    " Replace the scrollpercent segment with the charcode segment
    call Pl#Theme#ReplaceSegment('scrollpercent', 'fileinfo')
endif
" }}}

"-----------------------------------------------------------
" Syntastic
"-----------------------------------------------------------
""if v:version > '702'
if index(g:pathogen_disabled, 'syntastic') == -1
    let g:syntastic_enable_signs=1
    let g:syntastic_auto_loc_list=1
endif

" ------------------------------------------------------------
"  Setting for Align
" ------------------------------------------------------------
let g:DrChipTopLvlMenu = '' " remove 'DrChip' menu

" ------------------------------------------------------------
"  Setting for headlighes
" ------------------------------------------------------------
let g:loaded_headlights = 1             " (Disable)
let g:headlights_use_plugin_menu = 0    " (Disabled)
let g:headlights_smart_menus = 1        " (Enabled)
let g:headlights_show_commands = 1      " (Enabled)
let g:headlights_show_mappings = 1      " (Enabled)
let g:headlights_show_abbreviations = 0 " (Disabled)
let g:headlights_show_functions = 0     " (Disabled)
let g:headlights_show_highlights = 0    " (Disabled)
let g:headlights_show_files = 0         " (Disabled)
let g:headlights_show_load_order = 0    " (Disabled)
let g:headlights_debug_mode = 0         " (Disabled)

" ------------------------------------------------------------
"  Setting for vim-support
" ------------------------------------------------------------
let g:Vim_GlobalTemplateDir = '$VIM/vimfiles/bundle/Vim-Support/vim-support/templates'
let g:Vim_GlobalTemplateFile = '$VIM/vimfiles/bundle/Vim-Support/vim-support/templates/Templates'
let g:Vim_MapLeader  = ','

" ------------------------------------------------------------
" tips of the day (totd)
" ------------------------------------------------------------
let g:loaded_totd = 1

"-----------------------------------------------------------
" tagbar
" {{{
if index(g:pathogen_disabled, 'tagbar') == -1
    if v:version > 700 && has('patch167')
      let g:tagbar_width = 31
      let g:tagbar_autofocus = 1
      let g:tagbar_sort = 0
      let g:tagbar_compact = 1
      let g:tagbar_expand = 1
      let g:tagbar_singleclick = 1
      let g:tagbar_usearrows = 1

      nnoremap <silent><leader>tt :TagbarToggle<CR>
    endif
endif
" }}}

"-----------------------------------------------------------
" neocomplcache
" {{{
if index(g:pathogen_disabled, 'neocomplcache') == -1
    if v:version > '702'
      let g:neocomplcache_enable_at_startup = 1
      let g:neocomplcache_enable_auto_select = 1
      let g:neocomplcache_enable_smart_case = 1
      let g:neocomplcache_enable_camel_case_completion = 1
      let g:neocomplcache_enable_underbar_completion = 1

      let g:neocomplcache_source_disable = {
        \ 'syntax_complete': 1,
      \ }

      let g:neocomplcache_auto_completion_start_length = 2

      if !exists('g:neocomplcache_omni_patterns')
        let g:neocomplcache_omni_patterns = {}
      endif

      let g:neocomplcache_omni_patterns.ruby = '[^. *\t]\.\w*\|\h\w*::'
      let g:neocomplcache_omni_patterns.php = '[^. \t]->\h\w*\|\h\w*::'
      let g:neocomplcache_omni_patterns.c = '\%(\.\|->\)\h\w*'
      let g:neocomplcache_omni_patterns.cpp = '\h\w*\%(\.\|->\)\h\w*\|\h\w*::'

      " Recommended key-mappings.
      " <CR>: cancel popup and save indent.
      " inoremap <expr><CR>  neocomplcache#cancel_popup() . "\<CR>"
      " " <C-h>, <BS>: close popup and delete backword char.
      " inoremap <expr><C-h> neocomplcache#smart_close_popup()."\<C-h>"
      " inoremap <expr><BS> neocomplcache#smart_close_popup()."\<C-h>"
      " inoremap <expr><C-y>  neocomplcache#close_popup()
      " inoremap <expr><C-e>  neocomplcache#cancel_popup()

      " use <Tab> to complete words, and also handle snippets
      function! TabWrapper(...)
        if a:0 == 0
          if pumvisible()
            " close the popup and expand snippets
            return "\<C-y>\<C-R>=TabWrapper(1)\<CR>"
          else
            echomsg "2"
            " popup is closed, use normal SnipMate behavior
            return TriggerSnippet()
          endif
        else
          echomsg "3"
          " expand snippets, but don't insert a <Tab>
          return substitute(TriggerSnippet(), '\t', '', '')
        endif
      endfunction
      autocmd VimEnter * inoremap <Tab> <C-R>=TabWrapper()<CR>
    endif
endif
" }}}

"-----------------------------------------------------------
" conque
" {{{
if index(g:pathogen_disabled, 'conque') == -1
  autocmd FileType conque_term match none
  let g:ConqueTerm_StartMessages = 0

  command! Sh ConqueTermSplit bash --login
  command! Irb ConqueTermSplit irb
  command! Py ConqueTermSplit ipython
endif
" }}}

"-----------------------------------------------------------
" indent guides
" {{{
let g:indent_guides_auto_colors = 0
autocmd VimEnter,BufRead,BufNewFile * highlight IndentGuidesOdd  ctermbg=235 guibg=#2a2a2a
autocmd VimEnter,BufRead,BufNewFile * highlight IndentGuidesEven ctermbg=236 guibg=#333333

nnoremap <silent> ,i :IndentGuidesToggle<CR>
" }}}

"-----------------------------------------------------------
" fuzzy finder
" {{{
" FuzzyFinder/L9 require Vim 7.2 and floating-point support
""if v:version > '702' && has('float')
if index(g:pathogen_disabled, 'FuzzyFinder') == -1
    ""call add(g:pathogen_disabled, 'l9')
    ""call add(g:pathogen_disabled, 'fuzzyfinder')
    nnoremap <silent> ,b :FufBuffer<CR>
    nnoremap <silent> ,f :FufFileWithCurrentBufferDir<CR>
    nnoremap <silent> ,j :FufJumpList<CR>
    nnoremap <silent> ,l :FufLine<CR>
endif
" }}}

"-----------------------------------------------------------
" gundo
" Gundo requires Vim 7.3 and Python
""if v:version > '703' && has('python')
if index(g:pathogen_disabled, 'gundo') == -1
    nnoremap <silent> ,u :GundoToggle<CR>
endif

"-----------------------------------------------------------
" ctrlp
if index(g:pathogen_disabled, 'ctrlp') == -1
    " let g:ctrlp_custom_ignore = '\v[\/]\.(git|hg|svn)$'
    let g:ctrlp_custom_ignore = {
        \ 'dir':  '\v[\/]\.(git|hg|svn)$',
        \ 'file': '\v\.(exe|so|dll)$'
        \ }
    let g:ctrlp_user_command = 'find %s -type f'        " MacOSX/Linux
    let g:ctrlp_user_command = 'dir %s /-n /b /s /a-d'  " Windows
    ""let g:ctrlp_user_command = {
    ""        \ 'types': {
    ""            \ 1: ['.git', 'cd %s && git ls-files'],
    ""            \ 2: ['.hg', 'hg --cwd %s locate -I .'],
    ""            \ },
    ""        \ 'fallback': 'find %s -type f'
    ""        \ }
endif

""if filereadable(expand("~/.vimrc.bundles.local"))
""    source ~/.vimrc.bundles.local
""endif