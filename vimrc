"*******************************************************************************
" Filename:          _vimrc
" Author:            Hong Jin - bestkindy@gmail.com
" Description:       Vim configuration file
"
" Revision History:
" Date          Auther      Revision        Description
" ------------------------------------------------------------------------------
" 2010.08.13    Hong Jin    0.1             1. Initial revision
" 2010.12.01    Hong Jin    0.2             1. Change coloscheme to randomly
" 2012.11.01    Hong Jin    0.3             1. Change structure
" ------------------------------------------------------------------------------
"
"******************************************************************************/

"-------------------------------------------------------------------------------
" Get out of VI's compatible mode
" Use Vim settings, rather then Vi settings.
" This must be first, because it changes other options as a side effect.
set nocompatible                " not use vi keyboard mode

let g:vimrc_loaded = 1
let g:vimrc_disable_setting = 1

" set mapleader
let mapleader=","
let g:mapleader=","
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
let s:is_windows = has('win32') || has('win64')

" Windows Compatible {
" On Windows, also use '.vim' instead of 'vimfiles'; this makes synchronization
" across (heterogeneous) systems easier.
if has('win32') || has('win64')
    set runtimepath=$HOME/.vim,$VIM/vimfiles,$VIMRUNTIME,$VIM/vimfiles/after,$HOME/.vim/after
endif
" }


"-----------------------------------------------------------
""" pathogen.vim {{{
" auto load all plugins
"-----------------------------------------------------------
let g:pathogen_not_loaded_plugin = 1
if MySys() == "windows"
    " set rtp+=$VIM/vimfiles/bundle
    source $VIM/vimfiles/bundle/vim-pathogen/autoload/pathogen.vim
    call pathogen#infect()
elseif MySys() == "linux"
    " set rtp+=~/.vim/bundle
    runtime bundle/vim-pathogen/autoload/pathogen.vim
    call pathogen#infect('')
endif
let g:pathogen_disabled = []

if v:version < 700 || !has('patch167')
    call add(g:pathogen_disabled, 'tagbar')
endif

if v:version < 701
    call add(g:pathogen_disabled, 'vim-alignta')
endif

if v:version < 702
    call add(g:pathogen_disabled, 'Zoomwin')
    call add(g:pathogen_disabled, 'Vimball')
    call add(g:pathogen_disabled, 'neocomplcache')
    call add(g:pathogen_disabled, 'cscope_win')
    call add(g:pathogen_disabled, 'syntastic')
    call add(g:pathogen_disabled, 'unite')
    call add(g:pathogen_disabled, 'ColorV')
    call add(g:pathogen_disabled, 'galaxy')
    call add(g:pathogen_disabled, 'neosnippet')
    call add(g:pathogen_disabled, 'AutoComplPop')
    call add(g:pathogen_disabled, 'netrw')
endif

if v:version < 702 || !has('gui_running')
    call add(g:pathogen_disabled, 'powerline')
endif

if v:version < 702 || !has('float')
    call add(g:pathogen_disabled, 'L9')
    call add(g:pathogen_disabled, 'FuzzyFinder')
endif

if v:version < 703 || !has('python')
    call add(g:pathogen_disabled, 'gundo')
endif

" Disable on purpose
if exists('g:pathogen_not_loaded_plugin')
endif

call pathogen#runtime_append_all_bundles()
call pathogen#helptags()

" pathogen 管理vba格式的插件
"   :e name.vba
"   :!mkdir $VIM\vimfiles\bundle\name
"   :UseVimball $VIM\vimfiles\bundle\name
" }}}


"-----------------------------------------------------------
" Encoding Setting
"-----------------------------------------------------------
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
        set encoding=utf-8
        set fileencoding=chinese
    elseif v:lang =~ "^zh_TW"
        set encoding=taiwan
        set fileencoding=taiwan
    elseif v:lang =~ "^ko"
        set encoding=euc-kr
        set fileencoding=euc-kr
    elseif v:lang =~ "^ja_JP"
        set encoding=cp932                  " euc-jp
        set fileencoding=cp932              " euc-jp
    elseif v:lang =~ "utf8$"  || v:lang =~ "UTF-8$" || v:lang =~ "^en_US"
        " Detect UTF-8 locale, and replace CJK setting if needed
        set encoding=utf-8
        set fileencoding=utf-8
    endif
    let &termencoding = &encoding
else
    echoerr "Sorry, this version of (g)vim was not compiled with multi_byte"
endif

if MySys() == "windows"
    language message en                   " message language
    " language message en_US                   " message language
    " language message zh_CN.UTF-8
    " lang messages zh_CN.UTF-8 " 解决consle输出乱码
elseif MySys() == "linux"
    language message C
endif
"set langmenu=zh_CN.UTF-8
set langmenu=none               " menu language

if MySys() == "windows"
    if exists('+shellslash')
        set shellslash      " Exchange path separator
    endif
endif

set history=200                 " save cmd number in history
set viminfo='50,<1000,:50,n$VIM/viminfo     " save session

source $VIMRUNTIME/vimrc_example.vim
if MySys() == "windows"
    " source $VIMRUNTIME/mswin.vim      " Win behaviour
endif

runtime! ftplugin/man.vim
runtime! macros/matchit.vim

set helplang& helplang=en                 " use Chinese help

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
filetype plugin indent on              " load filetype plugin
""filetype indent on              " load indent

" Solarized
set t_Co=256
let g:solarized_termtrans=1
let g:solarized_termcolors=256
let g:solarized_contrast="high"
let g:solarized_visibility="high"
colorscheme solarized

" Set augroup
augroup MyAutoCmd
  autocmd!
augroup END

if exists("&autoread")
    set autoread                    " autoload when file changed outside vim
endif
set autowrite                   " write a modified buffer on each :next

set lazyredraw                  " Don't redraw while executing macros

" HighLight Character
highlight OverLength ctermbg=red ctermfg=white guibg=red guifg=white
" highlight pop menu
highlight Pmenu ctermbg=8 guibg=#606060
highlight PmenuSel ctermbg=1 guifg=#dddd00 guibg=#1f82cd
highlight PmenuSbar ctermbg=0 guibg=#d6d6d6
highlight LineNr ctermbg=0
highlight FoldColumn ctermbg=0

":match OverLength '\%200v.*'

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
set nomousehide                 " Hide the mouse when typing text
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
" set columns=1000                " max column number
" set title                       " display title
set shortmess+=atoOIT           " To avoid some hint messages
set report=0                    " Threshold for reporting number of lines changed
set noerrorbells                " No bell for error messages
" set fillchars=vert:\ ,stl:\ ,stlnc:\  " Characters to fill the statuslines and vertical separators
set fillchars=stl:-,stlnc:\ ,diff:-,vert:\|  " Characters to fill the statuslines and vertical separators
set novisualbell                " Use visual bell instead of beeping
set browsedir=current           " which directory to use for the file browser
set viewoptions=folds,options,cursor,unix,slash " better unix / windows compatibility
" set virtualedit=onemore         " allow for cursor beyond last character
set virtualedit+=block          " Enable virtualedit in visual block mode

" Set keyword help.
set keywordprg=:help

" Check timestamp more for 'autoread'.
autocmd MyAutoCmd WinEnter * checktime

"-----------------------------------------------------------
""" Line Feed
"-----------------------------------------------------------
" Default fileformat
set fileformat=unix
" Automatic recognition of a new line cord
set fileformats=unix,dos,mac
nmap <leader>fd :se ff=dos<cr>
nmap <leader>fu :se ff=unix<cr>

"-----------------------------------------------------------
""" Wrap Line
"-----------------------------------------------------------
" set whichwrap+=<,>,[,]      " Allow wrap only when cursor keys are used
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
set breakat=\ \	;:,!?
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


set list                        " list mode
"set listchars=tab:>-,trail:.,extends:>,precedes:<,eol:$   "display TAB，EOL,etc
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
    set showcmd                     " display incomplete commands
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

"-----------------------------------------------------------
"Replace/Search
"-----------------------------------------------------------
set hlsearch        " Highlight matched result when searching
set incsearch       " Show the pattern when typing a search command
set gdefault        " Replace all matched in a line, not just first one
set showmatch       " Highlight matched pairs
set matchtime=5     " Tenths of a second to show the matching paren
set matchpairs+=<:>
set ignorecase      " Ignore cases
set smartcase       " 
set nowrapscan      " Don't Searches wrap around the end of the file
set magic           " Changes the special characters that can be used in search patterns
" Use grep.
set grepprg=grep\ -nH

"-----------------------------------------------------------
""" Folding Setting
"-----------------------------------------------------------
" set foldenable              " turn on folding
set nofoldenable            " disable folding
if exists("&foldlevel")
    set foldlevel=999           " make it really high, so they're not displayed by default
endif
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
set backspace=indent,start  " same effect with above line
set formatoptions+=mM       " describes how automatic formatting is to be done
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

if v:version > 703
    set cryptmethod=blowfish
endif

"-----------------------------------------------------------
" Windows
"-----------------------------------------------------------
set equalalways " Multiple windows, when created, are equal in size
set splitbelow
set splitright

set display+=lastline
" CursorHold time
set updatetime=1000

"-----------------------------------------------------------
" Diff
"-----------------------------------------------------------
set diffopt=context:3       " display 3 lines above and below the different place
" set scrollbind      " 左右两侧的屏幕滚动是同步的
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
set complete+=k                 " scan the files given with the 'dictionary' option
set completeopt=longest,menuone    " Insert mode completetion
" set wildmode=longest:full,full
set wildmode=list:longest,full  " command <Tab> completion, list matches, then longest common part, then all"
set wildmenu                    " command-line completion operates in an enhanced mode
set wildignore+=.svn,CVS,.git,.hg,*.bak,*.o,*.e,*~,*.obj,*.swp,*.pyc,*.o,*.lo,*.la,*.exe,*.db,*.old,*.dat,*.,tmp,*.mdb,*~,~* " wildmenu: ignore these extensions
set wildignore+=*/tmp/*,*.so,*.swp,*.zip     " MacOSX/Linux"
set wildignore+=*\\tmp\\*,*.swp,*.zip,*.exe
" Set popup menu max height.
set pumheight=20

set showtabline=2

" Adjust window size of preview and help.
set previewheight=10
set helpheight=12

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

if MySys() == "windows"
    nmap ,v :e $VIM/_vimrc<CR> " key mapping for editing vimrc
elseif MySys() == "linux"
    nmap ,v :e ~/.vimrc
endif

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
map ,fv     :set ft=verilog_systemverilog<CR>

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
:noremap <Leader>h :split^M^W^W<cr>

" ,v - split vertically
nnoremap <silent> <leader>v :vsplit<CR>

" ,w - write file
func! DeleteTrailingWS()
  exe "normal mz"
  %s/\s\+$//ge
  exe "normal `z"
endfunc
noremap <leader>w :call DeleteTrailingWS()<CR>
" nnoremap <silent> <leader>w :write<CR>

" ,W - clear trailing whitespace
nnoremap <silent> <leader>W mw:%s/\s\s*$//e<CR>:nohlsearch<CR>`w:echohl Question<CR>:echo "Trailing whitespace cleared"<CR>:echohl none<CR>

"clearing highlighted search
nmap <silent> <leader>\ :nohlsearch<CR>
nnoremap <ESC><ESC> :nohlsearch<CR>

inoremap <buffer> /*          /**/<Left><Left>
inoremap <buffer> /*<Space>   /*<Space><Space>*/<Left><Left><Left>
inoremap <buffer> /*<CR>      /*<CR>*/<Esc>O
inoremap <buffer> <Leader>/*  /*

map <Leader>p <C-^>     "Go back to previous file

" Easy escape."{{{
imap jj <Esc>
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
nnoremap <silent> gl  :<C-u>call SmartEnd("n")<CR>
xnoremap <silent> gh  <ESC>:<C-u>call SmartHome("v")<CR>
xnoremap <silent> gl  <ESC>:<C-u>call SmartEnd("v")<CR>
nnoremap <expr> gm    (virtcol('$')/2).'\|'
xnoremap <expr> gm    (virtcol('$')/2).'\|'
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

"-----------------------------------------------------------
" AutoCommands
"-----------------------------------------------------------
if has("autocmd") 
    autocmd FileType xml,html,c,cs,java,perl,shell,bash,cpp,python,vim,php,ruby,verilog_systemverilog,sv set number
    autocmd FileType xml,html vmap <C-o> <ESC>'<i<!--<ESC>o<ESC>'>o-->
    autocmd FileType java,c,cpp,cs vmap <C-o> <ESC>'<o/*<ESC>'>o*/
    autocmd FileType html,text,php,vim,c,java,xml,bash,shell,perl,python,verilog_systemverilog,sv,vimwiki set textwidth=80
    autocmd FileType lisp set ts=2
    autocmd FileType help set nonu
    autocmd FileType lisp set softtabstop=2
    autocmd BufReadPre,BufNewFile,BufRead *.vp setfiletype verilog_systemverilog
"    autocmd BufNewFile,BufRead *.sv      setfiletype systemverilog
    autocmd BufReadPre,BufNewFile,BufRead *.do,*.tree     setfiletype tcl
    autocmd BufReadPre,BufNewFile,BufRead *.log setfiletype txt
    autocmd BufRead,BufNewFile *.txt setfiletype txt " highlight TXT file
    autocmd BufReadPost * 
      \ if line("'\"") > 0 && line("'\"") <= line("$") |
      \   exe "normal g`\"" |
      \ endif
    autocmd BufEnter * :syntax sync fromstart
    autocmd BufEnter * :lchdir %:p:h
    " auto load vimrc when editing it
    if MySys() == "windows"
        autocmd! bufwritepost _vimrc source $VIM/_vimrc
    elseif MySys() == "linux"
        autocmd! BufWritePost .vimrc source %
    endif
endif " has("autocmd")

"-----------------------------------------------------------
" Highlight current Line
"-----------------------------------------------------------
"highlight CurrentLine guibg=#4D4D4D         "848284     "guifg=white
"au! Cursorhold * exe 'match CurrentLine /\%' . line('.') . 'l.*/'

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
inoremap        iav     <ESC>:Allpn<CR>
map             :iav        :Allpn<CR>
" :inoremap     av      <ESC>:Allcom<CR>
" map               :av     :Allcom<CR>
inoremap        ihv             <ESC>:AddHeader<CR>
map             <leader>hv      :AddHeader<CR>
inoremap        icv             <ESC>:Acontent<CR>
map             <leader>cv      :Acontent<CR>


"=====================================================================
" Plugin Setting
"=====================================================================
"-----------------------------------------------------------
"Tag List
"-----------------------------------------------------------
":TlistOpen”打开taglist窗口，           ":TlistClose”关闭taglist窗口
"或者使用“:TlistToggle”在打开和关闭间切换       " 使用" tl"键就可以打开/关闭taglist窗口
"map <silent> <leader>tl :TlistToogle<cr>       " <CR>  跳到光标下tag所定义的位置，用鼠标双击此tag功能也一样
" o   在一个新打开的窗口中显示光标下tag         " <Space> 显示光标下tag的原型定义
" u  更新taglist窗口中的tag                     " s  更改排序方式，在按名字排序和按出现顺序排序间切换
" x  taglist窗口放大和缩小，方便查看较长的tag
" +  打开一个折叠，同zo                 " -  将tag折叠起来，同zc
" *  打开所有的折叠，同zR               " =  将所有tag折叠起来，同zM
" [[  跳到前一个文件                    " ]]  跳到后一个文件
" q   关闭taglist窗口                   " <F1>  显示帮助
"""""""""""""""""""""""""""""""""""""""""""""""""""""""
if pathogen#is_disabled('taglist') == 0
    if MySys() == "windows"
        let Tlist_Ctags_Cmd = './vimfiles/ctags58/ctags.exe'           "设置ctags的路径
    elseif MySys() == "linux"
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
    " let tlist_actionscript_settings = 'actionscript;c:class;f:method;p:property;v:variable'
    " let Tlist_Show_Menu=1                     " show taglist menu
    " let Tlist_Show_One_File=1           
    " let Tlist_Auto_Update=1                   " auto update
    " let Tlist_Process_File_Always             " 始终解析文件中的tag
    " let Tlist_WinWidth = 20                   " set width of the vertically split taglist window
    " map to  :TlistOpen<CR>                    " 键盘映射 to 打开tag窗口
    " map tc  :TlistClose<CR>                   " tc 关闭tag窗口
    map tt  :TlistToggle<CR>
    nmap <silent> <leader>tl :Tlist<cr>
endif

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
if pathogen#is_disabled('winmanager') == 0
    " let loaded_winmanager = 1
    "nmap <silent> <leader>wm :WMToggle<cr>
    let g:winManagerWindowLayout='NERDTree|BufExplorer'  
    "let g:winManagerWindowLayout='FileExplorer|TagList' "what windows CTRL-N 切换
    "let g:winManagerWindowLayout = 'FileExplorer|TagList'  
    "let g:winManagerWindowLayout = 'FileExplorer'  
    let g:winManagerWidth = 25               " How wide should it be( pixels)
    let g:defaultExplorer = 0
    nmap wm :WMToggle<cr>
    nmap <C-W><C-F> :FirstExplorerWindow<cr>
    nmap <C-W><C-B> :BottomExplorerWindow<cr>
    autocmd BufWinEnter \[Buf\ List\] setl nonumber
endif

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
if pathogen#is_disabled('minibufexpl') == 0
    let loaded_minibufexplorer = 0         " *** Disable minibuffer plugin
    let g:miniBufExplMapCTabSwitchBufs = 1
    let g:miniBufExplMapWindowNavVim = 1
    let g:miniBufExplMapWindowNavArrows = 1
    let g:miniBufExplModSelTarget = 1
    let g:miniBufExplSplitBelow = 1
    let g:miniBufExplMaxSize = 2
    let g:miniBufExplUseSingleClick = 1    " select by single click
    autocmd BufRead,BufNew :call UMiniBufExplorer
endif

"-----------------------------------------------------------
"BufExplorer
"-----------------------------------------------------------
if pathogen#is_disabled('bufexplorer') == 0
    map ,be :BufExplorerHorizontalSplit<CR> " set hotkey for BufExplorer
    let g:bufExplorerDefaultHelp=1          " Show default help.
    let g:bufExplorerDetailedHelp=0         " Show detailed help
    let g:bufExplorerShowRelativePath=1     " Show relative paths.
    let g:bufExplorerSortBy='name'          " Sort by name.
    let g:bufExplorerSplitBelow=0           " Split new window above current.
    let g:bufExplorerShowDirectories=1      " Show directories
endif

"-----------------------------------------------------------
"Matchit
"-----------------------------------------------------------
"let b:match_ignorecase=1

"-----------------------------------------------------------
" Netrw  File Explorer :e <PATH>
"-----------------------------------------------------------
":Explore    等Ex命令来打开文件浏览器           "<F1>        显示帮助
"<cr>        如果光标下为目录，则进入该目录；如果光标下是文件，则用VIM打开该文件
"-           返回上级目录               "c    切换VIM的当前工作目录为正在浏览的目录
"d           创建目录                   "D    删除文件或目录
"i           切换显示方式               "R    改名文件或目录
"s           选择排序方式               "x    定制浏览方式，使用你指定的程序打开该文件
"
if pathogen#is_disabled('netrw') == 0
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
if pathogen#is_disabled('nerdtree') == 0
    map ne :NERDTree<CR>
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
endif

"-----------------------------------------------------------
" Cscope
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
        silent cscope add cscope.out
    elseif $CSCOPE_DB != ""
        silent cscope add $CSCOPE_DB
    endif
    set csverb
    set cscopetag
    set cscopequickfix=s-,g-,c-,d-,t-,e-,f-,i-
endif

"-----------------------------------------------------------
"Calendar
" :Calendar         "Open calendar   " :CalendarH        "打开水平的日历窗口
"-----------------------------------------------------------
"let g:calendar_diary=<PATH>
let g:calendar_wruler = '日 一 二 三 四 五 六'
let g:calendar_mark = 'left-fit'
let g:calendar_focus_today = 1
map ca :Calendar<CR>

"-----------------------------------------------------------
" lookupfile setting
"-----------------------------------------------------------
if v:version < 701
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
if pathogen#is_disabled('vcscommand') == 0
    " let SVNCommandSplit='vertical'
    " let SVNCommandDiffSplit='vertical'
    let SVNCommandEnableBufferSetup=1
    let SVNCommandEdit='split'
    let SVNCommandNameResultBuffers=1
    " let SVNAutoCommitDiff='1'
    let SVNCommandCommitOnWrite=1
    let SVNCommandAutoSVK='svk'
endif

"-----------------------------------------------------------
" showmarks setting
"-----------------------------------------------------------
if pathogen#is_disabled('ShowMarks') == 0
    " Enable ShowMarks
    let g:showmarks_enable = 1
    " Show which marks
    let g:showmarks_include = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"
    " Ignore help, quickfix, non-modifiable buffers
    let g:showmarks_ignore_type = "hqm"
    " Hilight lower & upper marks
    let g:showmarks_hlline_lower = 1
    let g:showmarks_hlline_upper = 1
    let g:showmarks_textlower = "\t"
    let g:showmarks_textupper = "\t"
    let g:showmarks_textother = "\t"
    let g:showmarks_no_mappings = 1
    nmap mt <Plug>ShowMarksToggle
endif


"-----------------------------------------------------------
" mark setting
"-----------------------------------------------------------
" {{{
nmap <silent> <leader>hl <Plug>MarkSet
vmap <silent> <leader>hl <Plug>MarkSet
nmap <silent> <leader>hh <Plug>MarkClear
vmap <silent> <leader>hh <Plug>MarkClear
nmap <silent> <leader>hr <Plug>MarkRegex
vmap <silent> <leader>hr <Plug>MarkRegex
" }}}


"-----------------------------------------------------------
" Vimwiki
" {{{
if pathogen#is_disabled('vimwiki') == 0
    let g:vimwiki_list = [{'path': 'E:/Workspace/Ref/vim/vim_wiki',
                         \ 'path_html': 'E:/Workspace/Ref/vim/vim_wiki/pub_html',
                         \ 'nested_syntaxes' : {'python': 'python', 'verilog': 'verilog'},
                         \ 'diary_rel_path': 'diary/'}]
    let g:vimwiki_badsyms = ' '
    let g:vimwiki_camel_case = 0
endif
" }}}

"-----------------------------------------------------------
" timestamp
" {{{
"let g:timestamp_regexp = '\v\C%(<Last %([cC]hanged?|[Mm]odified)\s*:\s+)@<=.*$|2010-08-13 09:49:39'
let g:timestamp_regexp = '\v\C%(<Last %([cC]hanged?|[Mm]odified|[Uu]pdated)\s*:\s+)@<=\d{4}-\d{2}-\d{2} \d{2}:\d{2}:\d{2}|2010-11-01 12:57:29'
let g:timestamp_rep = '%Y-%m-%d %H:%M:%S'
let g:timestamp_modelines = 20
" }}}

"-----------------------------------------------------------
" Auto Change Date
" {{{
" autodate.vim: include "Last Changed: ."
"   let autodate_keyword_pre =
"   let autodate_keyword_pre  = '\$Date'            : default: '\cLast Changed:'
"   let autodate_keyword_post = '\$'                " default: '\.'
"   let autodate_format = ': %Y/%m/%d %H:%M:%S '
let plugin_autodate_disable = 1     " disable
let autodate_format = '%Y/%m/%d-%H:%M:%S '
let autodate_keyword_pre = 'Last \%(Change\|Modified\):'
""" Function: change last change time
function! LastMod()
  if line("$") > 5
    let l = 5
  else
    let l = line("$")
  endif
  exe "1," . l . "s/[Ll]ast [Mm]odified: .*/Last modified: " . strftime("%c") . " [" . hostname() . "]/e"
endfunction
" }}}

"-----------------------------------------------------------
" yankring.vim
" {{{
"-----------------------------------------------------------
if pathogen#is_disabled('yankring') == 0
    let g:yankring_enabled=0
    map <leader>yr :YRShow<cr>
endif
" }}}

set isfname-==  " remove = from filename characters

"-----------------------------------------------------------
" Rainbow Parentheses
" {{{
if pathogen#is_disabled('Rainbow-Parentheses-Improved') == 0
    let g:rainbow_active = 1
    let g:rainbow_load_separately = [
        \   [ '*' , [['(', ')'], ['\[', '\]'], ['{', '}']] ],
        \   [ '*.tex' , [['(', ')'], ['\[', '\]']] ],
        \   [ '*.cpp' , [['(', ')'], ['\[', '\]'], ['{', '}']] ],
        \   [ '*.{html,htm}' , [['(', ')'], ['\[', '\]'], ['{', '}'], ['<\a[^>]*>', '</[^>]*>']] ],
        \   ]
    let g:rainbow_guifgs = ['RoyalBlue3', 'SeaGreen3', 'DarkOrange3', 'FireBrick',]
endif
" }}}

"""""""""""""""""""""""""""""""""""
"" Command Line mode
"""""""""""""""""""""""""""""""""""
" $q is super useful when browsing on the command line
cnoremap $q <C-\>eDeleteTillSlash()<cr>

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
" {{{
" Powerline and neocomplcache require Vim 7.2
if pathogen#is_disabled('powerline') == 0
    if has('win32') || has('win64')
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
if pathogen#is_disabled('syntastic') == 0
    let g:syntastic_enable_signs=1
    let g:syntastic_auto_loc_list=1
endif
" }}}

" ------------------------------------------------------------
"  Setting for Align
" ------------------------------------------------------------
" {{{
let g:DrChipTopLvlMenu = 'Plugin.' " remove 'DrChip' menu
" }}}

" ------------------------------------------------------------
"  Setting for headlighes
" {{{
if pathogen#is_disabled('headlights') == 0
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
endif
" }}}

" ------------------------------------------------------------
"  vim-support
" {{{
if pathogen#is_disabled('Vim-Support') == 0
    if MySys() == "windows"
        let g:plugin_dir = '$VIM/vimfiles/bundle/Vim-Support'
        let g:Vim_GlobalTemplateDir = '$VIM/vimfiles/bundle/Vim-Support/vim-support/templates'
        let g:Vim_GlobalTemplateFile = '$VIM/vimfiles/bundle/Vim-Support/vim-support/templates/Templates'
        let g:Vim_LocalTemplateDir  = '$VIM/vimfiles/vim-support/templates'
        let g:Vim_LocalTemplateFile = '$VIM/vimfiles/vim-support/templates/Templates'
    elseif MySys() == "linux"
        let g:Vim_GlobalTemplateDir = '~/.vim/bundle/Vim-Support/vim-support/templates'
        let g:Vim_GlobalTemplateFile = '~/.vim/bundle/Vim-Support/vim-support/templates/Templates'
        let g:Vim_LocalTemplateFile = '~/.vim/bundle/Vim-Support/vim-support/templates/Templates'
    endif
    let g:Vim_MapLeader  = ','
    let g:Vim_RootMenu = "&Plugin"
endif
" }}}

"-----------------------------------------------------------
" tagbar
" {{{
if pathogen#is_disabled('tagbar') == 0
    if v:version > 700 && has('patch167')
        if !executable('ctags')
            let g:loaded_tagbar = 1
        elseif
            let g:tagbar_width = 30
            let g:tagbar_autofocus = 1
            let g:tagbar_sort = 0
            let g:tagbar_compact = 1
            let g:tagbar_expand = 1
            let g:tagbar_singleclick = 1
            let g:tagbar_usearrows = 1
            nnoremap <silent><leader>tt :TagbarToggle<CR>
        endif
    endif
endif
" }}}

"-----------------------------------------------------------
" neocomplcache
" {{{
if pathogen#is_disabled('neocomplcache') == 0
    if v:version > 702
      let g:acp_enableAtStartup = 0              " Disable AutoComplPop.
      let g:neocomplcache_enable_at_startup = 1  " Use neocomplcache
      let g:neocomplcache_enable_auto_select = 1
      let g:neocomplcache_enable_smart_case = 1  " Use smartcase
      let g:neocomplcache_enable_camel_case_completion = 1 " Use camel case completion
      let g:neocomplcache_enable_underbar_completion = 1   " Use underbar completion
      " Set minimum syntax keyword length.
      let g:neocomplcache_min_syntax_length = 3
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

      " Plugin key-mappings.
      imap <C-k>     <Plug>(neocomplcache_snippets_expand)
      smap <C-k>     <Plug>(neocomplcache_snippets_expand)
      inoremap <expr><C-g>     neocomplcache#undo_completion()
      inoremap <expr><C-l>     neocomplcache#complete_common_string()

      " Recommended key-mappings.
      " <CR>: cancel popup and save indent.
      " inoremap <expr><CR>  neocomplcache#cancel_popup() . "\<CR>"
      " " <C-h>, <BS>: close popup and delete backword char.
      " inoremap <expr><C-h> neocomplcache#smart_close_popup()."\<C-h>"
      " inoremap <expr><BS> neocomplcache#smart_close_popup()."\<C-h>"
      " inoremap <expr><C-y>  neocomplcache#close_popup()
      " inoremap <expr><C-e>  neocomplcache#cancel_popup()

      " use <Tab> to complete words, and also handle snippets
    endif
endif
" }}}

"-----------------------------------------------------------
" conque
" {{{
if pathogen#is_disabled('conque') == 0
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
if pathogen#is_disabled('indent-guides') == 0
    let g:indent_guides_enable_on_vim_startup = 0
    let g:indent_guides_auto_colors = 0
    let g:indent_guides_guide_size = 1
    let g:indent_guides_indent_levels = 30
    autocmd VimEnter,BufRead,BufNewFile * highlight IndentGuidesOdd  ctermbg=235 guibg=#2a2a2a
    autocmd VimEnter,BufRead,BufNewFile * highlight IndentGuidesEven ctermbg=236 guibg=#333333

    nnoremap <silent> ,i :IndentGuidesToggle<CR>
endif
" }}}

"-----------------------------------------------------------
" fuzzy finder
" {{{
" FuzzyFinder/L9 require Vim 7.2 and floating-point support
if pathogen#is_disabled('FuzzyFinder') == 0
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
if index(g:pathogen_disabled, 'gundo') == -1
    nnoremap <silent> ,u :GundoToggle<CR>
endif

"-----------------------------------------------------------
" ctrlp
if pathogen#is_disabled('ctrlp') == 0
    " let g:ctrlp_custom_ignore = '\v[\/]\.(git|hg|svn)$'
    let g:ctrlp_map = '<Leader>p'
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

"-----------------------------------------------------------
" numbers
if pathogen#is_disabled('numbers') == 0
    ""nnoremap <leader>nt :NumbersToggle<CR>
    nnoremap <F10> :NumbersToggle<CR>
endif

"-----------------------------------------------------------
" vim-cycle
" {{{
""if index(g:pathogen_disabled, 'vim-cycle') == -1
if pathogen#is_disabled('vim-cycle') == 0
    let g:cycle_default_groups = [
          \   [['true', 'false']],
          \   [['yes', 'no']],
          \   [['on', 'off']],
          \   [['+', '-']],
          \   [['>', '<']],
          \   [['"', "'"]],
          \   [['==', '!=']],
          \   [['0', '1']],
          \   [['and', 'or']],
          \   [['in', 'out']],
          \   [['up', 'down']],
          \   [['min', 'max']],
          \   [['get', 'set']],
          \   [['add', 'remove']],
          \   [['to', 'from']],
          \   [['read', 'write']],
          \   [['save', 'load', 'restore']],
          \   [['next', 'previous', 'prev']],
          \   [['only', 'except']],
          \   [['without', 'with']],
          \   [['exclude', 'include']],
          \   [['width', 'height']],
          \   [['asc', 'desc']],
          \   [['是', '否']],
          \   [['上', '下']],
          \   [['男', '女']],
          \   [['Sunday', 'Monday', 'Tuesday', 'Wednesday', 'Thursday',
          \     'Friday', 'Saturday'], ['hard_case', {'name': 'Days'}]],
          \   [['{:}', '[:]', '(:)'], 'sub_pairs'],
          \   [['（:）', '「:」', '『:』'], 'sub_pairs'],
          \ ]
    nmap <silent> <Leader>n <Plug>CycleNext
    vmap <silent> <Leader>n <Plug>CycleNext
endif
" }}}

"-----------------------------------------------------------
" Neosnippet
" {{{
""if index(g:pathogen_disabled, 'Neosnippet') == -1
if pathogen#is_disabled('neosnippet') == 0
    " Plugin key-mappings.
    imap <C-k>     <Plug>(neosnippet_expand_or_jump)
    smap <C-k>     <Plug>(neosnippet_expand_or_jump)

    "" " SuperTab like snippets behavior
    "" imap <expr><TAB> neosnippet#expandable() ? "\<Plug>(neosnippet_expand_or_jump)" : pumvisible() ? "\<C-n>" : "\<TAB>"
    "" smap <expr><TAB> neosnippet#expandable() ? "\<Plug>(neosnippet_expand_or_jump)" : "\<TAB>"

    " For snippet_complete marker.
    if has('conceal')
          set conceallevel=2 concealcursor=i
    endif"

    " use a different collection of snippets other than the built-in ones
    if MySys() == "windows"
        let g:neosnippet#snippets_directory='$VIM/vimfiles/bundle/snipmate-snippets/snippets'
    elseif MySys() == "linux"
        let g:neosnippet#snippets_directory='~/.vim/bundle/snipmate-snippets/snippets'
    endif
endif
" }}}

"-----------------------------------------------------------
" vim-snippet
" {{{
if pathogen#is_disabled('vim-snipmate') == 0
    let g:snips_trigger_key='<c-space>'
endif
" }}}

"-----------------------------------------------------------
" Auto Pairs
" {{{
let g:AutoPairs = {'(':')', '[':']', '{':'}',"'":"'",'"':'"'}
" }}}

"-----------------------------------------------------------
" vimfiler
" {{{
if pathogen#is_disabled('vimfiler') == 0
    let g:vimfiler_as_default_explorer = 1
    let g:vimfiler_edit_action = 'tabopen'
    let g:vimfiler_enable_clipboard = 0
    let g:vimfiler_safe_mode_by_default = 0
    let g:vimfiler_time_format = '%y-%m-%d %H:%M'
endif
" }}}

"-----------------------------------------------------------
" alignta
" {{{
if pathogen#is_disabled('vim-alignta') == 0
    let g:alignta_default_arguments = '! \S\+'
    xnoremap <silent> <LocalLeader>= :Alignta! \S\+<CR>
    xnoremap <silent> <LocalLeader>A :Alignta! \S\+<CR>
endif
" }}}

"-----------------------------------------------------------
" unite
" {{{
if pathogen#is_disabled('unite') == 0
    nnoremap [unite] <Nop>
    xnoremap [unite] <Nop>
    nmap <Leader>f [unite]
    xmap <Leader>f [unite]

    nnoremap [unite]S :<C-U>Unite source<CR>
    nnoremap <silent> [unite]f :<C-U>UniteWithBufferDir -buffer-name=files -start-insert file<CR>
    nnoremap <silent> [unite]r :<C-U>Unite -buffer-name=mru -start-insert file_mru<CR>
    nnoremap <silent> [unite]/ :<C-U>Unite -buffer-name=search line<CR>

    nnoremap <silent> [unite]d :<C-U>Unite -buffer-name=mru_dir -start-insert directory_mru<CR>
    nnoremap <silent> [unite]t :<C-U>Unite -buffer-name=tabs -start-insert tab<CR>
    nnoremap <silent> [unite]p :<C-U>Unite -buffer-name=registers -start-insert register<CR>
    xnoremap <silent> [unite]p "_d:<C-U>Unite -buffer-name=register register<CR>
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

    let g:unite_update_time = 70
    let g:unite_enable_split_vertically = 1
    let g:unite_source_file_mru_time_format = "(%m/%d %T) "
    let g:unite_source_file_rec_max_depth = 5
    let g:unite_enable_ignore_case = 1
    let g:unite_enable_smart_case = 1
    let g:unite_enable_start_insert = 0
    let g:unite_enable_short_source_names = 1
    let g:unite_source_history_yank_enable = 1
    let g:unite_winheight = 20
    let g:unite_source_session_path = expand('~/.vim/session/')
    let g:unite_cursor_line_highlight = 'TabLineSel'
    let g:unite_source_file_mru_filename_format = ':~:.'
    let g:unite_source_file_mru_limit = 300
    " let g:unite_source_directory_mru_time_format = ''
    let g:unite_source_directory_mru_limit = 300

    function! s:unite_settings()
      nmap <buffer> <C-J> <Plug>(unite_loop_cursor_down)
      nmap <buffer> <C-K> <Plug>(unite_loop_cursor_up)
      nmap <buffer> m <Plug>(unite_toggle_mark_current_candidate)
      nmap <buffer> M <Plug>(unite_toggle_mark_all_candidate)
      nmap <buffer> <LocalLeader><F5> <Plug>(unite_redraw)
      nmap <buffer> <LocalLeader>q <Plug>(unite_exit)

      vmap <buffer> m <Plug>(unite_toggle_mark_selected_candidates)

      imap <buffer> <C-J> <Plug>(unite_select_next_line)
      imap <buffer> <C-K> <Plug>(unite_select_previous_line)
      imap <buffer> <LocalLeader><BS> <Plug>(unite_delete_backward_path)
      imap <buffer> <LocalLeader>q <Plug>(unite_exit)
    endfunction
endif
" }}}

" git.vim{{{
let g:git_no_default_mappings = 1
let g:git_use_vimproc = 1
let g:git_command_edit = 'rightbelow vnew'
nnoremap <silent> [Space]gd :<C-u>GitDiff --cached<CR>
nnoremap <silent> [Space]gD :<C-u>GitDiff<CR>
" nnoremap <silent> [Space]gs :<C-u>GitStatus<CR>
nnoremap <silent> [Space]gl :<C-u>GitLog<CR>
nnoremap <silent> [Space]gL :<C-u>GitLog -u \| head -10000<CR>
nnoremap <silent> [Space]ga :<C-u>GitAdd<CR>
nnoremap <silent> [Space]gA :<C-u>GitAdd <cfile><CR>
" nnoremap <silent> [Space]gc :<C-u>GitCommit<CR>
nnoremap <silent> [Space]gp q:Git push<Space>
nnoremap <silent> [Space]gt q:Git tag<Space>
"}}}


" if pathogen#is_disabled('molokai') == 0
"     echoerr "molokai enable"
" endif

""if filereadable(expand("~/.vimrc.bundles.local"))
""    source ~/.vimrc.bundles.local
""endif

set secure
