if !has('gui_running')
      finish
endif

let g:gvimrc_loaded = 1

" Max width
" set columns=9999

" Color Setting
" colo adrian          "molokai fruity blackbeauty adaryn fnaqevan myColor_1
"set colorscheme randomly
set background=dark
let colorscheme_list = ['adam', 'adrian', 'asu1dark', 'af', 'solarized',
            \ 'billw', 'blacksea', 'blackbeauty', 'blugrine', 'brookstream',
            \ 'candy', 'calmar256-dark', 'candycode', 'colorer', 'badwolf',
            \ 'dante', 'fnaqevan', 'fruity', 'koehler', 'molokai', 'metacosm',
            \ 'tir_black', 'winter', 'desert256', 'bluechia', 'galaxy',
            \ 'desertink', 'diablo3', 'luinnar', 'putty', 'manxome','ir_black']
exec "colorscheme " . colorscheme_list[localtime()%len(colorscheme_list)]

" Display Settings
" {{{
set guioptions+=grTt
" don't use autoselect on OS X
if has('mac')
    set guioptions-=a
endif

" For CTRL-v to work autoselect must be off.
" On Unix we have two selections, autoselect can be used.
if !has('unix')
    set guioptions-=a
endif

" Font Setting
if has('mac')
    set guifont=Menlo\ Regular:h13
elseif has('unix')
    " set guifont=WenQuanYi\ Micro\ Hei\ Mono\ 10
    set guifont=Monospace\ 12
    set guifontwide=WenQuanYi\ Micro\ Hei\ Mono\ 10
else
    " Windows platform
    set guifont=DejaVu_Sans_Mono:h12:cANSI
    " set guifont=Raize:h12:b:cANSI
    set guifontwide=Courier_New:h12:cANSI
endif

" set guifont=GulimChe:h13:cANSI
" set guifont=MS_Gothic:h13:cANSI
" set guifont=monofur:h13:b:cANSI
" set guifont=Raize:h11:b:cANSI    " Raize:h12:b:cANSI
" set guifont=Bitstream_Vera_Sans_Mono:h11:cANSI
"   if MySys() == "mac"
"     set gfn=Menlo:h14
"     set shell=/bin/bash
"   elseif MySys() == "windows"
"     set gfn=Bitstream\ Vera\ Sans\ Mono:h10
"   elseif MySys() == "linux"
"     set gfn=Monospace\ 10
"     set shell=/bin/bash
"   endif
"

"-----------------------------------------------------------
" Tab Setting
"-----------------------------------------------------------
try
  set switchbuf=useopen
  set stal=1
catch
endtry


" Tab bar
hi TabLine guifg=LightGray guibg=#606060
hi TabLineSel gui=bold guifg=White guibg=#808080
hi TabLineFill gui=underline guifg=LightGray guibg=grey20 guibg=#505050

"-----------------------------------------------------------
""" Scroll Bar
"-----------------------------------------------------------
if has("gui_running")
    if has("gui_win32")     " Win
        set guioptions+=bh  " Horizontal scrolbar
    endif
endif
set scrolloff=3             " Keep 3 lines when cursor reach the top/bottom

" autocmd
autocmd BufWritePost .vimrc source % source ~/.gvimrc
autocmd BufWritePost .gvimrc source %

"-----------------------------------------------------------
"gvim max size when open
"au GUIEnter * simalt ~x
"-----------------------------------------------------------

