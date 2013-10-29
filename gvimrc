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
let colorscheme_list = ['solarized', 'calmar256-dark', 'badwolf', 'koehler', 'molokai',
            \ 'galaxy', 'gruvbox', 'desertink', 'ir_black', 'vividchalk',
            \ 'inkpot', 'skittles_berry', 'hybrid', 'zenburn', 'vombato', 'kolor']
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
        set guifont=Monospace\ 12
        set guifontwide=WenQuanYi\ Micro\ Hei\ Mono\ 10
    elseif has("gui_win32")     " Windows platform
        let font_name = ""
        if getfontname( "DejaVu_Sans_Mono" ) != ""
            set guifont=DejaVu_Sans_Mono:h11:cANSI
            let font_name = "DejaVu_Sans_Mono"
        elseif getfontname( "Source_Code_Pro" ) != ""
            set guifont=Source_Code_Pro:h12:cANSI
            let font_name = "Source_Code_Pro"
        elseif getfontname( "Bitstream_Vera_Sans_Mono" ) != ""
            set guifont=Bitstream_Vera_Sans_Mono:h10:cANSI
            let font_name = "Bitstream_Vera_Sans_Mono"
        elseif getfontname( "Consolas" ) != ""
            set guifont=Consolas:h11:cANSI " this is the default visual studio font
            let font_name = "Consolas"
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
set sidescrolloff=2

" autocmd
autocmd BufWritePost .vimrc source % source ~/.gvimrc
autocmd BufWritePost .gvimrc source %

"-----------------------------------------------------------
"gvim max size when open
"au GUIEnter * simalt ~x
"-----------------------------------------------------------

