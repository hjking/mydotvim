mydotvim
========

[![I Love Vim](https://img.shields.io/badge/I%20Love-Vim-red.svg)](http://vim.org)

## my dot vim folder

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


## Plugins I'm using

- AnsiEsc
- anzu: display matching pattern in command line
- bufferline: display buffer name in command line
- c: support for c/c++
- CamelCaseMotion
- Conque-Shell
- calendar.vim: nice calendar
- cscope_macros
- ctrlp

    provides a uniform fuzzy matching interface for files, buffers, tags, quickfix entries, recent files, changes

- delimitMate: auto insert brackets
- DrawIt
- easy-align
- easymotion
    bit weird at first, but my flow has now gone to /[Class] || [Method] --> ,w --> char. Super fast. Hint: stare down where you want to go, then ,w
- eunuch
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
- niceblock
    better editing in visual mode
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
- tlib_vim
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
- VisIncr
- yankring
- Statusline
    * airline
    * lightline: sometimes I'm using Vim 7.2, use this to subsitute airline
    * lightline-powerful: powerful setting for lightline
- ColorScheme
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

