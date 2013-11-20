mydotvim
========

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
neocomplete.vim : autocompletion with fuzzy matching and faster than neocomplcache.vim.
unite.vim : creates new interface with your customization.
vimfiler.vim : better file manager with tree feature.
neosnippet.vim : snippet plugin with auto completion.
Pathogen: allows me to install plugins in a cleaner manner.
AutoComplPop: provides autocompletion.
Commentary: gives me painless commenting.
CtrlP: provides a uniform fuzzy matching interface for files, buffers, tags, quickfix entries, recent files, changes¡­
Snipmate: gives me lovely snippet-expansion.
Sparkup: allows me to generate large blocks of HTML with very simple CSS one-liners.
Surround: adds/changes/deletes pairs like ""''(){}[]<h1></h1>.
Syntastic: gives me syntax checking for many languages.
Tabular: allows me to align blocks of code.
grep.vim: grep buffers (should be part of core IMHO)
Align: align stuff, very powerful
vim-niceblock: better editing in visual mode
FuzzyFinder: I use it mostly for switching buffer, it can do a lot more
gundo.vim: undo history and more
tagbar: better than taglist
colorizer: colorize all text in the form #rrggbb or #rgb
smartusline: color statusbar according to mode (insert/normal/etc)
ultisnips.git: very powerful snippet manager
hybrid: good support for most langs, also don't find it distracting
vim-multiple-cursors: can come in really handy... some learning curve here
powerline: it's a purrty status line. actually find things like filetype, git branch and % useful, too.
YouCompleteMe: - awesome Johnny on the Spot autocompletion for everything... the best
easymotion: bit weird at first, but my flow has now gone to /[Class] || [Method] --> ,w --> char. Super fast. Hint: stare down where you want to go, then ,w
NerdCommenter: (un)coment easily
EasyTags: Tag search, better dan Ctags
supertab: for autocomplete
markdown: for markdown

